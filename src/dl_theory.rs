use crate::rational::{InfRational, Rational};

#[derive(Clone, Debug)]
pub struct DlEdge {
    to: usize,
    weight: InfRational,
    literal: usize,
}

pub struct DlTheory {
    graph: Vec<Vec<DlEdge>>,

    history: Vec<usize>,

    distances: Vec<InfRational>,
    parents: Vec<Option<(usize, usize)>>,

    work_queue: std::collections::VecDeque<usize>,
    in_queue: Vec<bool>,
}

impl DlTheory {
    pub(super) fn new() -> Self {
        Self {
            graph: Vec::new(),
            history: Vec::new(),
            distances: Vec::new(),
            parents: Vec::new(),
            work_queue: std::collections::VecDeque::new(),
            in_queue: Vec::new(),
        }
    }

    pub(super) fn new_var(&mut self) -> usize {
        let id = self.graph.len();

        self.graph.push(Vec::new());

        self.distances.push(InfRational::from(0));

        self.parents.push(None);
        self.in_queue.push(false);

        id
    }

    pub(super) fn lbs(&self) -> Vec<InfRational> {
        let dists_to_zero = self.exact_distances_from_reversed(0);
        dists_to_zero.into_iter().map(|d| -d).collect()
    }

    pub(super) fn lb(&self, var: usize) -> InfRational {
        let dists = self.exact_distances_from(var);
        -dists[0].clone()
    }

    pub(super) fn ubs(&self) -> Vec<InfRational> {
        self.exact_distances_from(0)
    }

    pub(super) fn ub(&self, var: usize) -> InfRational {
        let dists = self.exact_distances_from(0);
        dists[var].clone()
    }

    pub(super) fn exact_distance(&self, from: usize, to: usize) -> InfRational {
        let dists = self.exact_distances_from(from);
        dists[to].clone()
    }

    fn exact_distances_from(&self, source: usize) -> Vec<InfRational> {
        let n = self.graph.len();

        let mut dists = vec![InfRational::from(Rational::PositiveInf); n];
        let mut in_queue = vec![false; n];
        let mut queue = std::collections::VecDeque::with_capacity(n);

        dists[source] = InfRational::from(0);
        queue.push_back(source);
        in_queue[source] = true;

        while let Some(u) = queue.pop_front() {
            in_queue[u] = false;

            for edge in &self.graph[u] {
                let v = edge.to;
                let relaxed = dists[u].clone() + edge.weight.clone();

                if relaxed < dists[v] {
                    dists[v] = relaxed;
                    if !in_queue[v] {
                        queue.push_back(v);
                        in_queue[v] = true;
                    }
                }
            }
        }

        dists
    }

    fn exact_distances_from_reversed(&self, source: usize) -> Vec<InfRational> {
        let n = self.graph.len();

        let mut rev_graph: Vec<Vec<(usize, InfRational)>> = vec![Vec::new(); n];
        for u in 0..n {
            for edge in &self.graph[u] {
                rev_graph[edge.to].push((u, edge.weight.clone()));
            }
        }

        let mut dists = vec![InfRational::from(Rational::PositiveInf); n];
        let mut in_queue = vec![false; n];
        let mut queue = std::collections::VecDeque::with_capacity(n);

        dists[source] = InfRational::from(0);
        queue.push_back(source);
        in_queue[source] = true;

        while let Some(u) = queue.pop_front() {
            in_queue[u] = false;

            for (v_node, weight) in &rev_graph[u] {
                let v = *v_node;
                let relaxed = dists[u].clone() + weight.clone();

                if relaxed < dists[v] {
                    dists[v] = relaxed;
                    if !in_queue[v] {
                        queue.push_back(v);
                        in_queue[v] = true;
                    }
                }
            }
        }

        dists
    }

    pub(super) fn cancel_until(&mut self, target_len: usize) {
        while self.history.len() > target_len {
            let from = self.history.pop().unwrap();
            self.graph[from].pop();
        }
    }

    pub(super) fn assert_edge(&mut self, from: usize, edge: DlEdge) -> Result<(), Vec<usize>> {
        self.graph[from].push(edge.clone());
        self.history.push(from);

        self.check_negative_cycle(from, edge)
    }

    fn check_negative_cycle(&mut self, source_u: usize, new_edge: DlEdge) -> Result<(), Vec<usize>> {
        let target_v = new_edge.to;

        let new_dist = self.distances[source_u].clone() + new_edge.weight.clone();

        if new_dist >= self.distances[target_v] {
            return Ok(());
        }

        self.distances[target_v] = new_dist;
        self.parents[target_v] = Some((source_u, new_edge.literal));

        for node in self.work_queue.drain(..) {
            self.in_queue[node] = false;
        }
        self.work_queue.push_back(target_v);
        self.in_queue[target_v] = true;

        while let Some(curr) = self.work_queue.pop_front() {
            self.in_queue[curr] = false;

            if curr == source_u {
                return Err(self.extract_nogood(source_u));
            }

            for edge in &self.graph[curr] {
                let next = edge.to;
                let relaxed_dist = self.distances[curr].clone() + edge.weight.clone();

                if relaxed_dist < self.distances[next] {
                    self.distances[next] = relaxed_dist;
                    self.parents[next] = Some((curr, edge.literal));

                    if !self.in_queue[next] {
                        self.work_queue.push_back(next);
                        self.in_queue[next] = true;
                    }
                }
            }
        }

        Ok(())
    }

    fn extract_nogood(&self, conflict_node: usize) -> Vec<usize> {
        let mut nogood = Vec::new();
        let mut curr = conflict_node;

        loop {
            let (parent_node, literal) = self.parents[curr].unwrap();

            nogood.push(literal);

            curr = parent_node;

            if curr == conflict_node {
                break;
            }
        }

        nogood
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initialization_and_vars() {
        let mut dl = DlTheory::new();

        let zero = dl.new_var();
        let x = dl.new_var();

        assert_eq!(zero, 0, "First variable should have ID 0");
        assert_eq!(x, 1);
        assert_eq!(dl.graph.len(), 2);
        assert_eq!(dl.distances.len(), 2);
    }

    #[test]
    fn test_simple_bounds_extraction() {
        let mut dl = DlTheory::new();
        let zero = dl.new_var();
        let x = dl.new_var();
        let y = dl.new_var();

        assert!(dl.assert_edge(zero, DlEdge { to: x, weight: InfRational::from(10), literal: 100 }).is_ok());

        assert!(dl.assert_edge(x, DlEdge { to: y, weight: InfRational::from(5), literal: 101 }).is_ok());

        assert_eq!(dl.ub(x), InfRational::from(10));
        assert_eq!(dl.ub(y), InfRational::from(15));

        assert!(dl.assert_edge(x, DlEdge { to: zero, weight: InfRational::from(-3), literal: 102 }).is_ok());

        assert_eq!(dl.lb(x), InfRational::from(3));

        let ubs = dl.ubs();
        let lbs = dl.lbs();
        assert_eq!(ubs[x], InfRational::from(10));
        assert_eq!(ubs[y], InfRational::from(15));
        assert_eq!(lbs[x], InfRational::from(3));
    }

    #[test]
    fn test_negative_cycle_detection() {
        let mut dl = DlTheory::new();
        let zero = dl.new_var();
        let x = dl.new_var();

        assert!(dl.assert_edge(zero, DlEdge { to: x, weight: InfRational::from(5), literal: 1 }).is_ok());

        let res = dl.assert_edge(x, DlEdge { to: zero, weight: InfRational::from(-10), literal: 2 });

        assert!(res.is_err(), "Should detect a negative cycle");

        let nogood = res.unwrap_err();
        assert_eq!(nogood.len(), 2);
        assert!(nogood.contains(&1));
        assert!(nogood.contains(&2));
    }

    #[test]
    fn test_strict_inequality_infinitesimal_cycle() {
        let mut dl = DlTheory::new();
        let zero = dl.new_var();
        let x = dl.new_var();

        assert!(dl.assert_edge(zero, DlEdge { to: x, weight: InfRational::from(5), literal: 1 }).is_ok());

        let res = dl.assert_edge(x, DlEdge { to: zero, weight: InfRational::from((Rational::from(-5), -1)), literal: 2 });

        assert!(res.is_err(), "Should detect a negative cycle with infinitesimal weight");
    }

    #[test]
    fn test_backtracking_cancel_until() {
        let mut dl = DlTheory::new();
        let zero = dl.new_var();
        let x = dl.new_var();

        assert!(dl.assert_edge(zero, DlEdge { to: x, weight: InfRational::from(10), literal: 1 }).is_ok());
        let target_len = dl.history.len();

        assert!(dl.assert_edge(zero, DlEdge { to: x, weight: InfRational::from(2), literal: 2 }).is_ok());
        assert_eq!(dl.ub(x), InfRational::from(2), "UB should be updated to 2 after the second edge is added");

        dl.cancel_until(target_len);

        assert_eq!(dl.graph[zero].len(), 1);
        assert_eq!(dl.ub(x), InfRational::from(10), "UB should revert to 10 after backtracking");
    }
}
