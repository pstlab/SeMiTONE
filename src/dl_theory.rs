use crate::{
    Lit,
    rational::{InfRational, Rational},
};

#[derive(Clone, Debug)]
struct DlEdge {
    to: usize,
    weight: InfRational,
    literal: Lit,
}

pub(super) struct DlTheory {
    graph: Vec<Vec<DlEdge>>,

    history: Vec<usize>,

    distances: Vec<InfRational>,
    parents: Vec<Option<(usize, Lit)>>,

    work_queue: std::collections::VecDeque<usize>,
    in_queue: Vec<bool>,
    trail_lim: Vec<usize>,
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
            trail_lim: Vec::new(),
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

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.history.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        if level < self.trail_lim.len() {
            let target_len = self.trail_lim[level];
            while self.history.len() > target_len {
                let from = self.history.pop().unwrap();
                self.graph[from].pop();
            }
            self.trail_lim.truncate(level);
        }
    }

    pub(super) fn assert_edge(&mut self, from: usize, to: usize, weight: InfRational, literal: Lit) -> Result<bool, Vec<Lit>> {
        self.graph[from].push(DlEdge { to, weight: weight.clone(), literal });
        self.history.push(from);

        self.check_negative_cycle(from, to, weight, literal)
    }

    fn check_negative_cycle(&mut self, source_u: usize, target_v: usize, weight: InfRational, literal: Lit) -> Result<bool, Vec<Lit>> {
        let new_dist = self.distances[source_u].clone() + weight;

        if new_dist >= self.distances[target_v] {
            return Ok(false);
        }

        self.distances[target_v] = new_dist;
        self.parents[target_v] = Some((source_u, literal));

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

        Ok(true)
    }

    fn extract_nogood(&self, conflict_node: usize) -> Vec<Lit> {
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

        assert!(dl.assert_edge(zero, x, InfRational::from(10), Lit::new(100, false)).is_ok());

        assert!(dl.assert_edge(x, y, InfRational::from(5), Lit::new(101, false)).is_ok());

        assert_eq!(dl.ub(x), InfRational::from(10));
        assert_eq!(dl.ub(y), InfRational::from(15));

        assert!(dl.assert_edge(x, zero, InfRational::from(-3), Lit::new(102, false)).is_ok());

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

        assert!(dl.assert_edge(zero, x, InfRational::from(5), Lit::new(1, false)).is_ok());

        let res = dl.assert_edge(x, zero, InfRational::from(-10), Lit::new(2, false));

        assert!(res.is_err(), "Should detect a negative cycle");

        let nogood = res.unwrap_err();
        assert_eq!(nogood.len(), 2);
        assert!(nogood.contains(&Lit::new(1, false)));
        assert!(nogood.contains(&Lit::new(2, false)));
    }

    #[test]
    fn test_strict_inequality_infinitesimal_cycle() {
        let mut dl = DlTheory::new();
        let zero = dl.new_var();
        let x = dl.new_var();

        assert!(dl.assert_edge(zero, x, InfRational::from(5), Lit::new(1, false)).is_ok());

        let res = dl.assert_edge(x, zero, InfRational::from((Rational::from(-5), -1)), Lit::new(2, false));

        assert!(res.is_err(), "Should detect a negative cycle with infinitesimal weight");
    }

    #[test]
    fn test_backtracking_cancel_until() {
        let mut dl = DlTheory::new();
        let zero = dl.new_var();
        let x = dl.new_var();

        assert!(dl.assert_edge(zero, x, InfRational::from(10), Lit::new(1, false)).is_ok());

        dl.push();

        assert!(dl.assert_edge(zero, x, InfRational::from(2), Lit::new(2, false)).is_ok());
        assert_eq!(dl.ub(x), InfRational::from(2), "UB should be updated to 2 after the second edge is added");

        dl.cancel_until(0);

        assert_eq!(dl.graph[zero].len(), 1);
        assert_eq!(dl.ub(x), InfRational::from(10), "UB should revert to 10 after backtracking");
    }
}
