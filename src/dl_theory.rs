use crate::{
    Lit,
    rational::{InfRational, Rational},
};
use std::{
    collections::VecDeque,
    fmt,
    ops::{Index, IndexMut},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DlVar(usize);

impl<T> Index<DlVar> for Vec<T> {
    type Output = T;
    fn index(&self, var: DlVar) -> &Self::Output {
        &self[var.0]
    }
}

impl<T> IndexMut<DlVar> for Vec<T> {
    fn index_mut(&mut self, var: DlVar) -> &mut Self::Output {
        &mut self[var.0]
    }
}

impl fmt::Display for DlVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "d{}", self.0)
    }
}

#[derive(Clone, Debug)]
struct DlEdge {
    to: DlVar,
    weight: InfRational,
    literal: Lit,
}

pub(super) struct DlTheory {
    graph: Vec<Vec<DlEdge>>,
    rev_graph: Vec<Vec<DlEdge>>,

    history: Vec<(DlVar, DlVar)>,
    trail_lim: Vec<usize>,

    distances: Vec<InfRational>,
    parents: Vec<Option<(DlVar, Lit)>>,

    work_queue: VecDeque<DlVar>,
    in_queue: Vec<bool>,

    spfa_dists: Vec<InfRational>,
}

impl DlTheory {
    pub(super) fn new() -> Self {
        Self {
            graph: Vec::new(),
            rev_graph: Vec::new(),
            history: Vec::new(),
            trail_lim: Vec::new(),
            distances: Vec::new(),
            parents: Vec::new(),
            work_queue: VecDeque::new(),
            in_queue: Vec::new(),
            spfa_dists: Vec::new(),
        }
    }

    pub(super) fn mk_var(&mut self) -> DlVar {
        let id = DlVar(self.graph.len());

        self.graph.push(Vec::new());
        self.rev_graph.push(Vec::new());

        self.distances.push(InfRational::from(0));

        self.parents.push(None);
        self.in_queue.push(false);

        self.spfa_dists.push(InfRational::from(0));

        id
    }

    pub(super) fn value(&self, var: DlVar) -> InfRational {
        self.distances[var].clone() - self.distances[0].clone()
    }

    #[allow(dead_code)]
    pub(super) fn lbs(&self) -> Vec<InfRational> {
        let dists_to_zero = self.exact_distances_from(DlVar(0), true);
        dists_to_zero.into_iter().map(|d| -d).collect()
    }

    pub(super) fn lb(&self, var: DlVar) -> InfRational {
        let dists = self.exact_distances_from(var, false);
        -dists[0].clone()
    }

    #[allow(dead_code)]
    pub(super) fn ubs(&self) -> Vec<InfRational> {
        self.exact_distances_from(DlVar(0), false)
    }

    pub(super) fn ub(&self, var: DlVar) -> InfRational {
        let dists = self.exact_distances_from(DlVar(0), false);
        dists[var].clone()
    }

    #[allow(dead_code)]
    pub(super) fn exact_distance(&self, from: DlVar, to: DlVar) -> InfRational {
        let dists = self.exact_distances_from(from, false);
        dists[to].clone()
    }

    fn exact_distances_from(&self, source: DlVar, use_rev_graph: bool) -> Vec<InfRational> {
        let n = self.graph.len();
        let mut dists = vec![InfRational::from(Rational::PositiveInf); n];
        let mut in_queue = vec![false; n];
        let mut queue = VecDeque::with_capacity(n);

        dists[source] = InfRational::from(0);
        queue.push_back(source);
        in_queue[source] = true;

        let active_graph = if use_rev_graph { &self.rev_graph } else { &self.graph };

        while let Some(u) = queue.pop_front() {
            in_queue[u] = false;

            for edge in &active_graph[u] {
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

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.history.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        if level < self.trail_lim.len() {
            let target_len = self.trail_lim[level];
            while self.history.len() > target_len {
                let (from, to) = self.history.pop().unwrap();
                self.graph[from].pop();
                self.rev_graph[to].pop();
            }
            self.trail_lim.truncate(level);
        }
    }

    pub(super) fn assert_edge(&mut self, from: DlVar, to: DlVar, weight: InfRational, literal: Lit) -> Result<bool, Vec<Lit>> {
        self.graph[from].push(DlEdge { to, weight: weight.clone(), literal });
        self.rev_graph[to].push(DlEdge { to: from, weight: weight.clone(), literal });

        self.history.push((from, to));

        self.check_negative_cycle(from, to, weight, literal)
    }

    fn check_negative_cycle(&mut self, source_u: DlVar, target_v: DlVar, weight: InfRational, literal: Lit) -> Result<bool, Vec<Lit>> {
        let new_dist = self.distances[source_u].clone() + weight;

        if new_dist >= self.distances[target_v] {
            return Ok(false);
        }

        self.spfa_dists.clone_from_slice(&self.distances);
        self.spfa_dists[target_v] = new_dist;
        self.parents[target_v] = Some((source_u, literal));

        self.work_queue.clear();
        self.in_queue.fill(false);

        self.work_queue.push_back(target_v);
        self.in_queue[target_v] = true;

        while let Some(curr) = self.work_queue.pop_front() {
            self.in_queue[curr] = false;

            if curr == source_u {
                return Err(self.extract_nogood(source_u));
            }

            for edge in &self.graph[curr] {
                let next = edge.to;
                let relaxed_dist = self.spfa_dists[curr].clone() + edge.weight.clone();

                if relaxed_dist < self.spfa_dists[next] {
                    self.spfa_dists[next] = relaxed_dist;
                    self.parents[next] = Some((curr, edge.literal));

                    if !self.in_queue[next] {
                        self.work_queue.push_back(next);
                        self.in_queue[next] = true;
                    }
                }
            }
        }

        std::mem::swap(&mut self.distances, &mut self.spfa_dists);
        Ok(true)
    }

    fn extract_nogood(&self, conflict_node: DlVar) -> Vec<Lit> {
        let mut nogood = Vec::new();
        let mut curr = conflict_node;

        loop {
            let (parent_node, literal) = self.parents[curr].unwrap();
            nogood.push(!literal);
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
    use crate::SatSolver;

    #[test]
    fn test_initialization_and_vars() {
        let mut dl = DlTheory::new();

        let zero = dl.mk_var();
        let x = dl.mk_var();

        assert_eq!(zero, DlVar(0), "First variable should have ID 0");
        assert_eq!(x, DlVar(1));
        assert_eq!(dl.graph.len(), 2);
        assert_eq!(dl.distances.len(), 2);
    }

    #[test]
    fn test_simple_bounds_extraction() {
        let mut dl = DlTheory::new();
        let zero = dl.mk_var();
        let x = dl.mk_var();
        let y = dl.mk_var();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();
        let b3 = sat.mk_var();

        assert!(dl.assert_edge(zero, x, InfRational::from(10), Lit::new(b1, false)).is_ok());

        assert!(dl.assert_edge(x, y, InfRational::from(5), Lit::new(b2, false)).is_ok());

        assert_eq!(dl.ub(x), InfRational::from(10));
        assert_eq!(dl.ub(y), InfRational::from(15));

        assert!(dl.assert_edge(x, zero, InfRational::from(-3), Lit::new(b3, false)).is_ok());

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
        let zero = dl.mk_var();
        let x = dl.mk_var();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();

        assert!(dl.assert_edge(zero, x, InfRational::from(5), Lit::new(b1, false)).is_ok());

        let res = dl.assert_edge(x, zero, InfRational::from(-10), Lit::new(b2, false));

        assert!(res.is_err(), "Should detect a negative cycle");

        let nogood = res.unwrap_err();
        assert_eq!(nogood.len(), 2);
        assert!(nogood.contains(&Lit::new(b1, true)));
        assert!(nogood.contains(&Lit::new(b2, true)));
    }

    #[test]
    fn test_strict_inequality_infinitesimal_cycle() {
        let mut dl = DlTheory::new();
        let zero = dl.mk_var();
        let x = dl.mk_var();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();

        assert!(dl.assert_edge(zero, x, InfRational::from(5), Lit::new(b1, false)).is_ok());

        let res = dl.assert_edge(x, zero, InfRational::from((Rational::from(-5), -1)), Lit::new(b2, false));

        assert!(res.is_err(), "Should detect a negative cycle with infinitesimal weight");
    }

    #[test]
    fn test_backtracking_cancel_until() {
        let mut dl = DlTheory::new();
        let zero = dl.mk_var();
        let x = dl.mk_var();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();

        assert!(dl.assert_edge(zero, x, InfRational::from(10), Lit::new(b1, false)).is_ok());

        dl.push();

        assert!(dl.assert_edge(zero, x, InfRational::from(2), Lit::new(b2, false)).is_ok());
        assert_eq!(dl.ub(x), InfRational::from(2), "UB should be updated to 2 after the second edge is added");

        dl.cancel_until(0);

        assert_eq!(dl.graph[zero].len(), 1);
        assert_eq!(dl.ub(x), InfRational::from(10), "UB should revert to 10 after backtracking");
    }

    #[test]
    fn test_current_value_model() {
        let mut dl = DlTheory::new();
        let zero = dl.mk_var();
        let x = dl.mk_var();
        let y = dl.mk_var();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();
        let b3 = sat.mk_var();
        let b4 = sat.mk_var();
        let b5 = sat.mk_var();
        let b6 = sat.mk_var();

        // 1. Constraints on X: 5 <= X <= 10
        // X - zero <= 10
        assert!(dl.assert_edge(zero, x, InfRational::from(10), Lit::new(b1, false)).is_ok());
        // zero - X <= -5  (that is, X >= 5)
        assert!(dl.assert_edge(x, zero, InfRational::from(-5), Lit::new(b2, false)).is_ok());

        let val_x = dl.value(x);
        assert!(val_x >= InfRational::from(5), "The current value of X must satisfy the lower bound");
        assert!(val_x <= InfRational::from(10), "The current value of X must satisfy the upper bound");

        // 2. Relative constraint on Y: Y - X <= 7
        assert!(dl.assert_edge(x, y, InfRational::from(7), Lit::new(b3, false)).is_ok());

        // 3. Absolute constraint on Y: Y >= 15
        // zero - Y <= -15
        assert!(dl.assert_edge(y, zero, InfRational::from(-15), Lit::new(b4, false)).is_ok());

        // Extract the new values (the distances were relaxed due to the cycles)
        let val_x2 = dl.value(x);
        let val_y = dl.value(y);

        // Verify that ALL active constraints are simultaneously satisfied by the model
        assert!(val_y.clone() - val_x2.clone() <= InfRational::from(7), "The relative constraint Y - X <= 7 is not satisfied");
        assert!(val_y >= InfRational::from(15), "The lower bound of Y is not satisfied");
        assert!(val_x2 >= InfRational::from(5), "The lower bound of X is not satisfied after updating Y");
        assert!(val_x2 <= InfRational::from(10), "The upper bound of X is not satisfied after updating Y");

        // 4. Exact equality test: force X = 8
        assert!(dl.assert_edge(zero, x, InfRational::from(8), Lit::new(b5, false)).is_ok());
        assert!(dl.assert_edge(x, zero, InfRational::from(-8), Lit::new(b6, false)).is_ok());

        assert_eq!(dl.value(x), InfRational::from(8), "The value of X must be exactly 8");
    }

    #[test]
    fn test_failed_cycle_does_not_corrupt_distances() {
        let mut dl = DlTheory::new();
        let zero = dl.mk_var();
        let x = dl.mk_var();
        let y = dl.mk_var();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();
        let b3 = sat.mk_var();

        // Level 0:
        // 1) x - zero <= -2  (x <= -2)
        assert!(dl.assert_edge(zero, x, InfRational::from(-2), Lit::new(b1, false)).is_ok());
        // 2) y - x <= 0      (y <= x)
        assert!(dl.assert_edge(x, y, InfRational::from(0), Lit::new(b2, false)).is_ok());

        assert!(dl.value(x) <= InfRational::from(-2));
        assert!(dl.value(y) <= dl.value(x), "At level 0, y <= x must hold");

        // Level 1: add zero - x <= -5 (x >= 5), which creates a negative cycle with x <= -2
        dl.push();
        let conflict = dl.assert_edge(x, zero, InfRational::from(-5), Lit::new(b3, false));
        assert!(conflict.is_err(), "Should detect the negative cycle between zero and x");

        // Backtrack to level 0
        dl.cancel_until(0);

        // The potential model (distances) at level 0 must not have been corrupted by the failed cycle
        let val_x = dl.value(x);
        let val_y = dl.value(y);
        assert!(val_x <= InfRational::from(-2), "After cancel_until(0), x <= -2 must be preserved (found x = {})", val_x);
        assert!(val_y <= val_x, "After cancel_until(0), the potential must not be corrupted: y <= x violated (y = {}, x = {})", val_y, val_x);
    }
}
