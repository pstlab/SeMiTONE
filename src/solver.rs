use crate::{SeMiTONE, ast::BoolExpr, sat_solver::Lit};

pub struct Solver {
    pub smt: SeMiTONE,
    heuristic: BranchingHeuristics,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        Self { smt: SeMiTONE::new(), heuristic: BranchingHeuristics::new(0, 0.95, true) }
    }

    pub fn check_sat(&mut self) -> Option<bool> {
        self.heuristic.sync_with_solver(self.smt.num_vars());
        loop {
            if let Err((bt_level, lemma)) = self.smt.propagate() {
                for lit in self.smt.get_trail_delta(self.smt.get_trail_len_at_level(bt_level)) {
                    self.heuristic.save_phase(lit.var(), lit.sign());
                    self.heuristic.insert_unassigned(lit.var());
                }
                self.smt.cancel_until(bt_level);

                for lit in &lemma {
                    self.heuristic.bump_activity(lit.var());
                }

                self.heuristic.decay_activities();

                if self.smt.add_clause(lemma).is_err() {
                    return Some(false);
                }
                continue;
            }

            if let Some((var, polarity)) = self.heuristic.pick_branching_literal(|var| self.smt.get_bool_val(&BoolExpr::Var(var)).is_none()) {
                self.smt.decide(Lit::new(var, polarity));
            } else if let Err((bt_level, lemma)) = self.smt.check_ints() {
                self.heuristic.sync_with_solver(self.smt.num_vars());
                for lit in self.smt.get_trail_delta(self.smt.get_trail_len_at_level(bt_level)) {
                    self.heuristic.save_phase(lit.var(), lit.sign());
                    self.heuristic.insert_unassigned(lit.var());
                }
                self.smt.cancel_until(bt_level);

                for lit in &lemma {
                    self.heuristic.bump_activity(lit.var());
                }

                self.heuristic.decay_activities();

                if self.smt.add_clause(lemma).is_err() {
                    return Some(false);
                }
            } else {
                return Some(true);
            }
        }
    }
}

struct BranchingHeuristics {
    activities: Vec<f64>,
    inc: f64,
    decay_factor: f64,

    heap: Vec<usize>,
    indices: Vec<usize>,

    phases: Vec<bool>,
    default_phase: bool,
}

impl BranchingHeuristics {
    fn new(num_vars: usize, decay_factor: f64, default_phase: bool) -> Self {
        let mut slf = Self {
            activities: vec![0.0; num_vars],
            inc: 1.0,
            decay_factor,
            heap: Vec::with_capacity(num_vars),
            indices: vec![usize::MAX; num_vars],
            phases: vec![default_phase; num_vars],
            default_phase,
        };

        for i in 0..num_vars {
            slf.heap.push(i);
            slf.indices[i] = i;
        }

        slf
    }

    fn sync_with_solver(&mut self, current_num_vars: usize) {
        let known_vars = self.activities.len();
        for var in known_vars..current_num_vars {
            self.ensure_capacity(var);
            self.insert_unassigned(var);
        }
    }

    fn bump_activity(&mut self, var: usize) {
        self.ensure_capacity(var);

        self.activities[var] += self.inc;

        if self.indices[var] != usize::MAX {
            self.percolate_up(self.indices[var]);
        }

        if self.activities[var] > 1e100 {
            self.rescale_activities();
        }
    }

    fn decay_activities(&mut self) {
        self.inc /= self.decay_factor;
    }

    fn save_phase(&mut self, var: usize, polarity: bool) {
        self.ensure_capacity(var);
        self.phases[var] = polarity;
    }

    fn insert_unassigned(&mut self, var: usize) {
        if self.indices[var] == usize::MAX {
            let idx = self.heap.len();
            self.indices[var] = idx;
            self.heap.push(var);
            self.percolate_up(idx);
        }
    }

    fn pick_branching_literal<F>(&mut self, is_unassigned: F) -> Option<(usize, bool)>
    where
        F: Fn(usize) -> bool,
    {
        while !self.heap.is_empty() {
            let max_var = self.heap[0];
            self.indices[max_var] = usize::MAX;

            let last_var = self.heap.pop().unwrap();
            if !self.heap.is_empty() {
                self.heap[0] = last_var;
                self.indices[last_var] = 0;
                self.percolate_down(0);
            }

            if is_unassigned(max_var) {
                let polarity = self.phases[max_var];
                return Some((max_var, polarity));
            }
        }
        None
    }

    fn ensure_capacity(&mut self, var: usize) {
        if var >= self.activities.len() {
            let new_len = var + 1;
            self.activities.resize(new_len, 0.0);
            self.indices.resize(new_len, usize::MAX);
            self.phases.resize(new_len, self.default_phase);
        }
    }

    fn rescale_activities(&mut self) {
        for act in &mut self.activities {
            *act *= 1e-100;
        }
        self.inc *= 1e-100;
    }

    fn percolate_up(&mut self, mut i: usize) {
        let var = self.heap[i];
        let act = self.activities[var];

        while i > 0 {
            let parent_i = (i - 1) >> 1;
            let parent_var = self.heap[parent_i];

            if self.activities[parent_var] >= act {
                break;
            }

            self.heap[i] = parent_var;
            self.indices[parent_var] = i;
            i = parent_i;
        }

        self.heap[i] = var;
        self.indices[var] = i;
    }

    fn percolate_down(&mut self, mut i: usize) {
        let var = self.heap[i];
        let act = self.activities[var];
        let len = self.heap.len();

        loop {
            let left_i = (i << 1) + 1;
            if left_i >= len {
                break;
            }

            let right_i = left_i + 1;
            let mut child_i = left_i;

            if right_i < len && self.activities[self.heap[right_i]] > self.activities[self.heap[left_i]] {
                child_i = right_i;
            }

            let child_var = self.heap[child_i];
            if act >= self.activities[child_var] {
                break;
            }

            self.heap[i] = child_var;
            self.indices[child_var] = i;
            i = child_i;
        }

        self.heap[i] = var;
        self.indices[var] = i;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{ArithExpr, min},
        rational::{InfRational, Rational},
    };

    #[test]
    fn test_simplex_system_sat() {
        let mut solver = Solver::new();
        let x = solver.smt.new_real();
        let y = solver.smt.new_real();
        let z = solver.smt.new_real();

        // 2x - y + z == 10
        let exp1 = ((ArithExpr::from(2) * x.clone()) - y.clone() + z.clone()).eq(ArithExpr::from(10));

        // x > 0, y > 0, z > 0
        let bnd = x.gt(0) & y.gt(0) & z.gt(0);

        let result = solver.smt.assert(exp1 & bnd);
        assert!(result, "The system should be asserted successfully, as it has valid real solutions.");

        // Triggers the search loop to assign values to the slack variables
        assert_eq!(solver.check_sat(), Some(true), "The system has valid real solutions and should be SAT");
    }

    #[test]
    fn test_tseitin_nested_boolean_logic() {
        let mut solver = Solver::new();
        let a = solver.smt.new_bool();
        let b = solver.smt.new_bool();

        let nested_and = &a & &b;
        let nested_or = !&a | BoolExpr::False;

        let root_or = nested_and | nested_or | BoolExpr::True;

        assert!(solver.smt.assert(root_or), "The system should be asserted successfully, as it has valid boolean solutions.");
        assert_eq!(solver.check_sat(), Some(true), "The system has valid boolean solutions and should be SAT");
    }

    #[test]
    fn test_tseitin_nested_theory_atoms() {
        let mut solver = Solver::new();
        let x = solver.smt.new_real();

        let atom_lt = x.lt(5);
        let atom_ge = x.ge(10);
        let atom_le = x.le(0);
        let atom_gt = x.gt(20);

        let disjunction1 = atom_lt | atom_ge;
        let disjunction2 = atom_le | atom_gt;

        assert!(solver.smt.assert(disjunction1), "The system should be asserted successfully, as it has valid real solutions.");
        assert!(solver.smt.assert(disjunction2), "The system should be asserted successfully, as it has valid real solutions.");
        assert_eq!(solver.check_sat(), Some(true), "The system has valid real solutions and should be SAT");
    }

    #[test]
    fn test_encode_eq_booleans() {
        let mut solver = Solver::new();
        let a = solver.smt.new_bool();
        let b = solver.smt.new_bool();

        let eq_expr = a.eq(&b);

        assert!(solver.smt.assert(eq_expr & a), "The system should be asserted successfully, as it has valid boolean solutions.");
        assert_eq!(solver.check_sat(), Some(true), "The system has valid boolean solutions and should be SAT");

        assert_eq!(solver.smt.get_bool_val(&b), Some(true));
    }

    #[test]
    fn test_dpllt_backtracking_over_theory() {
        let mut solver = Solver::new();
        let x = solver.smt.new_real();

        // (x < 0 ∨ x > 10) ∧ (x > 5) ∧ (x < 15)
        let expr = (x.lt(0) | x.gt(10)) & x.gt(5) & x.lt(15);

        let result = solver.smt.assert(expr);
        assert!(result, "The system should be asserted successfully, as it has valid real solutions.");

        solver.smt.propagate().expect("Initial propagation should succeed");

        // check_sat will guess (x < 0), the theory will reject it against (x > 5),
        // the solver will learn the lemma, backtrack, and pick (x > 10) instead.
        assert_eq!(solver.check_sat(), Some(true), "Solver must backtrack from the x < 0 branch and find the SAT path");
    }

    #[test]
    fn test_dpllt_negated_equality_branching() {
        let mut solver = Solver::new();
        let x = solver.smt.new_real();
        let y = solver.smt.new_real();

        let not_eq = !x.eq(&y);

        let force_lt = x.lt(10) & y.gt(20);

        let expr = not_eq & force_lt;

        let result = solver.smt.assert(expr);
        assert!(result, "The system should be asserted successfully, as it has valid real solutions.");

        // The solver will branch on the disjunction, fail one path due to LRA bounds,
        // and backtrack to validate the other.
        assert_eq!(solver.check_sat(), Some(true), "Solver must resolve negated equality branching correctly");
    }

    #[test]
    fn test_enum_basic_sat() {
        let mut solver = Solver::new();
        let e = solver.smt.new_enum(vec![1, 2, 3]);

        let expr = e.eq(2);

        assert!(solver.smt.assert(expr), "The system should be asserted successfully, as it has valid enum solutions.");
        assert_eq!(solver.check_sat(), Some(true), "The solver should find a valid assignment for the enum variable");
    }

    #[test]
    fn test_enum_var_to_var_equality() {
        let mut solver = Solver::new();
        let e1 = solver.smt.new_enum(vec![1, 2, 3]);
        let e2 = solver.smt.new_enum(vec![3, 4, 5]);

        let eq_expr = e1.eq(&e2);

        assert!(solver.smt.assert(eq_expr), "The system should be asserted successfully, as it has valid enum solutions.");
        assert_eq!(solver.check_sat(), Some(true), "Solver should find a valid assignment for e1 and e2 where they are equal (SAT)");

        let not_3 = !e1.eq(3);
        assert!(!solver.smt.assert(not_3), "The system should not be asserted successfully, as it has no valid enum solutions.");
    }

    #[test]
    fn test_enum_dpllt_branching() {
        let mut solver = Solver::new();
        let e = solver.smt.new_enum(vec![1, 2, 3]);

        let expr = (e.eq(1) | e.eq(2)) & !e.eq(1);

        assert!(solver.smt.assert(expr), "The system should be asserted successfully, as it has valid enum solutions.");

        assert_eq!(solver.check_sat(), Some(true), "Solver should backtrack and explore e == 2 (SAT)");
    }

    #[test]
    fn test_integer_branch_and_bound_unsat() {
        let mut solver = Solver::new();
        let x = solver.smt.new_int();

        let eq_expr = (ArithExpr::from(2) * x.clone()).eq(ArithExpr::from(3));

        assert!(solver.smt.assert(eq_expr), "The system should be asserted successfully, as it has valid integer solutions.");

        assert_eq!(solver.check_sat(), Some(false), "There is no integer solution to 2x = 3, should be UNSAT");
    }

    #[test]
    fn test_integer_branch_and_bound_sat() {
        let mut solver = Solver::new();
        let x = solver.smt.new_int();

        let expr = x.gt((12, 10)) & x.lt((28, 10));

        assert!(solver.smt.assert(expr), "The system should be asserted successfully, as it has valid integer solutions.");

        assert_eq!(solver.check_sat(), Some(true), "There is an integer solution to the constraints, should be SAT");
    }

    #[test]
    fn test_min_constraint_sat_and_model_extraction() {
        let mut solver = Solver::new();
        let x = solver.smt.new_real();
        let y = solver.smt.new_real();
        let z = solver.smt.new_real();

        // x = 15, y = 10
        let eq_x = x.eq(15);
        let eq_y = y.eq(10);

        // z = min(x, y)
        let min_expr = min(z.clone(), [x.clone(), y.clone()]);

        let expr = eq_x & eq_y & min_expr;
        assert!(solver.smt.assert(expr), "The system should be asserted successfully, as it has valid real solutions.");

        // DPLL(T) should resolve this and guess z = 10
        assert_eq!(solver.check_sat(), Some(true), "The min constraint must be SAT");

        // Verify the extracted model
        assert_eq!(solver.smt.get_arith_val(&z), Some(InfRational::new(Rational::Finite(rug::Rational::from(10)), rug::Rational::from(0))), "The min constraint should resolve to z = 10");
    }

    #[test]
    fn test_push_pop_incremental_scopes() {
        let mut solver = Solver::new();
        let x = solver.smt.new_real();

        // x >= 10
        assert!(solver.smt.assert(x.ge(10)), "The system should be asserted successfully, as it has valid real solutions.");
        assert_eq!(solver.check_sat(), Some(true), "x >= 10 is SAT");

        solver.smt.push();
        // x <= 20
        assert!(solver.smt.assert(x.le(20)), "The system should be asserted successfully, as it has valid real solutions.");
        assert_eq!(solver.check_sat(), Some(true), "x >= 10 and x <= 20 is SAT");

        solver.smt.push();
        // x <= 5
        assert!(!solver.smt.assert(x.le(5)), "x >= 10 and x <= 5 is UNSAT");

        solver.smt.pop();
        assert_eq!(solver.check_sat(), Some(true), "x >= 10 and x <= 20 is SAT after popping the last scope");

        let val = solver.smt.get_arith_val(&x).unwrap();
        assert!(val >= InfRational::new(Rational::Finite(rug::Rational::from(10)), rug::Rational::from(0)));
        assert!(val <= InfRational::new(Rational::Finite(rug::Rational::from(20)), rug::Rational::from(0)));

        solver.smt.pop();
        assert!(solver.smt.assert(x.ge(50)), "The system should be asserted successfully, as it has valid real solutions.");
        assert_eq!(solver.check_sat(), Some(true), "x >= 50 is SAT after popping all scopes");
    }

    #[test]
    fn test_gomory_cut_generation_unsat() {
        let mut solver = Solver::new();
        let x = solver.smt.new_int();
        let y = solver.smt.new_int();

        let eq_expr = (&ArithExpr::from(3) * &x + &ArithExpr::from(3) * &y).eq(10);

        // Gomory cuts require variables to be bounded to effectively prune.
        // Without bounds, the cut becomes a tautology, leading to stagnation.
        let bounds = (x.clone().ge(0)) & (y.clone().ge(0));

        assert!(solver.smt.assert(eq_expr & bounds), "The system should be asserted successfully, as it has valid integer solutions.");

        assert_eq!(solver.check_sat(), Some(false), "3x + 3y = 10 has no integer solutions, must be UNSAT");
    }

    #[test]
    fn test_gomory_cut_generation_sat() {
        let mut solver = Solver::new();
        let x = solver.smt.new_int();
        let y = solver.smt.new_int();

        // 3x + 4y = 10, with x >= 0 and y >= 0
        let eq_expr = (ArithExpr::from(3) * x.clone() + ArithExpr::from(4) * y.clone()).eq(ArithExpr::from(10));

        let bounds = (x.clone().ge(0)) & (y.clone().ge(0));

        assert!(solver.smt.assert(eq_expr & bounds), "The system should be asserted successfully, as it has valid integer solutions.");

        assert_eq!(solver.check_sat(), Some(true), "Il sistema ha una soluzione intera e deve essere SAT");

        let val_x = solver.smt.get_arith_val(&x).expect("x deve avere un valore");
        let val_y = solver.smt.get_arith_val(&y).expect("y deve avere un valore");

        assert_eq!(val_x.rational_part().clone(), Rational::Finite(rug::Rational::from(2)));
        assert_eq!(val_y.rational_part().clone(), Rational::Finite(rug::Rational::from(1)));
    }
}
