use crate::{SmtSolver, ast::BoolExpr, sat_solver::Lit};

pub struct Solver {
    smt: SmtSolver,
    heuristic: BranchingHeuristics,
}

impl Solver {
    pub fn new() -> Self {
        Self { smt: SmtSolver::new(), heuristic: BranchingHeuristics::new(0, 0.95, true) }
    }

    pub fn check_sat(&mut self) -> Option<bool> {
        let root_level = self.smt.user_scopes_len();
        loop {
            self.heuristic.sync_with_solver(self.smt.num_vars());
            if let Some((var, polarity)) = self.heuristic.pick_branching_literal(|var| self.smt.get_bool_val(&BoolExpr::Var(var)).is_none()) {
                if let Err((bt_level, lemma)) = self.smt.decide(Lit::new(var, polarity)) {
                    let bt_level = bt_level.max(root_level);
                    for lit in self.smt.get_trail_delta(self.smt.get_trail_len_at_level(bt_level)) {
                        self.heuristic.save_phase(lit.var(), lit.sign());
                        self.heuristic.insert_unassigned(lit.var());
                    }
                    self.smt.cancel_until(bt_level);

                    let mut learned_clause = Vec::with_capacity(lemma.len());
                    for lit in lemma {
                        learned_clause.push(if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(lit.var()))) } else { BoolExpr::Var(lit.var()) });
                        self.heuristic.bump_activity(lit.var());
                    }

                    self.heuristic.decay_activities();

                    if self.smt.assert(&BoolExpr::And(learned_clause)).is_err() {
                        return Some(false);
                    }
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
