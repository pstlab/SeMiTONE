use std::{collections::VecDeque, fmt, mem, ops};
use tracing::trace;

pub(super) struct SatSolver {
    pub(super) assigns: Vec<Option<bool>>, // Current assignments of boolean variables (None = unassigned, Some(true/false) = assigned)
    pub(super) clauses: Vec<Clause>,       // List of clauses in the solver
    pub(super) watches: Vec<Vec<usize>>,   // Watch lists for each literal (positive and negative)
    reason: Vec<Option<usize>>,            // Reason for each variable's assignment
    seen: Vec<bool>,                       // Temporary storage for conflict analysis
    analyze_toclear: Vec<usize>,           // Temporary storage for conflict analysis
    prop_q: VecDeque<Lit>,                 // Queue of literals to propagate
    pub(super) trail: Vec<Lit>,            // Trail of assigned literals for backtracking
    trail_lim: Vec<usize>,                 // Indices in the trail where decisions were made
    level: Vec<Option<usize>>,             // Decision level for each variable
    true_var: usize,                       // Index of the variable representing the constant true (used for unit propagation)
}

impl SatSolver {
    pub(super) fn new() -> Self {
        let mut sat = SatSolver {
            assigns: Vec::new(),
            clauses: Vec::new(),
            watches: Vec::new(),
            reason: Vec::new(),
            seen: Vec::new(),
            analyze_toclear: Vec::new(),
            prop_q: VecDeque::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            level: Vec::new(),
            true_var: 0,
        };
        sat.true_var = sat.mk_var();
        sat.add_clause([Lit::new(sat.true_var, false)]).expect("Should be able to add true clause");
        sat.propagate().expect("Should be able to propagate true clause");
        sat
    }

    pub fn true_lit(&self) -> Lit {
        Lit::new(self.true_var, false)
    }

    pub fn false_lit(&self) -> Lit {
        !self.true_lit()
    }

    pub(super) fn mk_var(&mut self) -> usize {
        let idx = self.assigns.len();
        self.assigns.push(None);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new()); // For the negated literal
        self.reason.push(None);
        self.seen.push(false);
        self.level.push(None);
        idx
    }

    pub(super) fn push(&mut self) {
        assert!(self.prop_q.is_empty(), "Cannot push decision level while propagation queue is not empty");
        self.trail_lim.push(self.trail.len());
        trace!("Pushed decision level {}", self.decision_level());
    }

    pub(super) fn enqueue_decision(&mut self, lit: Lit) -> bool {
        assert!(self.lit_value(&lit).is_none(), "Cannot decide on an already assigned literal: {}", lit);
        self.enqueue(lit, None)
    }

    pub(super) fn propagate(&mut self) -> Result<(), (usize, Vec<Lit>)> {
        while let Some(lit) = self.prop_q.pop_front() {
            let falsified = !lit;
            let falsified_index = falsified.index();
            let watches = mem::take(&mut self.watches[falsified_index]);
            for i in 0..watches.len() {
                let clause_idx = watches[i];
                // Keep the first watched literal as the other watcher and the second as the falsified one.
                if self.clauses[clause_idx].lits[0] == falsified {
                    self.clauses[clause_idx].lits.swap(0, 1);
                }

                // Check if clause is already satisfied
                if self.lit_value(&self.clauses[clause_idx].lits[0]) == Some(true) {
                    self.watches[falsified_index].push(clause_idx);
                    continue;
                }

                // Find a replacement watcher that is not currently false.
                let mut found_replacement = false;
                for j in 2..self.clauses[clause_idx].lits.len() {
                    let next_lit = self.clauses[clause_idx].lits[j];
                    if self.lit_value(&next_lit) != Some(false) {
                        self.clauses[clause_idx].lits.swap(1, j);
                        self.watches[next_lit.index()].push(clause_idx);
                        found_replacement = true;
                        break;
                    }
                }

                if found_replacement {
                    continue;
                }

                // If we reach here, the clause is either unit or unsatisfied
                self.watches[falsified_index].push(clause_idx); // Re-add the clause to the watch list
                if !self.enqueue(self.clauses[clause_idx].lits[0], Some(clause_idx)) {
                    for c_i in watches.iter().skip(i + 1) {
                        self.watches[falsified_index].push(*c_i);
                    }
                    self.prop_q.clear();
                    if self.decision_level() == 0 {
                        return Err((0, self.clauses[clause_idx].lits.clone()));
                    }
                    return Err(self.analyze_conflict(clause_idx));
                }
            }
        }
        Ok(())
    }

    fn analyze_conflict(&mut self, mut confl: usize) -> (usize, Vec<Lit>) {
        let mut path_c = 0;
        let mut p_lit = None; // Option<Lit>
        let mut learnt = vec![Lit::new(0, false)];
        let mut index = self.trail.len();

        self.analyze_toclear.clear();

        loop {
            let clause = &self.clauses[confl];
            let start_idx = if p_lit.is_none() { 0 } else { 1 };

            for j in start_idx..clause.lits.len() {
                let q = clause.lits[j];
                let var = q.var();

                if !self.seen[var] && self.level(var).unwrap_or(0) > 0 {
                    self.seen[var] = true;
                    self.analyze_toclear.push(var);

                    if self.level(var).unwrap_or(0) >= self.decision_level() {
                        path_c += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }

            loop {
                index -= 1;
                if self.seen[self.trail[index].var()] {
                    break;
                }
            }

            let next_p = self.trail[index];
            p_lit = Some(next_p);
            confl = self.reason[next_p.var()].unwrap_or_default();
            self.seen[next_p.var()] = false;
            path_c -= 1;

            if path_c == 0 {
                break;
            }
        }

        learnt[0] = !p_lit.unwrap();

        let mut j = 1;
        for i in 1..learnt.len() {
            let var = learnt[i].var();
            let mut redundant = false;

            if let Some(reason_idx) = self.reason[var] {
                redundant = true;
                let c = &self.clauses[reason_idx];
                for k in 1..c.lits.len() {
                    let v = c.lits[k].var();
                    if !self.seen[v] && self.level(v).unwrap_or(0) > 0 {
                        redundant = false; // C'è una dipendenza esterna
                        break;
                    }
                }
            }

            if !redundant {
                learnt[j] = learnt[i];
                j += 1;
            }
        }
        learnt.truncate(j);

        let mut bt_level = 0;
        if learnt.len() > 1 {
            let mut max_i = 1;
            let mut max_level = self.level(learnt[1].var()).unwrap_or(0);

            for (i, lit) in learnt.iter().enumerate().skip(2) {
                let l = self.level(lit.var()).unwrap_or(0);
                if l > max_level {
                    max_level = l;
                    max_i = i;
                }
            }

            learnt.swap(1, max_i);
            bt_level = max_level;
        }

        for &var in &self.analyze_toclear {
            self.seen[var] = false;
        }

        (bt_level, learnt)
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        trace!("Enqueue {}{}", lit, reason.map_or("".to_string(), |r| format!(" (reason: {})", r)));
        match self.lit_value(&lit) {
            None => {
                self.assigns[lit.var()] = if lit.sign() { Some(false) } else { Some(true) };
                self.level[lit.var()] = Some(self.decision_level());
                self.reason[lit.var()] = reason;
                self.trail.push(lit);
                self.prop_q.push_back(lit);
                true
            }
            Some(value) => value,
        }
    }

    pub(super) fn add_clause(&mut self, lits: impl IntoIterator<Item = Lit>) -> Result<(), Vec<Lit>> {
        let mut simplified_lits = Vec::new();

        for lit in lits {
            match self.lit_value(&lit) {
                Some(true) if self.level(lit.var()) == Some(0) => {
                    return Ok(());
                }
                Some(false) if self.level(lit.var()) == Some(0) => {
                    continue;
                }
                _ => {
                    if simplified_lits.contains(&!lit) {
                        return Ok(());
                    }
                    if !simplified_lits.contains(&lit) {
                        simplified_lits.push(lit);
                    }
                }
            }
        }

        match simplified_lits.len() {
            0 => return Err(simplified_lits),
            1 => {
                if self.decision_level() > 0 {
                    self.cancel_until(0);
                }
                if !self.enqueue(simplified_lits[0], None) {
                    return Err(simplified_lits);
                }
            }
            _ => {
                let clause_index = self.clauses.len();

                simplified_lits.sort_by_key(|l| self.lit_value(l).is_some());

                let clause = Clause { lits: simplified_lits.clone() };
                trace!("Adding clause {}: {}", clause_index, clause);

                for lit in &clause.lits[0..2] {
                    self.watches[lit.index()].push(clause_index);
                }
                self.clauses.push(clause);
                if self.lit_value(&simplified_lits[0]) == Some(false) || (self.lit_value(&simplified_lits[1]) == Some(false) && !self.enqueue(simplified_lits[0], Some(clause_index))) {
                    return Err(simplified_lits);
                }
            }
        }
        Ok(())
    }

    pub(super) fn value(&self, var: usize) -> &Option<bool> {
        self.assigns.get(var).expect("Variable index out of bounds")
    }

    fn lit_value(&self, lit: &Lit) -> Option<bool> {
        let val = self.value(lit.var());
        if lit.sign() { val.map(|v| !v) } else { *val }
    }

    pub(super) fn level(&self, var: usize) -> Option<usize> {
        self.level.get(var).copied().expect("Variable index out of bounds")
    }

    pub(super) fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        trace!("Canceling until level {}", level);
        while self.decision_level() > level {
            let lim = self.trail_lim.pop().unwrap();
            while self.trail.len() > lim {
                let lit = self.trail.pop().expect("Trail underflow while canceling until level");
                trace!("Undoing assignment of {}", lit);
                self.assigns[lit.var()] = None;
                self.reason[lit.var()] = None;
                self.level[lit.var()] = None;
            }
        }
    }
}

impl fmt::Display for SatSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Assignments:")?;
        for (i, val) in self.assigns.iter().enumerate() {
            if let Some(v) = val {
                writeln!(f, "  b{} = {}", i, v)?;
            } else {
                writeln!(f, "  b{} = unassigned", i)?;
            }
        }
        writeln!(f, "Clauses:")?;
        for (i, clause) in self.clauses.iter().enumerate() {
            writeln!(f, "  {}: {}", i, clause)?;
        }
        Ok(())
    }
}

// Compact encoding: x = var*2 + sign_bit, where sign_bit=1 means negated (MiniSat convention).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit {
    x: usize,
}

impl Lit {
    pub fn new(var: usize, sign: bool) -> Self {
        Lit { x: var * 2 + sign as usize }
    }

    /// Variable index.
    pub fn var(self) -> usize {
        self.x >> 1
    }

    /// True if this is a negated literal.
    pub fn sign(self) -> bool {
        self.x & 1 != 0
    }

    /// Compact integer index suitable for watch-list indexing (MiniSat's toInt).
    pub fn index(self) -> usize {
        self.x
    }
}

impl ops::Not for Lit {
    type Output = Self;

    fn not(self) -> Self {
        Lit { x: self.x ^ 1 }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.sign() { write!(f, "¬b{}", self.var()) } else { write!(f, "b{}", self.var()) }
    }
}

pub(super) struct Clause {
    lits: Vec<Lit>, // List of literals in the clause
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<String> = self.lits.iter().map(|l| l.to_string()).collect();
        write!(f, "({})", lits.join(" ∨ "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decide(sat: &mut SatSolver, lit: Lit) -> Result<(), (usize, Vec<Lit>)> {
        sat.push();
        sat.enqueue_decision(lit);
        sat.propagate()
    }

    #[test]
    fn test_conflict_analysis() {
        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();
        let b3 = sat.mk_var();
        let b4 = sat.mk_var();
        let b5 = sat.mk_var();
        let b6 = sat.mk_var();
        let b7 = sat.mk_var();
        let b8 = sat.mk_var();
        let b9 = sat.mk_var();

        // [(b1 ∨ b2) ∧ (b1 ∨ b3 ∨ b7) ∧ (¬b2 ∨ ¬b3 ∨ b4) ∧ (¬b4 ∨ b5 ∨ b8) ∧ (¬b4 ∨ b6 ∨ b9) ∧ (¬b5 ∨ ¬b6)]
        sat.add_clause([Lit::new(b1, false), Lit::new(b2, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b1, false), Lit::new(b3, false), Lit::new(b7, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b2, true), Lit::new(b3, true), Lit::new(b4, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b4, true), Lit::new(b5, false), Lit::new(b8, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b4, true), Lit::new(b6, false), Lit::new(b9, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b5, true), Lit::new(b6, true)]).expect("Should be able to add clause");

        // Decision: ¬b7
        decide(&mut sat, Lit::new(b7, true)).expect("Should be able to decide ¬b7");
        // Decision: ¬b8
        decide(&mut sat, Lit::new(b8, true)).expect("Should be able to decide ¬b8");
        // Decision: ¬b9
        decide(&mut sat, Lit::new(b9, true)).expect("Should be able to decide ¬b9");
        // Decision: ¬b1
        let result = decide(&mut sat, Lit::new(b1, true));
        assert!(result.is_err());
        let (bt_level, conflict_clause) = result.unwrap_err();
        assert_eq!(bt_level, 3);
        assert!(conflict_clause.contains(&Lit::new(b4, true)));
        assert!(conflict_clause.contains(&Lit::new(b8, false)));
        assert!(conflict_clause.contains(&Lit::new(b9, false)));
        sat.cancel_until(bt_level);
        sat.add_clause(conflict_clause).expect("Should be able to add learnt clause");
    }
}
