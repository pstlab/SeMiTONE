use crate::sat_solver::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    fmt,
    ops::{Index, IndexMut},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumVar(usize);

impl<T> Index<EnumVar> for Vec<T> {
    type Output = T;
    fn index(&self, var: EnumVar) -> &Self::Output {
        &self[var.0]
    }
}

impl<T> IndexMut<EnumVar> for Vec<T> {
    fn index_mut(&mut self, var: EnumVar) -> &mut Self::Output {
        &mut self[var.0]
    }
}

impl fmt::Display for EnumVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.0)
    }
}

pub(super) struct EnumTheory {
    pub(super) initial_domain: Vec<FxHashSet<usize>>,
    pub(super) active_domain: Vec<FxHashSet<usize>>,

    trail: Vec<(EnumVar, usize)>,
    trail_lim: Vec<usize>,

    removal_reasons: FxHashMap<(EnumVar, usize), Lit>,
}

impl EnumTheory {
    pub(super) fn new() -> Self {
        Self {
            initial_domain: Vec::new(),
            active_domain: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            removal_reasons: FxHashMap::default(),
        }
    }

    pub(super) fn mk_var(&mut self, domain: FxHashSet<usize>) -> EnumVar {
        let id = EnumVar(self.initial_domain.len());
        self.initial_domain.push(domain.clone());
        self.active_domain.push(domain);
        id
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];
        while self.trail.len() > target_len {
            let (var, val) = self.trail.pop().expect("Enum trail underflow");
            self.active_domain[var].insert(val);
            self.removal_reasons.remove(&(var, val));
        }
        self.trail_lim.truncate(level);
    }

    pub(super) fn set_eq(&mut self, lit: Option<Lit>, var: EnumVar, val: usize) -> Result<bool, Vec<Lit>> {
        if !self.active_domain[var].contains(&val) {
            let mut conflict = Vec::with_capacity(2);
            if let Some(l) = lit {
                conflict.push(!l);
            }
            if let Some(&reason) = self.removal_reasons.get(&(var, val)) {
                conflict.push(!reason);
            }
            return Err(conflict);
        }

        let to_remove: Vec<usize> = self.active_domain[var].iter().filter(|&&v| v != val).copied().collect();

        if to_remove.is_empty() {
            return Ok(false);
        }

        for v in to_remove {
            self.active_domain[var].remove(&v);
            self.trail.push((var, v));
            if let Some(l) = lit {
                self.removal_reasons.insert((var, v), l);
            }
        }
        Ok(true)
    }

    pub(super) fn set_neq(&mut self, lit: Option<Lit>, var: EnumVar, val: usize) -> Result<bool, Vec<Lit>> {
        if !self.active_domain[var].contains(&val) {
            return Ok(false); // Already removed
        }

        self.active_domain[var].remove(&val);
        self.trail.push((var, val));
        if let Some(l) = lit {
            self.removal_reasons.insert((var, val), l);
        }

        if self.active_domain[var].is_empty() {
            let mut conflict = Vec::new();
            if let Some(l) = lit {
                conflict.push(!l);
            }

            for &v in &self.initial_domain[var] {
                if v != val
                    && let Some(&reason) = self.removal_reasons.get(&(var, v))
                    && !conflict.contains(&!reason)
                {
                    conflict.push(!reason);
                }
            }
            return Err(conflict);
        }
        Ok(true)
    }

    pub(super) fn initial_domain(&self, var: EnumVar) -> &FxHashSet<usize> {
        &self.initial_domain[var]
    }

    pub(super) fn domain(&self, var: EnumVar) -> &FxHashSet<usize> {
        &self.active_domain[var]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SatSolver;

    fn setup_enum() -> (EnumTheory, EnumVar) {
        let mut theory = EnumTheory::new();
        let domain: FxHashSet<usize> = vec![1, 2, 3].into_iter().collect();
        let var = theory.mk_var(domain);
        (theory, var)
    }

    #[test]
    fn test_enum_exhaustive_denial_conflict() {
        let (mut theory, var) = setup_enum();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();
        let b3 = sat.mk_var();

        let lit1 = Lit::new(b1, false); // SAT deduce: var != 1
        let lit2 = Lit::new(b2, false); // SAT deduce: var != 2
        let lit3 = Lit::new(b3, false); // SAT deduce: var != 3

        assert_eq!(theory.set_neq(Some(lit1), var, 1), Ok(true));
        assert_eq!(theory.set_neq(Some(lit2), var, 2), Ok(true));

        let res3 = theory.set_neq(Some(lit3), var, 3);
        assert!(res3.is_err());

        let conflict = res3.unwrap_err();

        assert_eq!(conflict.len(), 3);
        assert!(conflict.contains(&!lit1));
        assert!(conflict.contains(&!lit2));
        assert!(conflict.contains(&!lit3));
    }

    #[test]
    fn test_enum_positive_contradiction() {
        let (mut theory, var) = setup_enum();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();

        let lit_deny = Lit::new(b1, false);
        let lit_assert = Lit::new(b2, false);

        assert_eq!(theory.set_neq(Some(lit_deny), var, 1), Ok(true));

        let res_assert = theory.set_eq(Some(lit_assert), var, 1);
        assert!(res_assert.is_err());

        let conflict = res_assert.unwrap_err();

        assert!(conflict.contains(&!lit_assert));
        assert!(conflict.contains(&!lit_deny));
    }

    #[test]
    fn test_enum_positive_assignment_removes_others() {
        let (mut theory, var) = setup_enum();

        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();
        let b2 = sat.mk_var();

        let lit_set_1 = Lit::new(b1, false);
        let lit_set_2 = Lit::new(b2, false);

        assert_eq!(theory.set_eq(Some(lit_set_1), var, 1), Ok(true));
        assert_eq!(theory.active_domain[var].len(), 1);
        assert!(theory.active_domain[var].contains(&1));

        let res_set_2 = theory.set_eq(Some(lit_set_2), var, 2);
        assert!(res_set_2.is_err());

        let conflict = res_set_2.unwrap_err();

        assert!(conflict.contains(&!lit_set_2));
        assert!(conflict.contains(&!lit_set_1));
    }

    #[test]
    fn test_enum_backtracking_recovers_domain() {
        let (mut theory, var) = setup_enum();
        let mut sat = SatSolver::new();
        let b1 = sat.mk_var();

        let lit1 = Lit::new(b1, false);

        theory.push();

        assert_eq!(theory.set_neq(Some(lit1), var, 1), Ok(true));
        assert_eq!(theory.active_domain[var].len(), 2);

        theory.cancel_until(0);

        assert_eq!(theory.active_domain[var].len(), 3);
        assert!(!theory.removal_reasons.contains_key(&(var, 1)));

        assert_eq!(theory.set_neq(Some(lit1), var, 1), Ok(true));
    }
}
