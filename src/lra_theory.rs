use crate::{
    rational::{InfRational, Rational},
    sat_solver::Lit,
};
use rug::{Assign, Rational as RugRational};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::BTreeMap, mem};

pub(super) struct LraTheory {
    ints: Vec<bool>,                                      // true = integer variable, false = real variable
    reals: Vec<InfRational>,                              // Current assignments
    pub(super) lbs: Vec<(Option<Lit>, InfRational)>,      // Current lower bounds
    pub(super) ubs: Vec<(Option<Lit>, InfRational)>,      // Current upper bounds
    pub(super) lin_to_slack: FxHashMap<SparseRow, usize>, // Mapping from linear constraints to their slack variable
    pub(super) tableau: BTreeMap<usize, SparseRow>,       // Tableau: basic variable -> linear expression over non-basic variables
    pub(super) t_watches: Vec<FxHashSet<usize>>,          // For each variable, the set of tableau rows containing it
    bound_trail: Vec<BoundUpdate>,                        // Trail of bound updates for backtracking
    trail_lim: Vec<usize>,                                // Trail limits
    rational_pool: Vec<RugRational>,                      // Pool of rational numbers for reuse
}

impl LraTheory {
    pub(super) fn new() -> Self {
        Self {
            ints: Vec::new(),
            reals: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            lin_to_slack: FxHashMap::default(),
            tableau: BTreeMap::new(),
            t_watches: Vec::new(),
            bound_trail: Vec::new(),
            trail_lim: Vec::new(),
            rational_pool: Vec::new(),
        }
    }

    pub(super) fn mk_int(&mut self) -> usize {
        self.mk_var(true)
    }

    pub(super) fn mk_real(&mut self) -> usize {
        self.mk_var(false)
    }

    fn mk_var(&mut self, is_int: bool) -> usize {
        let var = self.reals.len();

        self.ints.push(is_int);
        self.reals.push(Self::zero());
        self.lbs.push((None, Self::negative_inf()));
        self.ubs.push((None, Self::positive_inf()));
        self.t_watches.push(FxHashSet::default());

        var
    }

    fn zero() -> InfRational {
        InfRational::new(Rational::Finite(RugRational::from(0)), RugRational::from(0))
    }

    fn negative_inf() -> InfRational {
        InfRational::new(Rational::NegativeInf, RugRational::from(0))
    }

    fn positive_inf() -> InfRational {
        InfRational::new(Rational::PositiveInf, RugRational::from(0))
    }

    pub(super) fn value(&self, var: usize) -> &InfRational {
        self.reals.get(var).expect("variable index out of bounds")
    }

    pub(super) fn get_or_create_slack(&mut self, vars: SparseRow) -> usize {
        if let Some(&slack) = self.lin_to_slack.get(&vars) {
            return slack;
        }

        let slack = self.mk_real();

        // Keep the new basic slack variable consistent with the current model:
        // slack = sum(coeff_i * var_i).
        let mut slack_value = Self::zero();
        for (var, coeff) in vars.iter() {
            slack_value += &self.reals[*var] * coeff;
        }
        self.reals[slack] = slack_value;

        self.tableau.insert(slack, vars.clone());
        for &var in vars.keys() {
            self.t_watches[var].insert(slack);
        }
        self.lin_to_slack.insert(vars, slack);

        slack
    }

    pub(super) fn lb(&self, var: usize) -> &InfRational {
        &self.lbs.get(var).expect("variable index out of bounds").1
    }

    pub(super) fn ub(&self, var: usize) -> &InfRational {
        &self.ubs.get(var).expect("variable index out of bounds").1
    }

    pub(super) fn set_lb(&mut self, lit: Option<Lit>, var: usize, new_lb: InfRational) -> Result<bool, Vec<Lit>> {
        assert!(var < self.reals.len(), "variable index out of bounds: {var}");

        if &new_lb <= self.lb(var) {
            return Ok(false);
        }

        if &new_lb > self.ub(var) {
            let mut conflict = Vec::with_capacity(2);
            if let Some(l) = lit {
                conflict.push(!l);
            }
            if let Some(guard) = self.ubs[var].0 {
                conflict.push(!guard);
            }
            return Err(conflict);
        }

        let (c_lit, val) = self.lbs[var].clone();
        self.bound_trail.push(BoundUpdate::LowerBound { lit: c_lit, var, val });
        self.lbs[var] = (lit, new_lb.clone());

        if self.value(var) < &new_lb && !self.is_basic(var) {
            self.update(var, new_lb);
        }
        Ok(true)
    }

    pub(super) fn set_ub(&mut self, lit: Option<Lit>, var: usize, new_ub: InfRational) -> Result<bool, Vec<Lit>> {
        assert!(var < self.reals.len(), "variable index out of bounds: {var}");

        if &new_ub >= self.ub(var) {
            return Ok(false);
        }

        if &new_ub < self.lb(var) {
            let mut conflict = Vec::with_capacity(2);
            if let Some(l) = lit {
                conflict.push(!l);
            }
            if let Some(guard) = self.lbs[var].0 {
                conflict.push(!guard);
            }
            return Err(conflict);
        }

        let (c_lit, val) = self.ubs[var].clone();
        self.bound_trail.push(BoundUpdate::UpperBound { lit: c_lit, var, val });
        self.ubs[var] = (lit, new_ub.clone());

        if self.value(var) > &new_ub && !self.is_basic(var) {
            self.update(var, new_ub);
        }
        Ok(true)
    }

    fn is_basic(&self, var: usize) -> bool {
        self.tableau.contains_key(&var)
    }

    fn update(&mut self, var: usize, new_value: InfRational) {
        assert!(var < self.reals.len(), "variable index out of bounds: {var}");
        assert!(!self.is_basic(var), "cannot directly update a basic variable");
        assert!(&new_value >= self.lb(var) && &new_value <= self.ub(var), "new value must be within bounds");

        let old_value = self.reals[var].clone();
        let delta_var = &new_value - &old_value;

        if delta_var == Self::zero() {
            return;
        }

        let watched_rows: Vec<usize> = self.t_watches[var].iter().copied().collect();

        for row_var in watched_rows {
            let coeff = self.tableau[&row_var].get(&var).expect("watched variable must occur in tableau row").clone();
            let delta = &delta_var * &coeff;
            self.reals[row_var] += delta;
        }

        self.reals[var] = new_value;
    }

    pub fn check(&mut self) -> Result<(), Vec<Lit>> {
        loop {
            // we search for a basic variable whose value is not within its bounds..
            let var = self.tableau.iter().find_map(|(&var, _)| {
                if self.value(var) < self.lb(var) {
                    Some((var, self.lb(var).clone()))
                } else if self.value(var) > self.ub(var) {
                    Some((var, self.ub(var).clone()))
                } else {
                    None
                }
            });
            if let Some((leaving, val)) = var {
                // .. if we find one, we try to pivot it with a non-basic variable that can take it back within bounds
                if self.value(leaving) < &val {
                    let entering = (&self.tableau[&leaving]).into_iter().find_map(|(v, coeff)| if (coeff.is_positive() && self.value(*v) < self.ub(*v)) || (coeff.is_negative() && self.value(*v) > self.lb(*v)) { Some(*v) } else { None });
                    if let Some(entering) = entering {
                        self.pivot_and_update(entering, leaving, val.clone());
                    } else {
                        let mut conflict = Vec::new();
                        for (vr, vl) in &self.tableau[&leaving] {
                            if vl.is_positive()
                                && let Some(guard_lit) = self.ubs[*vr].0
                            {
                                conflict.push(!guard_lit);
                            } else if vl.is_negative()
                                && let Some(guard_lit) = self.lbs[*vr].0
                            {
                                conflict.push(!guard_lit);
                            }
                        }
                        if let Some(guard_lit) = self.lbs[leaving].0 {
                            conflict.push(!guard_lit);
                        }
                        return Err(conflict);
                    }
                }
                if self.value(leaving) > &val {
                    let entering = (&self.tableau[&leaving]).into_iter().find_map(|(v, coeff)| if (coeff.is_positive() && self.value(*v) > self.lb(*v)) || (coeff.is_negative() && self.value(*v) < self.ub(*v)) { Some(*v) } else { None });
                    if let Some(entering) = entering {
                        self.pivot_and_update(entering, leaving, val);
                    } else {
                        let mut conflict = Vec::new();
                        for (vr, vl) in &self.tableau[&leaving] {
                            if vl.is_positive()
                                && let Some(guard_lit) = self.lbs[*vr].0
                            {
                                conflict.push(!guard_lit);
                            } else if vl.is_negative()
                                && let Some(guard_lit) = self.ubs[*vr].0
                            {
                                conflict.push(!guard_lit);
                            }
                        }
                        if let Some(guard_lit) = self.ubs[leaving].0 {
                            conflict.push(!guard_lit);
                        }
                        self.minimize_conflict(&mut conflict);
                        return Err(conflict);
                    }
                }
            } else {
                return Ok(()); // all basic variables are within bounds, we are done
            }
        }
    }

    fn minimize_conflict(&self, conflict: &mut Vec<Lit>) {
        if conflict.len() <= 1 {
            return;
        }

        conflict.sort_unstable();
        conflict.dedup();

        conflict.retain(|_lit| true);
    }

    fn pivot(&mut self, entering: usize, leaving: usize) {
        assert!(entering < self.reals.len(), "variable index out of bounds: {entering}");
        assert!(leaving < self.reals.len(), "variable index out of bounds: {leaving}");
        assert!(self.is_basic(leaving), "leaving variable must be basic");
        assert!(!self.is_basic(entering), "entering variable must be non-basic");

        let leaving_row_vars: Vec<usize> = self.tableau[&leaving].keys().copied().collect();

        for var in leaving_row_vars {
            self.t_watches[var].remove(&leaving);
        }

        let mut new_row = self.tableau.remove(&leaving).expect("leaving variable must have a tableau row");

        let pivot_coeff = new_row.remove(&entering).expect("entering variable must occur in leaving row");
        assert!(!pivot_coeff.is_zero(), "pivot coefficient must be non-zero");

        let inv_pivot = (-pivot_coeff.clone()).recip();
        for coeff in new_row.values_mut() {
            *coeff *= &inv_pivot;
        }

        new_row.insert(leaving, pivot_coeff.recip());

        let affected_rows: Vec<usize> = mem::take(&mut self.t_watches[entering]).into_iter().collect();

        for row_var in affected_rows {
            if row_var == leaving {
                continue;
            }

            let Some(row) = self.tableau.get_mut(&row_var) else {
                continue;
            };
            let Some(coeff_entering) = row.remove(&entering) else {
                continue;
            };

            row.add_scaled(&new_row, &coeff_entering, &mut self.t_watches, row_var, &mut self.rational_pool);
        }

        for v in new_row.keys().copied() {
            self.t_watches[v].insert(entering);
        }

        self.tableau.insert(entering, new_row);
    }

    fn pivot_and_update(&mut self, entering: usize, leaving: usize, new_value: InfRational) {
        assert!(entering < self.reals.len(), "variable index out of bounds: {entering}");
        assert!(leaving < self.reals.len(), "variable index out of bounds: {leaving}");
        assert!(self.is_basic(leaving), "leaving variable must be basic");
        assert!(!self.is_basic(entering), "entering variable must be non-basic");
        assert!(&new_value >= self.lb(leaving) && &new_value <= self.ub(leaving), "new value for leaving variable must be within bounds");

        let pivot_coeff = self.tableau[&leaving].get(&entering).expect("entering variable must occur in leaving row").clone();
        assert!(!pivot_coeff.is_zero(), "pivot coefficient must be non-zero");

        let theta = (&new_value - self.value(leaving)) / &pivot_coeff;

        self.reals[leaving] = new_value;
        self.reals[entering] += &theta;

        let affected_rows: Vec<usize> = self.t_watches[entering].iter().copied().collect();

        for row_var in affected_rows {
            if row_var == leaving {
                continue;
            }

            let Some(row) = self.tableau.get(&row_var) else {
                continue;
            };

            let Some(coeff) = row.get(&entering) else {
                continue;
            };

            self.reals[row_var] += &theta * coeff;
        }

        self.pivot(entering, leaving);
    }

    pub(super) fn check_ints(&self) -> Result<(), (usize, Rational)> {
        for (var, &is_int) in self.ints.iter().enumerate() {
            if is_int {
                let val = self.value(var);
                if !val.infinitesimal_part().is_zero() || !val.rational_part().is_integer() {
                    return Err((var, val.rational_part().clone()));
                }
            }
        }
        Ok(())
    }

    fn fract_part(val: &rug::Rational) -> rug::Rational {
        let mut floor = val.clone();
        floor.floor_mut();

        let mut f = val.clone();
        f -= floor;
        f
    }

    pub(super) fn generate_gomory_cut(&mut self, basic_var: usize) -> Option<(SparseRow, rug::Rational)> {
        let Rational::Finite(val) = self.value(basic_var).rational_part() else { unreachable!("basic variable should have a finite rational value") };
        let f0 = Self::fract_part(val);

        if f0.is_zero() {
            return None;
        }

        let row = self.tableau.get(&basic_var)?;
        let mut cut_row = SparseRow::new();

        for (nb_var, coeff) in row.iter() {
            if !self.ints[*nb_var] {
                return None;
            }

            let fj = Self::fract_part(coeff);
            if !fj.is_zero() {
                cut_row.add_coeff(*nb_var, &fj);
            }
        }

        if cut_row.is_empty() {
            return None;
        }

        Some((cut_row, f0))
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.bound_trail.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];

        while self.bound_trail.len() > target_len {
            let update = self.bound_trail.pop().expect("trail should contain an update");

            match update {
                BoundUpdate::LowerBound { lit, var, val } => {
                    self.lbs[var] = (lit, val);
                }
                BoundUpdate::UpperBound { lit, var, val } => {
                    self.ubs[var] = (lit, val);
                }
            }
        }

        self.trail_lim.truncate(level);
    }
}

#[derive(Clone, Default, Debug, PartialEq, Eq, Hash)]
pub(super) struct SparseRow {
    pub terms: Vec<(usize, RugRational)>,
}

impl SparseRow {
    pub fn new() -> Self {
        Self { terms: Vec::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, (usize, RugRational)> {
        self.terms.iter()
    }

    pub fn get(&self, var: &usize) -> Option<&RugRational> {
        self.terms.binary_search_by_key(var, |&(v, _)| v).ok().map(|idx| &self.terms[idx].1)
    }

    pub fn insert(&mut self, var: usize, coeff: RugRational) {
        match self.terms.binary_search_by_key(&var, |&(v, _)| v) {
            Ok(idx) => self.terms[idx].1 = coeff,
            Err(idx) => self.terms.insert(idx, (var, coeff)),
        }
    }

    pub fn remove(&mut self, var: &usize) -> Option<RugRational> {
        if let Ok(idx) = self.terms.binary_search_by_key(var, |&(v, _)| v) { Some(self.terms.remove(idx).1) } else { None }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&usize, &mut RugRational) -> bool,
    {
        self.terms.retain_mut(|(v, c)| f(v, c));
    }

    pub fn keys(&self) -> impl Iterator<Item = &usize> {
        self.terms.iter().map(|(v, _)| v)
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut RugRational> {
        self.terms.iter_mut().map(|(_, c)| c)
    }

    pub fn add_coeff(&mut self, var: usize, delta: &RugRational) {
        if delta.is_zero() {
            return;
        }
        match self.terms.binary_search_by_key(&var, |&(v, _)| v) {
            Ok(idx) => {
                self.terms[idx].1 += delta;
            }
            Err(idx) => {
                self.terms.insert(idx, (var, delta.clone()));
            }
        }
    }

    pub fn add_scaled(&mut self, other: &SparseRow, scale: &RugRational, watches: &mut [FxHashSet<usize>], target_row_var: usize, pool: &mut Vec<RugRational>) {
        let old_terms = std::mem::take(&mut self.terms);
        let mut new_terms = Vec::with_capacity(old_terms.len());

        let mut old_iter = old_terms.into_iter().peekable();
        let mut other_iter = other.terms.iter().peekable();

        while let (Some(&(v1, _)), Some(&(v2, _))) = (old_iter.peek(), other_iter.peek()) {
            if v1 < *v2 {
                new_terms.push(old_iter.next().unwrap());
            } else if v1 > *v2 {
                let (v2, c2) = other_iter.next().unwrap();

                let mut delta = pool.pop().unwrap_or_else(|| rug::Rational::from(0));
                delta.assign(c2 * scale);

                if !delta.is_zero() {
                    watches[*v2].insert(target_row_var);
                    new_terms.push((*v2, delta));
                } else {
                    pool.push(delta);
                }
            } else {
                let (v1, mut c1) = old_iter.next().unwrap();
                let (_, c2) = other_iter.next().unwrap();

                let mut tmp_delta = pool.pop().unwrap_or_else(|| rug::Rational::from(0));
                tmp_delta.assign(c2 * scale);

                c1 += &tmp_delta;
                pool.push(tmp_delta);

                if c1.is_zero() {
                    watches[v1].remove(&target_row_var);
                    pool.push(c1);
                } else {
                    new_terms.push((v1, c1));
                }
            }
        }

        new_terms.extend(old_iter);

        for (v2, c2) in other_iter {
            let mut delta = pool.pop().unwrap_or_else(|| rug::Rational::from(0));
            delta.assign(c2 * scale);

            if !delta.is_zero() {
                watches[*v2].insert(target_row_var);
                new_terms.push((*v2, delta));
            } else {
                pool.push(delta);
            }
        }

        self.terms = new_terms;
    }
}

impl<'a> IntoIterator for &'a SparseRow {
    type Item = &'a (usize, RugRational);
    type IntoIter = std::slice::Iter<'a, (usize, RugRational)>;

    fn into_iter(self) -> Self::IntoIter {
        self.terms.iter()
    }
}

enum BoundUpdate {
    LowerBound { lit: Option<Lit>, var: usize, val: InfRational },
    UpperBound { lit: Option<Lit>, var: usize, val: InfRational },
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::Rational as RugRational;

    fn real(val: i32) -> InfRational {
        InfRational::new(Rational::Finite(RugRational::from(val)), RugRational::from(0))
    }

    fn add_test_row(theory: &mut LraTheory, basic_var: usize, terms: &[(usize, i32)]) {
        let mut row = SparseRow::new();
        for &(var, coeff) in terms {
            row.insert(var, RugRational::from(coeff));
            theory.t_watches[var].insert(basic_var);
        }
        theory.tableau.insert(basic_var, row);
    }

    fn build_row(terms: &[(usize, i32)]) -> SparseRow {
        let mut row = SparseRow::new();
        for &(var, coeff) in terms {
            row.insert(var, RugRational::from(coeff));
        }
        row
    }

    #[test]
    fn test_pure_pivot_algebra() {
        let mut lra = LraTheory::new();

        let x = lra.mk_real(); // 0
        let y = lra.mk_real(); // 1
        let s = lra.mk_real(); // 2 (slack)

        add_test_row(&mut lra, s, &[(x, 2), (y, -3)]);

        assert!(lra.is_basic(s));
        assert!(!lra.is_basic(x));
        assert!(lra.t_watches[x].contains(&s));

        lra.pivot(y, s);

        assert!(!lra.is_basic(s));
        assert!(lra.is_basic(y));
        assert!(!lra.t_watches[y].contains(&s), "y should not be watching s after pivoting");
        assert!(lra.t_watches[x].contains(&y), "x should now be watched by y after pivoting");
        assert!(lra.t_watches[s].contains(&y), "s should now be watched by y after pivoting");

        let row_y = lra.tableau.get(&y).expect("y must have a row in the tableau");
        assert_eq!(row_y.get(&x).unwrap(), &RugRational::from((2, 3)));
        assert_eq!(row_y.get(&s).unwrap(), &RugRational::from((-1, 3)));
    }

    #[test]
    fn test_pivot_and_update_maintains_equality() {
        let mut lra = LraTheory::new();

        let x = lra.mk_real();
        let y = lra.mk_real();
        let s = lra.mk_real();

        add_test_row(&mut lra, s, &[(x, 1), (y, 1)]);

        lra.reals[x] = real(5);
        lra.reals[y] = real(3);
        lra.reals[s] = real(8);

        lra.set_lb(None, s, real(0)).expect("setting lower bound should succeed");
        lra.set_ub(None, s, real(10)).expect("setting upper bound should succeed");

        lra.pivot_and_update(y, s, real(6));

        assert_eq!(lra.value(s), &real(6));
        assert_eq!(lra.value(x), &real(5));
        assert_eq!(lra.value(y), &real(1), "y should have absorbed the delta of -2");
    }

    #[test]
    fn test_check_resolves_out_of_bounds() {
        let mut lra = LraTheory::new();

        let x = lra.mk_real();
        let y = lra.mk_real();
        let s = lra.mk_real();

        add_test_row(&mut lra, s, &[(x, 1), (y, 1)]); // s = x + y

        lra.set_lb(None, x, real(0)).expect("setting lower bound should succeed");
        lra.set_ub(None, x, real(10)).expect("setting upper bound should succeed");
        lra.set_lb(None, y, real(-10)).expect("setting lower bound should succeed");
        lra.set_ub(None, y, real(10)).expect("setting upper bound should succeed");
        lra.set_ub(None, s, real(5)).expect("setting upper bound should succeed");

        lra.set_lb(None, x, real(6)).expect("setting lower bound should succeed");

        assert!(lra.value(s) > lra.ub(s));

        let result = lra.check();

        assert!(result.is_ok(), "check should resolve the out-of-bounds situation");

        assert_eq!(lra.value(s), &real(5));
        assert_eq!(lra.value(y), &real(-1));

        assert!(!lra.is_basic(s));
        assert!(lra.value(s) <= lra.ub(s));
    }

    #[test]
    fn test_check_detects_conflict() {
        let mut lra = LraTheory::new();

        let x = lra.mk_real();
        let y = lra.mk_real();
        let s = lra.mk_real();

        add_test_row(&mut lra, s, &[(x, 1), (y, 1)]);

        lra.set_lb(Some(Lit::new(1, false)), x, real(3)).expect("setting lower bound should succeed");
        assert_eq!(lra.value(s), &real(3));

        lra.set_lb(Some(Lit::new(2, false)), y, real(4)).expect("setting lower bound should succeed");
        assert_eq!(lra.value(s), &real(7));

        lra.set_ub(Some(Lit::new(3, false)), s, real(5)).expect("setting upper bound should succeed");

        let result = lra.check();

        assert!(result.is_err());
        let conflict = result.unwrap_err();

        assert!(conflict.contains(&Lit::new(1, true)));
        assert!(conflict.contains(&Lit::new(2, true)));
        assert!(conflict.contains(&Lit::new(3, true)));
    }

    #[test]
    fn test_sparse_row_add_scaled_cancellation() {
        let rational_pool = &mut Vec::new();
        // row1 = 2*v0 + 3*v1 - 1*v3
        let mut row1 = build_row(&[(0, 2), (1, 3), (3, -1)]);
        // row2 = 1*v1 + 4*v2 + 2*v3
        let row2 = build_row(&[(1, 1), (2, 4), (3, 2)]);

        let mut watches = vec![FxHashSet::default(); 4];
        let target_row = 10;

        watches[0].insert(target_row);
        watches[1].insert(target_row);
        watches[3].insert(target_row);

        let scale = RugRational::from(-3);
        row1.add_scaled(&row2, &scale, &mut watches, target_row, rational_pool);

        assert_eq!(row1.len(), 3, "The row should have exactly 3 active terms");
        assert_eq!(row1.get(&0), Some(&RugRational::from(2)));
        assert_eq!(row1.get(&1), None, "v1 should have been removed from the row");
        assert_eq!(row1.get(&2), Some(&RugRational::from(-12)));
        assert_eq!(row1.get(&3), Some(&RugRational::from(-7)));

        assert!(watches[0].contains(&target_row), "The watch for v0 should remain unchanged");
        assert!(!watches[1].contains(&target_row), "The watch for v1 should have been removed because the coefficient became zero");
        assert!(watches[2].contains(&target_row), "The watch for v2 should have been added dynamically");
        assert!(watches[3].contains(&target_row), "The watch for v3 should remain unchanged after the coefficient update");
    }

    #[test]
    fn test_tableau_pivot_nested_substitution() {
        let mut lra = LraTheory::new();

        let x = lra.mk_real(); // 0
        let y = lra.mk_real(); // 1
        let z = lra.mk_real(); // 2

        let s1 = lra.mk_real(); // 3 (slack 1)
        let s2 = lra.mk_real(); // 4 (slack 2)

        // s1 = 2x + 1y - 1z
        add_test_row(&mut lra, s1, &[(x, 2), (y, 1), (z, -1)]);
        // s2 = 1x - 1y + 2z
        add_test_row(&mut lra, s2, &[(x, 1), (y, -1), (z, 2)]);

        lra.pivot(x, s2);

        let row_s1 = lra.tableau.get(&s1).expect("s1 should still be present in the tableau");

        assert_eq!(row_s1.get(&s2), Some(&RugRational::from(2)));
        assert_eq!(row_s1.get(&y), Some(&RugRational::from(3)));
        assert_eq!(row_s1.get(&z), Some(&RugRational::from(-5)));

        assert_eq!(row_s1.get(&x), None, "x is now basic, so it cannot appear in s1");

        // Verify that the reverse dependencies (watches) remain consistent.
        assert!(!lra.t_watches[x].contains(&s1), "s1 should no longer watch x");
        assert!(lra.t_watches[s2].contains(&s1), "s1 should now watch s2");
        assert!(lra.t_watches[y].contains(&s1));
        assert!(lra.t_watches[z].contains(&s1));
    }
}
