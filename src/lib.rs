pub mod ast;
mod enum_theory;
mod lra_theory;
#[cfg(feature = "parser")]
pub mod parser;
mod proxy;
pub mod rational;
mod sat_solver;
#[cfg(feature = "parser")]
pub mod solver;

use crate::{
    ast::{ArithExpr, BoolExpr, EnumExpr, Expr},
    enum_theory::EnumTheory,
    lra_theory::{LraTheory, SparseRow},
    proxy::{ProxyRegistry, TheoryConstraint},
    rational::{InfRational, Rational},
    sat_solver::{Lit, SatSolver},
};
use rug::Assign;

/// Main solver entry point for propositional, linear arithmetic, and enum constraints.
///
/// The solver combines a SAT core with theory propagation for linear rational
/// arithmetic and finite-domain enum reasoning.
pub struct SmtSolver {
    registry: ProxyRegistry,
    sat_solver: SatSolver,
    lra_theory: LraTheory,
    enum_theory: EnumTheory,
    notified_len: usize,
    user_scopes: Vec<(usize, usize)>,
}

impl Default for SmtSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtSolver {
    /// Creates a new empty solver instance.
    pub fn new() -> Self {
        Self {
            registry: ProxyRegistry::new(),
            sat_solver: SatSolver::new(),
            lra_theory: LraTheory::new(),
            enum_theory: EnumTheory::new(),
            notified_len: 0,
            user_scopes: Vec::new(),
        }
    }

    /// Allocates a new Boolean variable.
    pub fn new_bool(&mut self) -> BoolExpr {
        BoolExpr::Var(self.sat_solver.mk_var())
    }

    /// Allocates a new integer variable.
    pub fn new_int(&mut self) -> ArithExpr {
        ArithExpr::IntVar(self.lra_theory.mk_int())
    }

    /// Allocates a new real variable.
    pub fn new_real(&mut self) -> ArithExpr {
        ArithExpr::RealVar(self.lra_theory.mk_real())
    }

    /// Allocates a new enum variable with the given finite domain.
    pub fn new_enum(&mut self, domain: impl IntoIterator<Item = i32>) -> EnumExpr {
        EnumExpr::Var(self.enum_theory.mk_var(domain.into_iter().collect()))
    }

    pub fn num_vars(&self) -> usize {
        self.sat_solver.num_vars()
    }

    pub fn add_clause(&mut self, clause: impl IntoIterator<Item = Lit>) -> Result<(), Vec<Lit>> {
        self.sat_solver.add_clause(clause)
    }

    /// Adds a Boolean constraint to the current solver context.
    ///
    /// Returns `Ok(())` when the formula is consistent with the current theory
    /// state, or an error containing the backtracking scope and a conflict witness.
    pub fn assert(&mut self, expr: &BoolExpr) -> Result<(), (usize, Vec<Lit>)> {
        if !self.assert_internal(expr, true) {
            return Err((self.user_scopes.len(), vec![self.sat_solver.false_lit()]));
        }
        self.propagate()
    }

    fn assert_internal(&mut self, expr: &BoolExpr, polarity: bool) -> bool {
        match (expr, polarity) {
            (BoolExpr::Not(inner), _) => self.assert_internal(inner, !polarity),
            (BoolExpr::And(args), true) | (BoolExpr::Or(args), false) => {
                for arg in args {
                    if !self.assert_internal(arg, polarity) {
                        return false;
                    }
                }
                true
            }
            (BoolExpr::Or(args), true) | (BoolExpr::And(args), false) => {
                let mut clause = Vec::with_capacity(args.len());
                for arg in args {
                    let mut lit = self.encode_bool(arg);
                    if !polarity {
                        lit = !lit;
                    }
                    clause.push(lit);
                }
                self.sat_solver.add_clause(clause).is_ok()
            }
            (BoolExpr::Lt(e1, e2), _) | (BoolExpr::Le(e1, e2), _) | (BoolExpr::Ge(e1, e2), _) | (BoolExpr::Gt(e1, e2), _) => {
                let (vars, const_term) = self.diff(e1, e2);
                if vars.is_empty() {
                    let is_sat = match expr {
                        BoolExpr::Lt(_, _) => const_term.is_negative(),
                        BoolExpr::Le(_, _) => const_term.is_negative() || const_term.is_zero(),
                        BoolExpr::Ge(_, _) => !const_term.is_negative(),
                        BoolExpr::Gt(_, _) => const_term.is_positive(),
                        _ => unreachable!(),
                    };
                    return if polarity { is_sat } else { !is_sat };
                }

                let (is_upper_bound, eps_val) = match (expr, polarity) {
                    (BoolExpr::Lt(_, _), true) => (true, rug::Rational::from(-1)),
                    (BoolExpr::Lt(_, _), false) => (false, rug::Rational::from(0)),
                    (BoolExpr::Le(_, _), true) => (true, rug::Rational::from(0)),
                    (BoolExpr::Le(_, _), false) => (false, rug::Rational::from(1)),
                    (BoolExpr::Ge(_, _), true) => (false, rug::Rational::from(0)),
                    (BoolExpr::Ge(_, _), false) => (true, rug::Rational::from(-1)),
                    (BoolExpr::Gt(_, _), true) => (false, rug::Rational::from(1)),
                    (BoolExpr::Gt(_, _), false) => (true, rug::Rational::from(0)),
                    _ => unreachable!(),
                };

                let bound = InfRational::new(Rational::Finite(-const_term.clone()), eps_val);

                if vars.len() == 1 {
                    let (var, coeff) = vars.iter().next().unwrap();
                    let final_bound = bound / coeff.clone();
                    if is_upper_bound == coeff.is_positive() { self.lra_theory.set_ub(None, *var, final_bound).is_ok() } else { self.lra_theory.set_lb(None, *var, final_bound).is_ok() }
                } else {
                    let slack = self.lra_theory.get_or_create_slack(vars);
                    if is_upper_bound { self.lra_theory.set_ub(None, slack, bound).is_ok() } else { self.lra_theory.set_lb(None, slack, bound).is_ok() }
                }
            }
            (BoolExpr::Eq(e1, e2), _) => {
                if let (Expr::Arith(a1), Expr::Arith(a2)) = (&**e1, &**e2) {
                    let (vars, const_term) = self.diff(a1, a2);

                    if vars.is_empty() {
                        let is_sat = const_term.is_zero();
                        return if polarity { is_sat } else { !is_sat };
                    }

                    if polarity {
                        let bound = InfRational::new(Rational::Finite(-const_term.clone()), rug::Rational::from(0));

                        if vars.len() == 1 {
                            let (var, coeff) = vars.iter().next().unwrap();
                            let final_bound = bound / coeff.clone();
                            self.lra_theory.set_lb(None, *var, final_bound.clone()).is_ok() && self.lra_theory.set_ub(None, *var, final_bound).is_ok()
                        } else {
                            let slack = self.lra_theory.get_or_create_slack(vars);
                            self.lra_theory.set_lb(None, slack, bound.clone()).is_ok() && self.lra_theory.set_ub(None, slack, bound).is_ok()
                        }
                    } else {
                        let lt_lit = self.mk_le(a1, a2, true);
                        let gt_lit = self.mk_ge(a1, a2, true);
                        self.sat_solver.add_clause([lt_lit, gt_lit]).is_ok()
                    }
                } else {
                    let mut lit = self.encode_eq(e1, e2);
                    if !polarity {
                        lit = !lit;
                    }
                    self.sat_solver.add_clause([lit]).is_ok()
                }
            }
            _ => {
                let mut lit = self.encode_bool(expr);
                if !polarity {
                    lit = !lit;
                }
                self.sat_solver.add_clause([lit]).is_ok()
            }
        }
    }

    fn encode_bool(&mut self, expr: &BoolExpr) -> Lit {
        match expr {
            BoolExpr::True => self.sat_solver.true_lit(),
            BoolExpr::False => !self.sat_solver.true_lit(),
            BoolExpr::Var(v) => Lit::new(*v, false),
            BoolExpr::Not(inner) => match inner.as_ref() {
                BoolExpr::Lt(a1, a2) => self.mk_ge(a1, a2, false),
                BoolExpr::Le(a1, a2) => self.mk_ge(a1, a2, true),
                BoolExpr::Ge(a1, a2) => self.mk_le(a1, a2, true),
                BoolExpr::Gt(a1, a2) => self.mk_le(a1, a2, false),
                _ => !self.encode_bool(inner),
            },
            BoolExpr::And(terms) => {
                let mut lits = Vec::with_capacity(terms.len());
                for term in terms {
                    lits.push(self.encode_bool(term));
                }

                let proxy_var = self.sat_solver.mk_var();
                let proxy_lit = Lit::new(proxy_var, true);

                for &lit in &lits {
                    self.sat_solver.add_clause([!proxy_lit, lit]).expect("Failed to add clause");
                }

                let mut big_clause: Vec<Lit> = lits.into_iter().map(|l| !l).collect();
                big_clause.push(proxy_lit);
                self.sat_solver.add_clause(big_clause).expect("Failed to add clause");

                proxy_lit
            }
            BoolExpr::Or(terms) => {
                let mut lits = Vec::with_capacity(terms.len());
                for term in terms {
                    lits.push(self.encode_bool(term));
                }

                let proxy_var = self.sat_solver.mk_var();
                let proxy_lit = Lit::new(proxy_var, true);

                for &lit in &lits {
                    self.sat_solver.add_clause([!lit, proxy_lit]).expect("Failed to add clause");
                }

                let mut big_clause = lits;
                big_clause.push(!proxy_lit);
                self.sat_solver.add_clause(big_clause).expect("Failed to add clause");

                proxy_lit
            }
            BoolExpr::Lt(e1, e2) => self.mk_le(e1, e2, true),
            BoolExpr::Le(e1, e2) => self.mk_le(e1, e2, false),
            BoolExpr::Ge(e1, e2) => self.mk_ge(e1, e2, false),
            BoolExpr::Gt(e1, e2) => self.mk_ge(e1, e2, true),
            BoolExpr::Eq(e1, e2) => self.encode_eq(e1, e2),
        }
    }

    fn encode_eq(&mut self, expr1: &Expr, expr2: &Expr) -> Lit {
        match (expr1, expr2) {
            (Expr::Arith(a1), Expr::Arith(a2)) => self.mk_arith_eq(a1, a2),
            (Expr::Bool(b1), Expr::Bool(b2)) => {
                let l1 = self.encode_bool(b1);
                let l2 = self.encode_bool(b2);
                let proxy_var = self.sat_solver.mk_var();
                let p = Lit::new(proxy_var, true);

                self.sat_solver.add_clause([!p, l1, !l2]).expect("Failed to add clause");
                self.sat_solver.add_clause([!p, !l1, l2]).expect("Failed to add clause");
                self.sat_solver.add_clause([p, l1, l2]).expect("Failed to add clause");
                self.sat_solver.add_clause([p, !l1, !l2]).expect("Failed to add clause");

                p
            }
            (Expr::Enum(e1), Expr::Enum(e2)) => self.mk_enum_eq(e1, e2),
            _ => panic!("Type mismatch in Eq: cannot compare different domains.\nLeft: {:?}\nRight: {:?}", expr1, expr2),
        }
    }

    fn mk_enum_eq(&mut self, e1: &EnumExpr, e2: &EnumExpr) -> Lit {
        match (e1, e2) {
            (EnumExpr::Const(c1), EnumExpr::Const(c2)) => {
                if c1 == c2 {
                    self.sat_solver.true_lit()
                } else {
                    self.sat_solver.false_lit()
                }
            }
            (EnumExpr::Var(v), EnumExpr::Const(c)) | (EnumExpr::Const(c), EnumExpr::Var(v)) => self.get_or_create_proxy(TheoryConstraint::EnumEq(*v, *c)),
            (EnumExpr::Var(v1), EnumExpr::Var(v2)) => {
                if v1 == v2 {
                    return self.sat_solver.true_lit();
                }

                let domain1 = self.enum_theory.initial_domains[*v1].clone();
                let domain2 = self.enum_theory.initial_domains[*v2].clone();
                let common: Vec<i32> = domain1.intersection(&domain2).copied().collect();

                if common.is_empty() {
                    return self.sat_solver.false_lit();
                }

                let mut lits = Vec::with_capacity(common.len());
                for val in common {
                    let p1 = self.get_or_create_proxy(TheoryConstraint::EnumEq(*v1, val));
                    let p2 = self.get_or_create_proxy(TheoryConstraint::EnumEq(*v2, val));

                    let and_proxy_var = self.sat_solver.mk_var();
                    let and_proxy = Lit::new(and_proxy_var, false);

                    self.sat_solver.add_clause([!and_proxy, p1]).unwrap();
                    self.sat_solver.add_clause([!and_proxy, p2]).unwrap();
                    self.sat_solver.add_clause([!p1, !p2, and_proxy]).unwrap();

                    lits.push(and_proxy);
                }

                let or_proxy_var = self.sat_solver.mk_var();
                let or_proxy = Lit::new(or_proxy_var, false);

                for &lit in &lits {
                    self.sat_solver.add_clause([!lit, or_proxy]).unwrap();
                }

                let mut big_clause = lits;
                big_clause.push(!or_proxy);
                self.sat_solver.add_clause(big_clause).unwrap();

                or_proxy
            }
        }
    }

    fn mk_le(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> Lit {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => {
                if if strict { const_term.is_negative() } else { const_term.is_negative() || const_term.is_zero() } {
                    self.sat_solver.true_lit()
                } else {
                    self.sat_solver.false_lit()
                }
            }
            1 => {
                let (var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) } / coeff);
                let bound = if coeff.is_positive() { TheoryConstraint::LraUb(*var, bound) } else { TheoryConstraint::LraLb(*var, bound) };
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.lra_theory.get_or_create_slack(vars);
                let bound = TheoryConstraint::LraUb(slack, InfRational::new(Rational::Finite(-const_term), if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) }));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn mk_arith_eq(&mut self, e1: &ArithExpr, e2: &ArithExpr) -> Lit {
        if e1 == e2 {
            return self.sat_solver.true_lit();
        }

        let le_lit = self.mk_le(e1, e2, false);
        let ge_lit = self.mk_ge(e1, e2, false);

        let proxy_var = self.sat_solver.mk_var();
        let p = Lit::new(proxy_var, false);

        // p -> (x <= y)
        self.sat_solver.add_clause([!p, le_lit]).expect("Failed to add clause");
        // p -> (x >= y)
        self.sat_solver.add_clause([!p, ge_lit]).expect("Failed to add clause");
        // (x <= y) ∧ (x >= y) -> p
        self.sat_solver.add_clause([!le_lit, !ge_lit, p]).expect("Failed to add clause");

        p
    }

    fn mk_ge(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> Lit {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => {
                if if strict { const_term.is_positive() } else { const_term.is_positive() || const_term.is_zero() } {
                    self.sat_solver.true_lit()
                } else {
                    self.sat_solver.false_lit()
                }
            }
            1 => {
                let (var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), if strict { rug::Rational::from(1) } else { rug::Rational::from(0) } / coeff);
                let bound = if coeff.is_positive() { TheoryConstraint::LraLb(*var, bound) } else { TheoryConstraint::LraUb(*var, bound) };
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.lra_theory.get_or_create_slack(vars);
                let bound = TheoryConstraint::LraLb(slack, InfRational::new(Rational::Finite(-const_term), if strict { rug::Rational::from(1) } else { rug::Rational::from(0) }));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn diff(&self, e1: &ArithExpr, e2: &ArithExpr) -> (SparseRow, rug::Rational) {
        let mut vars = SparseRow::new();
        let mut const_term = rug::Rational::from(0);

        let pos_one = rug::Rational::from(1);
        let neg_one = rug::Rational::from(-1);

        let mut temp = rug::Rational::new();

        self.accumulate_expr(e1, &pos_one, &mut vars, &mut const_term, &mut temp);
        self.accumulate_expr(e2, &neg_one, &mut vars, &mut const_term, &mut temp);

        vars.retain(|_, c| *c != 0);

        (vars, const_term)
    }

    fn accumulate_expr(&self, expr: &ArithExpr, scale: &rug::Rational, vars: &mut SparseRow, const_term: &mut rug::Rational, temp: &mut rug::Rational) {
        match expr {
            ArithExpr::Const(c) => {
                temp.assign(c * scale);
                *const_term += &*temp;
            }
            ArithExpr::IntVar(var) | ArithExpr::RealVar(var) => {
                self.accumulate_var(*var, scale, vars, temp);
            }
            ArithExpr::Add(terms) => {
                for term in terms {
                    self.accumulate_expr(term, scale, vars, const_term, temp);
                }
            }
            ArithExpr::Mul(terms) => {
                if terms.len() != 2 {
                    panic!("Only binary multiplication is supported in linear arithmetic");
                }
                let (first, second) = (&terms[0], &terms[1]);

                // Ricorsione intelligente: accettiamo (Costante * SottoEspressione)
                match (first, second) {
                    (ArithExpr::Const(c), sub_expr) | (sub_expr, ArithExpr::Const(c)) => {
                        let mut new_scale = rug::Rational::new();
                        new_scale.assign(c * scale);
                        self.accumulate_expr(sub_expr, &new_scale, vars, const_term, temp);
                    }
                    _ => {
                        panic!("Non-linear arithmetic: multiplication between two non-constant expressions is not supported");
                    }
                }
            }
            ArithExpr::Div(numerator, denominator) => {
                // Il denominatore DEVE essere una costante per preservare la linearità
                if let ArithExpr::Const(c) = &**denominator {
                    if c.is_zero() {
                        panic!("Division by zero detected in AST");
                    }
                    let mut div_scale = rug::Rational::new();
                    div_scale.assign(scale / c);
                    self.accumulate_expr(numerator, &div_scale, vars, const_term, temp);
                } else {
                    panic!("Non-linear arithmetic: division by a non-constant expression is not supported");
                }
            }
            ArithExpr::Neg(sub_expr) => {
                let mut neg_scale = rug::Rational::new();
                neg_scale.assign(scale * -1);
                self.accumulate_expr(sub_expr, &neg_scale, vars, const_term, temp);
            }
        }
    }

    fn accumulate_var(&self, var: usize, scale: &rug::Rational, vars: &mut SparseRow, temp: &mut rug::Rational) {
        if let Some(basic_row) = self.lra_theory.tableau.get(&var) {
            for (sub_var, sub_coeff) in basic_row.iter() {
                temp.assign(sub_coeff * scale);
                vars.add_coeff(*sub_var, temp);
            }
        } else {
            vars.add_coeff(var, scale);
        }
    }

    fn get_or_create_proxy(&mut self, constraint: TheoryConstraint) -> Lit {
        if let Some(&sat_var) = self.registry.get_proxy(&constraint) {
            sat_var
        } else {
            let sat_var = self.sat_solver.mk_var();
            self.registry.register(constraint, Lit::new(sat_var, false));
            Lit::new(sat_var, false)
        }
    }

    /// Adds a decision literal to the current search branch.
    pub fn decide(&mut self, lit: Lit) -> bool {
        self.sat_solver.push();
        self.lra_theory.push();
        self.enum_theory.push();
        self.sat_solver.enqueue_decision(lit)
    }

    /// Decides that an enum variable takes a specific value in the current branch.
    pub fn decide_enum(&mut self, expr: &EnumExpr, value: i32) -> bool {
        let eq_expr = TheoryConstraint::EnumEq(
            match expr {
                EnumExpr::Var(v) => *v,
                EnumExpr::Const(_) => panic!("Cannot decide on a constant value"),
            },
            value,
        );
        let lit = self.get_or_create_proxy(eq_expr);
        self.decide(lit)
    }

    /// Returns the current decision level of the solver.
    pub fn decision_level(&self) -> usize {
        self.sat_solver.decision_level()
    }

    /// Cancels all decisions and theory updates at levels deeper than `level`.
    pub fn cancel_until(&mut self, level: usize) {
        self.sat_solver.cancel_until(level);
        self.lra_theory.cancel_until(level);
        self.enum_theory.cancel_until(level);
        self.notified_len = self.sat_solver.trail.len();
    }

    /// Returns the trail suffix starting at `from_index`.
    pub fn get_trail_delta(&self, from_index: usize) -> &[Lit] {
        &self.sat_solver.trail[from_index..]
    }

    /// Returns the current size of the solver trail.
    pub fn current_trail_len(&self) -> usize {
        self.sat_solver.trail.len()
    }

    /// Returns the size of the solver trail at a specific decision level.
    pub fn get_trail_len_at_level(&self, level: usize) -> usize {
        if level < self.sat_solver.trail_lim.len() { self.sat_solver.trail_lim[level] } else { self.sat_solver.trail.len() }
    }

    /// Returns a slice of the solver trail between two indices.
    pub fn get_trail_slice(&self, start: usize, end: usize) -> &[Lit] {
        &self.sat_solver.trail[start..end]
    }

    /// Returns the number of user-defined scopes currently active in the solver.
    pub fn user_scopes_len(&self) -> usize {
        self.user_scopes.len()
    }

    pub fn propagate(&mut self) -> Result<(), (usize, Vec<Lit>)> {
        let base_level = self.user_scopes.last().map(|&(lvl, _)| lvl).unwrap_or(0);
        if let Err((bt_level, conflict)) = self.sat_solver.propagate() {
            return Err((bt_level.max(base_level), conflict));
        }

        while self.notified_len < self.sat_solver.trail.len() {
            let lit = self.sat_solver.trail[self.notified_len];

            if let Some(constraint) = self.registry.get_constraint(lit).or_else(|| self.registry.get_constraint(!lit)) {
                let theory_result = match (constraint, lit.sign()) {
                    (TheoryConstraint::LraUb(var, bound), false) => self.lra_theory.set_ub(Some(lit), *var, bound.clone()),
                    (TheoryConstraint::LraLb(var, bound), true) => self.lra_theory.set_ub(Some(lit), *var, InfRational::new(bound.rational_part().clone(), if bound.infinitesimal_part().is_positive() { rug::Rational::from(0) } else { rug::Rational::from(-1) })),
                    (TheoryConstraint::LraLb(var, bound), false) => self.lra_theory.set_lb(Some(lit), *var, bound.clone()),
                    (TheoryConstraint::LraUb(var, bound), true) => self.lra_theory.set_lb(Some(lit), *var, InfRational::new(bound.rational_part().clone(), if bound.infinitesimal_part().is_negative() { rug::Rational::from(0) } else { rug::Rational::from(1) })),
                    (TheoryConstraint::EnumEq(var, val), false) => self.enum_theory.set_eq(Some(lit), *var, *val),
                    (TheoryConstraint::EnumEq(var, val), true) => self.enum_theory.set_neq(Some(lit), *var, *val),
                };

                if let Err(lemma) = theory_result {
                    return Err((self.compute_backtrack_level(&lemma, base_level), lemma));
                }
            }
            self.notified_len += 1;
        }

        if let Err(conflict) = self.lra_theory.check() {
            return Err((self.compute_backtrack_level(&conflict, base_level), conflict));
        }
        Ok(())
    }

    /// Returns the assigned value of a Boolean expression when it is fully determined.
    pub fn get_bool_val(&self, expr: &BoolExpr) -> Option<bool> {
        match expr {
            BoolExpr::True => Some(true),
            BoolExpr::False => Some(false),
            BoolExpr::Var(v) => *self.sat_solver.value(*v),
            BoolExpr::Not(inner) => self.get_bool_val(inner).map(|val| !val),
            BoolExpr::And(args) => {
                let mut result = Some(true);
                for arg in args {
                    match self.get_bool_val(arg) {
                        Some(val) => {
                            if !val {
                                return Some(false);
                            }
                        }
                        None => result = None,
                    }
                }
                result
            }
            BoolExpr::Or(args) => {
                let mut result = Some(false);
                for arg in args {
                    match self.get_bool_val(arg) {
                        Some(val) => {
                            if val {
                                return Some(true);
                            }
                        }
                        None => result = None,
                    }
                }
                result
            }
            _ => None,
        }
    }

    /// Returns the current value of an arithmetic expression when it is fixed by the model.
    pub fn get_arith_val(&self, expr: &ArithExpr) -> Option<InfRational> {
        match expr {
            ArithExpr::Const(c) => Some(InfRational::new(Rational::Finite(c.clone()), rug::Rational::from(0))),
            ArithExpr::RealVar(v) | ArithExpr::IntVar(v) => Some(self.lra_theory.value(*v).clone()),
            ArithExpr::Add(terms) => {
                let mut sum = InfRational::new(Rational::Finite(rug::Rational::from(0)), rug::Rational::from(0));
                for term in terms {
                    {
                        sum += self.get_arith_val(term)?;
                    }
                }
                Some(sum)
            }
            ArithExpr::Neg(term) => self.get_arith_val(term).map(|val| -val),
            _ => None,
        }
    }

    /// Returns the concrete value of an enum variable if it has been fully assigned.
    pub fn get_enum_val(&self, expr: &EnumExpr) -> Option<i32> {
        match expr {
            EnumExpr::Const(c) => Some(*c),
            EnumExpr::Var(v) => {
                let domain = &self.enum_theory.active_domains[*v];
                if domain.len() == 1 { domain.iter().next().copied() } else { None }
            }
        }
    }

    /// Opens a new incremental scope for assertions and decisions.
    pub fn push(&mut self) {
        let clauses_len = self.sat_solver.clauses.len();

        self.sat_solver.push();
        self.lra_theory.push();
        self.enum_theory.push();

        let current_level = self.sat_solver.decision_level();
        self.user_scopes.push((current_level, clauses_len));
    }

    /// Restores the previous solver scope and discards all assertions added since it was opened.
    pub fn pop(&mut self) {
        if let Some((saved_level, saved_clauses_len)) = self.user_scopes.pop() {
            let target_level = saved_level - 1;
            self.sat_solver.cancel_until(target_level);
            self.lra_theory.cancel_until(target_level);
            self.enum_theory.cancel_until(target_level);
            self.notified_len = self.sat_solver.trail.len();

            for watch_list in self.sat_solver.watches.iter_mut() {
                watch_list.retain(|&clause_idx| clause_idx < saved_clauses_len);
            }
            self.sat_solver.clauses.truncate(saved_clauses_len);
        }
    }

    fn compute_backtrack_level(&self, lemma: &[Lit], root_level: usize) -> usize {
        if lemma.len() <= 1 {
            return root_level;
        }

        let mut levels: Vec<usize> = lemma.iter().map(|lit| self.sat_solver.level(lit.var()).expect("literal should have a decision level")).collect();

        levels.sort_unstable_by(|a, b| b.cmp(a));

        let max_level = levels[0];

        if max_level <= root_level {
            return root_level;
        }

        if levels.iter().filter(|&&l| l == max_level).count() == 1 { levels[1].max(root_level) } else { (max_level - 1).max(root_level) }
    }

    pub fn check_ints(&mut self) -> Result<(), (usize, Vec<Lit>)> {
        if let Err((var, frac_val)) = self.lra_theory.check_ints() {
            let base_level = self.user_scopes.last().map(|&(lvl, _)| lvl).unwrap_or(0);
            if let Some((cut_row, f0)) = self.lra_theory.generate_gomory_cut(var) {
                let cut_slack = self.lra_theory.get_or_create_slack(cut_row);
                let bound = InfRational::new(Rational::Finite(f0), rug::Rational::from(0));
                let cut_lit = self.get_or_create_proxy(TheoryConstraint::LraLb(cut_slack, bound));

                let lemma = vec![cut_lit];
                let base_level = self.user_scopes.last().map(|&(lvl, _)| lvl).unwrap_or(0);
                return Err((base_level, lemma));
            }

            let Rational::Finite(inner_frac) = frac_val else {
                unreachable!("Fractional variable in Branch & Bound must be finite");
            };

            let mut floor_val = inner_frac.clone();
            floor_val.floor_mut();
            let mut ceil_val = inner_frac.clone();
            ceil_val.ceil_mut();

            let ub = InfRational::new(Rational::Finite(floor_val), rug::Rational::from(0));
            let lb = InfRational::new(Rational::Finite(ceil_val), rug::Rational::from(0));

            let lit_ub = self.get_or_create_proxy(TheoryConstraint::LraUb(var, ub));
            let lit_lb = self.get_or_create_proxy(TheoryConstraint::LraLb(var, lb));

            let lemma = vec![lit_ub, lit_lb];
            return Err((base_level, lemma));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{add, and, cst_arith, cst_enum, eq_arith, eq_enum, ge, gt, le, lt, or};

    #[test]
    fn test_pure_sat_resolution() {
        let mut solver = SmtSolver::new();

        let a = solver.new_bool();
        let b = solver.new_bool();
        let c = solver.new_bool();

        // (A ∨ B) ∧ (¬B ∨ C) ∧ (¬B ∨ ¬C) ∧ (¬A)
        // With ¬A, clause (A ∨ B) forces B; then B forces both C and ¬C.
        let expr = and([or([a.clone(), b.clone()]), or([!b.clone(), c.clone()]), or([!b, !c]), !a]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_early_bounding_unsat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        // x > 10 ∧ x < 5
        let expr = and([gt(x.clone(), cst_arith(10)), lt(x, cst_arith(5))]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_equality_mutually_exclusive() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        // x == 5 ∧ x > 6
        let expr = and([eq_arith(x.clone(), cst_arith(5)), gt(x, cst_arith(6))]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_simplex_system_unsat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();
        let y = solver.new_real();

        // x + y == 10
        let eq_expr = eq_arith(add([x.clone(), y.clone()]), cst_arith(10));
        // x > 6
        let gt_x = gt(x.clone(), cst_arith(6));
        // y > 6
        let gt_y = gt(y.clone(), cst_arith(6));

        let expr = and([eq_expr, gt_x, gt_y]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_constant_arithmetic_evaluations() {
        let mut solver = SmtSolver::new();

        assert!(solver.assert(&lt(cst_arith(5), cst_arith(10))).is_ok());
        assert!(solver.assert(&le(cst_arith(5), cst_arith(5))).is_ok());
        assert!(solver.assert(&ge(cst_arith(10), cst_arith(5))).is_ok());
        assert!(solver.assert(&gt(cst_arith(10), cst_arith(5))).is_ok());

        assert!(solver.assert(&lt(cst_arith(10), cst_arith(5))).is_err());
        assert!(solver.assert(&le(cst_arith(10), cst_arith(5))).is_err());
        assert!(solver.assert(&ge(cst_arith(5), cst_arith(10))).is_err());
        assert!(solver.assert(&gt(cst_arith(5), cst_arith(10))).is_err());

        assert!(solver.assert(&!lt(cst_arith(10), cst_arith(5))).is_ok());
        assert!(solver.assert(&!lt(cst_arith(5), cst_arith(10))).is_err());
    }

    #[test]
    fn test_negated_variable_inequalities() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        solver.push();
        assert!(solver.assert(&!lt(x.clone(), cst_arith(5))).is_ok());
        assert!(solver.assert(&lt(x.clone(), cst_arith(4))).is_err());
        solver.pop();

        solver.push();
        assert!(solver.assert(&!le(x.clone(), cst_arith(5))).is_ok());
        assert!(solver.assert(&le(x.clone(), cst_arith(5))).is_err());
        solver.pop();

        solver.push();
        assert!(solver.assert(&!ge(x.clone(), cst_arith(5))).is_ok());
        assert!(solver.assert(&ge(x.clone(), cst_arith(5))).is_err());
        solver.pop();

        solver.push();
        assert!(solver.assert(&!gt(x.clone(), cst_arith(5))).is_ok());
        assert!(solver.assert(&gt(x.clone(), cst_arith(5))).is_err());
        solver.pop();
    }

    #[test]
    #[should_panic(expected = "Type mismatch in Eq")]
    fn test_encode_eq_type_mismatch_panic() {
        let mut solver = SmtSolver::new();
        let a = solver.new_bool();
        let x = solver.new_real();

        let bad_eq = BoolExpr::Eq(Box::new(Expr::Bool(a)), Box::new(Expr::Arith(x)));

        let _ = solver.assert(&bad_eq);
    }

    #[test]
    fn test_enum_out_of_domain_unsat() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2]);

        let expr = eq_enum(e, cst_enum(3));

        let result = solver.assert(&expr);
        assert!(result.is_err(), "The solver should detect that the enum variable cannot take a value outside its domain");
    }

    #[test]
    fn test_enum_exhaustive_denial_integration() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2]);

        // (e != 1) AND (e != 2)
        let expr = and(vec![!(eq_enum(e.clone(), cst_enum(1))), !(eq_enum(e, cst_enum(2)))]);

        assert!(solver.assert(&expr).is_err());
    }
}
