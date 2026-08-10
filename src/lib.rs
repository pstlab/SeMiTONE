pub mod ast;
mod enum_theory;
mod lra_theory;
#[cfg(feature = "parser")]
pub mod parser;
mod proxy;
mod rational;
mod sat_solver;

use crate::{
    ast::{ArithExpr, BoolExpr, EnumExpr, Expr},
    enum_theory::EnumTheory,
    lra_theory::{LraTheory, SparseRow},
    proxy::{ProxyRegistry, TheoryConstraint},
    rational::{InfRational, Rational},
    sat_solver::{Lit, SatSolver},
};
use rug::Assign;

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

    pub fn new_bool(&mut self) -> BoolExpr {
        BoolExpr::Var(self.sat_solver.mk_var())
    }

    pub fn new_int(&mut self) -> ArithExpr {
        ArithExpr::IntVar(self.lra_theory.mk_int())
    }

    pub fn new_real(&mut self) -> ArithExpr {
        ArithExpr::RealVar(self.lra_theory.mk_real())
    }

    pub fn new_enum(&mut self, domain: impl IntoIterator<Item = i32>) -> EnumExpr {
        EnumExpr::Var(self.enum_theory.mk_var(domain.into_iter().collect()))
    }

    pub fn assert(&mut self, expr: &BoolExpr) -> Result<(), (usize, Vec<BoolExpr>)> {
        if !self.assert_internal(expr, true) {
            return Err((self.user_scopes.len(), vec![BoolExpr::False]));
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

    fn build_conflict(lemma: Vec<Lit>) -> Vec<BoolExpr> {
        lemma
            .into_iter()
            .map(|lit| {
                let var = BoolExpr::Var(lit.var());
                if lit.sign() { BoolExpr::Not(Box::new(var)) } else { var }
            })
            .collect()
    }

    pub fn decide(&mut self, lit: Lit) -> Result<(), (usize, Vec<BoolExpr>)> {
        self.sat_solver.push();
        self.lra_theory.push();
        self.enum_theory.push();
        if !self.sat_solver.enqueue_decision(lit) {
            return Err((self.user_scopes.len(), vec![BoolExpr::False]));
        }
        self.propagate()
    }

    pub fn cancel_until(&mut self, level: usize) {
        self.sat_solver.cancel_until(level);
        self.lra_theory.cancel_until(level);
        self.enum_theory.cancel_until(level);
        self.notified_len = self.sat_solver.trail.len();
    }

    fn propagate(&mut self) -> Result<(), (usize, Vec<BoolExpr>)> {
        if let Err((bt_level, conflict)) = self.sat_solver.propagate() {
            return Err((bt_level, Self::build_conflict(conflict)));
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
                    return Err((self.compute_backtrack_level(&lemma, self.user_scopes.len()), Self::build_conflict(lemma)));
                }
            }
            self.notified_len += 1;
        }

        if let Err(conflict) = self.lra_theory.check() {
            return Err((self.compute_backtrack_level(&conflict, self.user_scopes.len()), Self::build_conflict(conflict)));
        }
        Ok(())
    }

    pub fn get_bool_val(&self, expr: &BoolExpr) -> Option<bool> {
        match expr {
            BoolExpr::True => Some(true),
            BoolExpr::False => Some(false),
            BoolExpr::Var(v) => *self.sat_solver.value(*v),
            _ => None,
        }
    }

    pub fn get_arith_val(&self, expr: &ArithExpr) -> Option<InfRational> {
        match expr {
            ArithExpr::Const(c) => Some(InfRational::new(Rational::Finite(c.clone()), rug::Rational::from(0))),
            ArithExpr::RealVar(v) | ArithExpr::IntVar(v) => Some(self.lra_theory.value(*v).clone()),
            _ => None,
        }
    }

    pub fn get_enum_val(&self, expr: &EnumExpr) -> Option<i32> {
        match expr {
            EnumExpr::Const(c) => Some(*c),
            EnumExpr::Var(v) => {
                let domain = &self.enum_theory.active_domains[*v];
                if domain.len() == 1 { domain.iter().next().copied() } else { None }
            }
        }
    }

    pub fn push(&mut self) {
        let clauses_len = self.sat_solver.clauses.len();

        self.sat_solver.push();
        self.lra_theory.push();
        self.enum_theory.push();

        let current_level = self.sat_solver.decision_level();
        self.user_scopes.push((current_level, clauses_len));
    }

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

    /// Explores the search space to find a valid model or prove UNSAT.
    pub fn check_sat(&mut self) -> bool {
        let root_level = self.user_scopes.len();

        loop {
            // 1. PROPAGATION PHASE
            // Process the trail until exhausted. If a conflict occurs, resolve it and loop back
            // to propagate the newly learned clause immediately.
            if let Err((bt_level, lemma)) = self.propagate() {
                if self.sat_solver.decision_level() <= root_level {
                    return false;
                }

                self.cancel_until(bt_level);

                let mut learned_clause = Vec::with_capacity(lemma.len());
                for expr in lemma {
                    learned_clause.push(self.encode_bool(&expr));
                }

                if self.sat_solver.add_clause(learned_clause).is_err() {
                    return false;
                }

                // Crucial: loop back to propagate the learned unit clause BEFORE making any decisions
                continue;
            }

            // 2. CHECK UNASSIGNED VARIABLES
            let mut unassigned_var = None;
            for i in 0..self.sat_solver.assigns.len() {
                if self.sat_solver.value(i).is_none() {
                    unassigned_var = Some(i);
                    break;
                }
            }

            // 3. DECISION OR THEORY LATE-CHECK PHASE
            if let Some(var) = unassigned_var {
                // The trail is completely flushed, safe to guess
                self.sat_solver.push();
                self.lra_theory.push();
                self.enum_theory.push();
                if !self.sat_solver.enqueue_decision(Lit::new(var, false)) {
                    unreachable!()
                }
            } else {
                // All variables assigned, evaluate late theory checks (e.g., integers)
                if let Err((var, frac_val)) = self.lra_theory.check_ints() {
                    // --- GOMORY CUTS ---
                    if let Some((cut_row, f0)) = self.lra_theory.generate_gomory_cut(var) {
                        let cut_slack = self.lra_theory.get_or_create_slack(cut_row);
                        let bound = InfRational::new(Rational::Finite(f0), rug::Rational::from(0));
                        let cut_lit = self.get_or_create_proxy(TheoryConstraint::LraLb(cut_slack, bound));

                        self.cancel_until(root_level);

                        if self.sat_solver.add_clause([cut_lit]).is_err() {
                            return false;
                        }

                        continue;
                    }

                    // --- BRANCH & BOUND ---
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

                    self.cancel_until(root_level);

                    if self.sat_solver.add_clause([lit_ub, lit_lb]).is_err() {
                        return false;
                    }
                    continue;
                }

                // No unassigned variables and no theory violations
                return true;
            }
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{add, and, cst_arith, cst_enum, cst_frac, eq_arith, eq_enum, ge, gt, le, lt, min, mul, or};

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
    fn test_simplex_system_sat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();
        let y = solver.new_real();
        let z = solver.new_real();

        // 2x - y + z == 10
        let exp1 = add([mul([cst_arith(2), x.clone()]), mul([cst_arith(-1), y.clone()]), z.clone()]);
        let eq1 = eq_arith(exp1, cst_arith(10));

        // x > 0, y > 0, z > 0
        let bnd = and([gt(x.clone(), cst_arith(0)), gt(y.clone(), cst_arith(0)), gt(z.clone(), cst_arith(0))]);

        let result = solver.assert(&and([eq1, bnd]));
        assert!(result.is_ok());

        // Triggers the search loop to assign values to the slack variables
        assert!(solver.check_sat(), "The system has valid real solutions and should be SAT");
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
    fn test_tseitin_nested_boolean_logic() {
        let mut solver = SmtSolver::new();
        let a = solver.new_bool();
        let b = solver.new_bool();

        let nested_and = and([a.clone(), b.clone()]);
        let nested_or = or([!a.clone(), BoolExpr::False]);

        let root_or = or([nested_and, nested_or, BoolExpr::True]);

        assert!(solver.assert(&root_or).is_ok());
        assert!(solver.check_sat());
    }

    #[test]
    fn test_tseitin_nested_theory_atoms() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        let atom_lt = lt(x.clone(), cst_arith(5));
        let atom_ge = ge(x.clone(), cst_arith(10));
        let atom_le = le(x.clone(), cst_arith(0));
        let atom_gt = gt(x.clone(), cst_arith(20));

        let disjunction1 = or([atom_lt, atom_ge]);
        let disjunction2 = or([atom_le, atom_gt]);

        assert!(solver.assert(&disjunction1).is_ok());
        assert!(solver.assert(&disjunction2).is_ok());
        assert!(solver.check_sat());
    }

    #[test]
    fn test_encode_eq_booleans() {
        let mut solver = SmtSolver::new();
        let a = solver.new_bool();
        let b = solver.new_bool();

        let eq_expr = BoolExpr::Eq(Box::new(Expr::Bool(a.clone())), Box::new(Expr::Bool(b.clone())));

        assert!(solver.assert(&and([eq_expr, a])).is_ok());
        assert!(solver.check_sat());

        assert_eq!(solver.get_bool_val(&b), Some(true));
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
    fn test_dpllt_backtracking_over_theory() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        // (x < 0 ∨ x > 10) ∧ (x > 5) ∧ (x < 15)
        let expr = and([or([lt(x.clone(), cst_arith(0)), gt(x.clone(), cst_arith(10))]), gt(x.clone(), cst_arith(5)), lt(x.clone(), cst_arith(15))]);

        let result = solver.assert(&expr);
        assert!(result.is_ok());

        solver.propagate().expect("Initial propagation should succeed");

        // check_sat will guess (x < 0), the theory will reject it against (x > 5),
        // the solver will learn the lemma, backtrack, and pick (x > 10) instead.
        assert!(solver.check_sat(), "Solver must backtrack from the x < 0 branch and find the SAT path");
    }

    #[test]
    fn test_dpllt_negated_equality_branching() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();
        let y = solver.new_real();

        let not_eq = !eq_arith(x.clone(), y.clone());

        let force_lt = and([lt(x.clone(), cst_arith(10)), gt(y.clone(), cst_arith(20))]);

        let expr = and([not_eq, force_lt]);

        let result = solver.assert(&expr);
        assert!(result.is_ok());

        // The solver will branch on the disjunction, fail one path due to LRA bounds,
        // and backtrack to validate the other.
        assert!(solver.check_sat(), "Solver must resolve negated equality branching correctly");
    }

    #[test]
    fn test_enum_basic_sat() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2, 3]);

        let expr = eq_enum(e, cst_enum(2));

        assert!(solver.assert(&expr).is_ok());
        assert!(solver.check_sat(), "The solver should find a valid assignment for the enum variable");
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

    #[test]
    fn test_enum_var_to_var_equality() {
        let mut solver = SmtSolver::new();
        let e1 = solver.new_enum(vec![1, 2, 3]);
        let e2 = solver.new_enum(vec![3, 4, 5]);

        let eq_expr = eq_enum(e1.clone(), e2.clone());

        assert!(solver.assert(&eq_expr).is_ok());
        assert!(solver.check_sat(), "Solver should find a valid assignment for e1 and e2 where they are equal (SAT)");

        let not_3 = !(eq_enum(e1.clone(), cst_enum(3)));
        assert!(solver.assert(&not_3).is_err());
    }

    #[test]
    fn test_enum_dpllt_branching() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2, 3]);

        let expr = and([or([eq_enum(e.clone(), cst_enum(1)), eq_enum(e.clone(), cst_enum(2))]), !(eq_enum(e.clone(), cst_enum(1)))]);

        assert!(solver.assert(&expr).is_ok());

        assert!(solver.check_sat(), "Solver should backtrack and explore e == 2 (SAT)");
    }

    #[test]
    fn test_integer_branch_and_bound_unsat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_int();

        let eq_expr = eq_arith(mul([cst_arith(2), x.clone()]), cst_arith(3));

        assert!(solver.assert(&eq_expr).is_ok());

        assert!(!solver.check_sat(), "There is no integer solution to 2x = 3, should be UNSAT");
    }

    #[test]
    fn test_integer_branch_and_bound_sat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_int();

        let expr = and([gt(x.clone(), cst_frac(12, 10)), lt(x.clone(), cst_frac(28, 10))]);

        assert!(solver.assert(&expr).is_ok());

        assert!(solver.check_sat(), "There is an integer solution to the constraints, should be SAT");
    }

    #[test]
    fn test_min_constraint_sat_and_model_extraction() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();
        let y = solver.new_real();
        let z = solver.new_real();

        // x = 15, y = 10
        let eq_x = eq_arith(x.clone(), cst_arith(15));
        let eq_y = eq_arith(y.clone(), cst_arith(10));

        // z = min(x, y)
        let min_expr = min(z.clone(), [x.clone(), y.clone()]);

        let expr = and([eq_x, eq_y, min_expr]);
        assert!(solver.assert(&expr).is_ok());

        // DPLL(T) should resolve this and guess z = 10
        assert!(solver.check_sat(), "The min constraint must be SAT");

        // Verify the extracted model
        assert_eq!(solver.get_arith_val(&z), Some(InfRational::new(Rational::Finite(rug::Rational::from(10)), rug::Rational::from(0))), "The min constraint should resolve to z = 10");
    }

    #[test]
    fn test_push_pop_incremental_scopes() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        // x >= 10
        assert!(solver.assert(&ge(x.clone(), cst_arith(10))).is_ok());
        assert!(solver.check_sat(), "x >= 10 is SAT");

        solver.push();
        // x <= 20
        assert!(solver.assert(&le(x.clone(), cst_arith(20))).is_ok());
        assert!(solver.check_sat(), "x >= 10 and x <= 20 is SAT");

        solver.push();
        // x <= 5
        assert!(solver.assert(&le(x.clone(), cst_arith(5))).is_err(), "x >= 10 and x <= 5 is UNSAT");

        solver.pop();
        assert!(solver.check_sat(), "x >= 10 and x <= 20 is SAT after popping the last scope");

        let val = solver.get_arith_val(&x).unwrap();
        assert!(val >= InfRational::new(Rational::Finite(rug::Rational::from(10)), rug::Rational::from(0)));
        assert!(val <= InfRational::new(Rational::Finite(rug::Rational::from(20)), rug::Rational::from(0)));

        solver.pop();
        assert!(solver.assert(&ge(x.clone(), cst_arith(50))).is_ok());
        assert!(solver.check_sat(), "x >= 50 is SAT after popping all scopes");
    }

    #[test]
    fn test_gomory_cut_generation_unsat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_int();
        let y = solver.new_int();

        let eq_expr = eq_arith(add([mul([cst_arith(3), x.clone()]), mul([cst_arith(3), y.clone()])]), cst_arith(10));

        // Gomory cuts require variables to be bounded to effectively prune.
        // Without bounds, the cut becomes a tautology, leading to stagnation.
        let bounds = and([ge(x.clone(), cst_arith(0)), ge(y.clone(), cst_arith(0))]);

        assert!(solver.assert(&and([eq_expr, bounds])).is_ok());

        assert!(!solver.check_sat(), "3x + 3y = 10 has no integer solutions, must be UNSAT");
    }

    #[test]
    fn test_gomory_cut_generation_sat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_int();
        let y = solver.new_int();

        // 3x + 4y = 10, with x >= 0 and y >= 0
        let eq_expr = eq_arith(add([mul([cst_arith(3), x.clone()]), mul([cst_arith(4), y.clone()])]), cst_arith(10));

        let bounds = and([ge(x.clone(), cst_arith(0)), ge(y.clone(), cst_arith(0))]);

        assert!(solver.assert(&and([eq_expr, bounds])).is_ok());

        assert!(solver.check_sat(), "Il sistema ha una soluzione intera e deve essere SAT");

        let val_x = solver.get_arith_val(&x).expect("x deve avere un valore");
        let val_y = solver.get_arith_val(&y).expect("y deve avere un valore");

        assert_eq!(val_x.rational_part().clone(), Rational::Finite(rug::Rational::from(2)));
        assert_eq!(val_y.rational_part().clone(), Rational::Finite(rug::Rational::from(1)));
    }
}
