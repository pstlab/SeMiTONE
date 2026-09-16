#![doc = include_str!("../README.md")]

//! # API overview
//!
//! [`SeMiTONE`] owns all solver state. Create expressions with the types in
//! [`ast`], assert a [`ast::BoolExpr`], then call [`SeMiTONE::propagate`] after
//! each assertion or decision. Applications that need a complete SAT/SMT search
//! loop can use the decision, trail, and clause APIs exposed by [`SeMiTONE`].

pub mod ast;
mod dl_theory;
mod enum_theory;
mod euf_theory;
mod lra_theory;
#[cfg(feature = "parser")]
pub mod parser;
mod proxy;
pub mod rational;
mod sat_solver;
#[cfg(feature = "solver")]
pub mod solver;

use crate::{
    ast::{ArithExpr, BoolExpr, EnumExpr, EufExpr, Expr},
    dl_theory::DlTheory,
    enum_theory::EnumTheory,
    euf_theory::{EufTheory, Term},
    lra_theory::{LraTheory, SparseRow},
    proxy::{ProxyRegistry, TheoryConstraint},
    rational::{InfRational, Rational},
    sat_solver::SatSolver,
};
use rug::Assign;
pub use sat_solver::Lit;
use tracing::{debug, trace};

/// Main solver entry point for propositional, linear arithmetic, and enum constraints.
///
/// The solver combines a SAT core with theory propagation for linear rational
/// arithmetic and finite-domain enum reasoning.
pub struct SeMiTONE {
    registry: ProxyRegistry,
    sat_solver: SatSolver,
    lra_theory: LraTheory,
    enum_theory: EnumTheory,
    dl_theory: DlTheory,
    euf_theory: EufTheory,
    notified_len: usize,
    user_scopes: Vec<(usize, usize)>,
}

impl Default for SeMiTONE {
    fn default() -> Self {
        Self::new()
    }
}

impl SeMiTONE {
    /// Creates a new empty solver instance.
    pub fn new() -> Self {
        Self {
            registry: ProxyRegistry::new(),
            sat_solver: SatSolver::new(),
            lra_theory: LraTheory::new(),
            enum_theory: EnumTheory::new(),
            dl_theory: DlTheory::new(),
            euf_theory: EufTheory::new(),
            notified_len: 0,
            user_scopes: Vec::new(),
        }
    }

    /// Allocates a new SAT literal.
    pub fn new_lit(&mut self) -> Lit {
        Lit::new(self.sat_solver.mk_var(), false)
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

    /// Allocates a new time point variable for difference logic constraints.
    pub fn new_time_point(&mut self) -> usize {
        self.dl_theory.new_var()
    }

    /// Allocates a new EUF variable.
    pub fn new_euf_var(&mut self) -> EufExpr {
        EufExpr::Var(self.euf_theory.add_term(Term::Var(self.euf_theory.terms.len())))
    }

    /// Allocates a new EUF function application with the given function ID and arguments.
    pub fn new_euf_app(&mut self, func_id: usize, args: Vec<Expr>) -> EufExpr {
        let mut internal_args = Vec::with_capacity(args.len());
        for arg in &args {
            if let Expr::Euf(euf_arg) = arg {
                let arg_id = match euf_arg {
                    EufExpr::Var(n) => *n,
                    EufExpr::App(internal_id, _) => *internal_id,
                };
                internal_args.push(arg_id);
            } else {
                panic!("EUF application arguments must be EUF expressions, but got: {:?}", arg);
            }
        }

        let id = self.euf_theory.add_term(Term::App(func_id, internal_args));
        EufExpr::App(id, args)
    }

    /// Returns the current number of SAT variables allocated in the solver core.
    ///
    /// This includes user-visible Boolean variables and internal proxy variables
    /// introduced while encoding compound constraints.
    pub fn num_vars(&self) -> usize {
        self.sat_solver.num_vars()
    }

    /// Adds a clause directly to the SAT core.
    ///
    /// Returns `Ok(())` when the clause is accepted, or `Err(conflict_clause)` if
    /// the clause is immediately contradictory at the current root context.
    ///
    /// This is useful for integrating external search/learning loops that produce
    /// learned no-goods.
    pub fn add_clause(&mut self, clause: impl IntoIterator<Item = Lit>) -> Result<(), Vec<Lit>> {
        self.sat_solver.add_clause(clause)
    }

    /// Adds a Boolean constraint to the current solver context.
    ///
    /// Returns `true` if the assertion was successfully added, or `false` if it
    /// led to an immediate, trivial conflict while translating/asserting.
    ///
    /// Note that `true` does not imply global feasibility: call [`SeMiTONE::propagate`]
    /// to detect conflicts that emerge after propagation through SAT/theory state.
    pub fn assert(&mut self, expr: impl AsRef<BoolExpr>) -> bool {
        self.assert_internal(expr.as_ref(), true)
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

                let bound = InfRational::new(Rational::Finite(-const_term), eps_val);

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
                        let bound = InfRational::new(Rational::Finite(-const_term), rug::Rational::from(0));

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

    /// Encodes a Boolean expression and returns its equivalent SAT literal.
    ///
    /// The returned literal may refer to an internal proxy variable. Encoding
    /// a compound expression can therefore add auxiliary variables and
    /// clauses to the solver. The literal preserves the expression's polarity
    /// and can be inspected with [`SeMiTONE::get_lit_val`] or used with
    /// [`SeMiTONE::decide`]. This method does not assert the expression.
    pub fn track_expr(&mut self, expr: impl AsRef<BoolExpr>) -> Lit {
        self.encode_bool(expr.as_ref())
    }

    fn encode_bool(&mut self, expr: &BoolExpr) -> Lit {
        match expr {
            BoolExpr::True => Lit::TRUE,
            BoolExpr::False => Lit::FALSE,
            BoolExpr::Var(v) => Lit::new(*v, false),
            BoolExpr::Not(inner) => match inner.as_ref() {
                BoolExpr::Lt(a1, a2) => self.mk_ge(a1, a2, false),
                BoolExpr::Le(a1, a2) => self.mk_ge(a1, a2, true),
                BoolExpr::Ge(a1, a2) => self.mk_le(a1, a2, true),
                BoolExpr::Gt(a1, a2) => self.mk_le(a1, a2, false),
                BoolExpr::DlLt(f, t, b) => self.mk_dl_ge(*f, *t, b.clone(), false), // !(x < y) => x >= y
                BoolExpr::DlLe(f, t, b) => self.mk_dl_ge(*f, *t, b.clone(), true),  // !(x <= y) => x > y
                BoolExpr::DlGe(f, t, b) => self.mk_dl_le(*f, *t, b.clone(), true),  // !(x >= y) => x < y
                BoolExpr::DlGt(f, t, b) => self.mk_dl_le(*f, *t, b.clone(), false), // !(x > y) => x <= y
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
            BoolExpr::DlLt(from, to, b) => self.mk_dl_le(*from, *to, b.clone(), true),
            BoolExpr::DlLe(from, to, b) => self.mk_dl_le(*from, *to, b.clone(), false),
            BoolExpr::DlGt(from, to, b) => self.mk_dl_ge(*from, *to, b.clone(), true),
            BoolExpr::DlGe(from, to, b) => self.mk_dl_ge(*from, *to, b.clone(), false),
            BoolExpr::DlEq(from, to, b) => self.mk_dl_eq(*from, *to, b.clone()),
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
            (Expr::Euf(u1), Expr::Euf(u2)) => {
                let id1 = match u1 {
                    crate::ast::EufExpr::Var(n) => *n,
                    crate::ast::EufExpr::App(n, _) => *n,
                };
                let id2 = match u2 {
                    crate::ast::EufExpr::Var(n) => *n,
                    crate::ast::EufExpr::App(n, _) => *n,
                };

                if id1 == id2 {
                    return Lit::TRUE;
                }

                let (min_id, max_id) = if id1 < id2 { (id1, id2) } else { (id2, id1) };

                self.get_or_create_proxy(TheoryConstraint::EufEq(min_id, max_id))
            }
            _ => panic!("Type mismatch in Eq: cannot compare different domains.\nLeft: {:?}\nRight: {:?}", expr1, expr2),
        }
    }

    fn mk_enum_eq(&mut self, e1: &EnumExpr, e2: &EnumExpr) -> Lit {
        match (e1, e2) {
            (EnumExpr::Const(c1), EnumExpr::Const(c2)) => {
                if c1 == c2 {
                    Lit::TRUE
                } else {
                    Lit::FALSE
                }
            }
            (EnumExpr::Var(v), EnumExpr::Const(c)) | (EnumExpr::Const(c), EnumExpr::Var(v)) => self.get_or_create_proxy(TheoryConstraint::EnumEq(*v, *c)),
            (EnumExpr::Var(v1), EnumExpr::Var(v2)) => {
                if v1 == v2 {
                    return Lit::TRUE;
                }

                let domain1 = self.enum_theory.initial_domains[*v1].clone();
                let domain2 = self.enum_theory.initial_domains[*v2].clone();
                let common: Vec<i32> = domain1.intersection(&domain2).copied().collect();

                if common.is_empty() {
                    return Lit::FALSE;
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
                    Lit::TRUE
                } else {
                    Lit::FALSE
                }
            }
            1 => {
                let (var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term / coeff), if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) } / coeff);
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
            return Lit::TRUE;
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
                    Lit::TRUE
                } else {
                    Lit::FALSE
                }
            }
            1 => {
                let (var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term / coeff), if strict { rug::Rational::from(1) } else { rug::Rational::from(0) } / coeff);
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

    fn mk_dl_le(&mut self, from: usize, to: usize, bound: rug::Rational, strict: bool) -> Lit {
        let delta = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
        let inf_bound = InfRational::new(Rational::Finite(bound), delta);

        let constraint = TheoryConstraint::DlLeq(from, to, inf_bound);
        self.get_or_create_proxy(constraint)
    }

    fn mk_dl_ge(&mut self, from: usize, to: usize, bound: rug::Rational, strict: bool) -> Lit {
        self.mk_dl_le(to, from, -bound, strict)
    }

    fn mk_dl_eq(&mut self, from: usize, to: usize, bound: rug::Rational) -> Lit {
        let le_lit = self.mk_dl_le(from, to, bound.clone(), false);
        let ge_lit = self.mk_dl_ge(from, to, bound, false);

        let proxy_var = self.sat_solver.mk_var();
        let p = Lit::new(proxy_var, false);

        self.sat_solver.add_clause([!p, le_lit]).expect("Failed to add clause");
        self.sat_solver.add_clause([!p, ge_lit]).expect("Failed to add clause");
        self.sat_solver.add_clause([!le_lit, !ge_lit, p]).expect("Failed to add clause");

        p
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

                // Smart recursion: accept (Constant * SubExpression)
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
                // The denominator MUST be a constant to preserve linearity
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
    ///
    /// This opens a new internal decision level and enqueues `lit` as a decision.
    /// Returns `false` only if the literal is immediately inconsistent with the
    /// current assignment.
    ///
    /// After a successful decision, call [`SeMiTONE::propagate`] to derive its
    /// consequences and detect theory conflicts.
    pub fn decide(&mut self, lit: Lit) -> bool {
        self.sat_solver.push();
        self.lra_theory.push();
        self.enum_theory.push();
        self.dl_theory.push();
        self.euf_theory.push();
        self.sat_solver.enqueue_decision(lit)
    }

    /// Decides that an enum variable takes a specific value in the current branch.
    ///
    /// Convenience wrapper around [`SeMiTONE::decide`]. Returns `false` if the
    /// decision cannot be enqueued consistently.
    pub fn decide_enum(&mut self, expr: impl AsRef<EnumExpr>, value: i32) -> bool {
        let var = match expr.as_ref() {
            EnumExpr::Var(v) => *v,
            EnumExpr::Const(_) => panic!("Cannot decide on a constant value"),
        };

        let lit = self.get_or_create_proxy(TheoryConstraint::EnumEq(var, value));
        self.decide(lit)
    }

    /// Returns the current internal decision level.
    ///
    /// Level `0` corresponds to the root level (no user decision applied).
    pub fn decision_level(&self) -> usize {
        self.sat_solver.decision_level()
    }

    /// Cancels all decisions and theory updates at levels deeper than `level`.
    ///
    /// This restores SAT/theory state to the requested level and drops pending
    /// notifications beyond the restored trail.
    pub fn cancel_until(&mut self, level: usize) {
        self.sat_solver.cancel_until(level);
        self.lra_theory.cancel_until(level);
        self.enum_theory.cancel_until(level);
        self.dl_theory.cancel_until(level);
        self.euf_theory.cancel_until(level);
        self.notified_len = self.sat_solver.trail.len();
    }

    /// Returns the trail suffix starting at `from_index`.
    ///
    /// Useful for external heuristics that need to inspect newly assigned literals.
    pub fn get_trail_delta(&self, from_index: usize) -> &[Lit] {
        &self.sat_solver.trail[from_index..]
    }

    /// Returns the current size of the SAT assignment trail.
    pub fn current_trail_len(&self) -> usize {
        self.sat_solver.trail.len()
    }

    /// Returns the trail length recorded at a specific decision level.
    ///
    /// If `level` is beyond the current number of levels, returns the current
    /// trail length.
    pub fn get_trail_len_at_level(&self, level: usize) -> usize {
        if level < self.sat_solver.trail_lim.len() { self.sat_solver.trail_lim[level] } else { self.sat_solver.trail.len() }
    }

    /// Returns a slice of the trail between `start` (inclusive) and `end` (exclusive).
    pub fn get_trail_slice(&self, start: usize, end: usize) -> &[Lit] {
        &self.sat_solver.trail[start..end]
    }

    /// Returns the number of currently active user scopes (`push`/`pop`).
    pub fn user_scopes_len(&self) -> usize {
        self.user_scopes.len()
    }

    /// Runs SAT + theory propagation until a fixed point or a conflict.
    ///
    /// Returns:
    /// - `Ok(())` if the current branch is feasible after propagation.
    /// - `Err((backtrack_level, no_good))` if a conflict is found.
    ///
    /// The returned `backtrack_level` is the suggested non-chronological level to
    /// backtrack to, and `no_good` is a conflict explanation suitable for learning.
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
                    (TheoryConstraint::DlLeq(from, to, bound), false) => self.dl_theory.assert_edge(*from, *to, bound.clone(), lit).map_err(|cycle| cycle.into_iter().map(|l| !l).collect()),
                    (TheoryConstraint::DlLeq(from, to, bound), true) => {
                        let rat_part = bound.rational_part().clone();
                        let neg_rat = match rat_part {
                            Rational::Finite(val) => Rational::Finite(-val),
                            Rational::PositiveInf => Rational::NegativeInf,
                            Rational::NegativeInf => Rational::PositiveInf,
                        };

                        let neg_inf = -bound.infinitesimal_part().clone() - rug::Rational::from(1);
                        let neg_bound = InfRational::new(neg_rat, neg_inf);

                        self.dl_theory.assert_edge(*to, *from, neg_bound, lit).map_err(|cycle| cycle.into_iter().map(|l| !l).collect())
                    }
                    (TheoryConstraint::EufEq(t1, t2), false) => {
                        self.euf_theory.merge(*t1, *t2, Some(lit));
                        self.euf_theory.propagate_congruences();
                        self.euf_theory.check_disequalities()
                    }
                    (TheoryConstraint::EufEq(t1, t2), true) => self.euf_theory.assert_disequality(*t1, *t2, lit),
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

    /// Returns the assigned value of a literal in the current trail.
    pub fn get_lit_val(&self, lit: Lit) -> Option<bool> {
        self.sat_solver.lit_value(lit)
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
            BoolExpr::Lt(e1, e2) => {
                let (lb1, ub1) = self.get_arith_bounds(e1)?;
                let (lb2, ub2) = self.get_arith_bounds(e2)?;
                if ub1 < lb2 {
                    Some(true)
                } else if lb1 >= ub2 {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::Le(e1, e2) => {
                let (lb1, ub1) = self.get_arith_bounds(e1)?;
                let (lb2, ub2) = self.get_arith_bounds(e2)?;
                if ub1 <= lb2 {
                    Some(true)
                } else if lb1 > ub2 {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::Ge(e1, e2) => {
                let (lb1, ub1) = self.get_arith_bounds(e1)?;
                let (lb2, ub2) = self.get_arith_bounds(e2)?;
                if lb1 >= ub2 {
                    Some(true)
                } else if ub1 < lb2 {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::Gt(e1, e2) => {
                let (lb1, ub1) = self.get_arith_bounds(e1)?;
                let (lb2, ub2) = self.get_arith_bounds(e2)?;
                if lb1 > ub2 {
                    Some(true)
                } else if ub1 <= lb2 {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::DlLt(from, to, bound) => {
                let (lb_from, ub_from) = self.get_time_bounds(*from);
                let (lb_to, ub_to) = self.get_time_bounds(*to);
                let bound_inf = InfRational::new(Rational::Finite(bound.clone()), rug::Rational::from(0));

                // Max possible distance: ub_to - lb_from
                // Min possible distance: lb_to - ub_from
                let max_dist = ub_to.clone() - lb_from.clone();
                let min_dist = lb_to - ub_from;

                if max_dist < bound_inf {
                    Some(true)
                } else if min_dist >= bound_inf {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::DlLe(from, to, bound) => {
                let (lb_from, ub_from) = self.get_time_bounds(*from);
                let (lb_to, ub_to) = self.get_time_bounds(*to);
                let bound_inf = InfRational::new(Rational::Finite(bound.clone()), rug::Rational::from(0));

                let max_dist = ub_to.clone() - lb_from.clone();
                let min_dist = lb_to - ub_from;

                if max_dist <= bound_inf {
                    Some(true)
                } else if min_dist > bound_inf {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::DlGt(from, to, bound) => {
                let (lb_from, ub_from) = self.get_time_bounds(*from);
                let (lb_to, ub_to) = self.get_time_bounds(*to);
                let bound_inf = InfRational::new(Rational::Finite(bound.clone()), rug::Rational::from(0));

                let max_dist = ub_to.clone() - lb_from.clone();
                let min_dist = lb_to - ub_from;

                if min_dist > bound_inf {
                    Some(true)
                } else if max_dist <= bound_inf {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::DlGe(from, to, bound) => {
                let (lb_from, ub_from) = self.get_time_bounds(*from);
                let (lb_to, ub_to) = self.get_time_bounds(*to);
                let bound_inf = InfRational::new(Rational::Finite(bound.clone()), rug::Rational::from(0));

                let max_dist = ub_to.clone() - lb_from.clone();
                let min_dist = lb_to - ub_from;

                if min_dist >= bound_inf {
                    Some(true)
                } else if max_dist < bound_inf {
                    Some(false)
                } else {
                    None
                }
            }
            BoolExpr::DlEq(from, to, bound) => {
                let (lb_from, ub_from) = self.get_time_bounds(*from);
                let (lb_to, ub_to) = self.get_time_bounds(*to);
                let bound_inf = InfRational::new(Rational::Finite(bound.clone()), rug::Rational::from(0));

                let max_dist = ub_to.clone() - lb_from.clone();
                let min_dist = lb_to - ub_from;

                // Exact equality means max_dist and min_dist are both exactly equal to bound
                if max_dist == bound_inf && min_dist == bound_inf {
                    Some(true)
                } else if max_dist < bound_inf || min_dist > bound_inf {
                    Some(false) // It's impossible to satisfy the equality
                } else {
                    None
                }
            }
            BoolExpr::Eq(e1, e2) => match (e1.as_ref(), e2.as_ref()) {
                (Expr::Arith(a1), Expr::Arith(a2)) => {
                    let (lb1, ub1) = self.get_arith_bounds(a1)?;
                    let (lb2, ub2) = self.get_arith_bounds(a2)?;
                    if ub1 < lb2 || ub2 < lb1 {
                        Some(false)
                    } else if lb1 == ub1 && lb2 == ub2 && lb1 == lb2 {
                        Some(true)
                    } else {
                        None
                    }
                }
                (Expr::Bool(b1), Expr::Bool(b2)) => {
                    let val1 = self.get_bool_val(b1);
                    let val2 = self.get_bool_val(b2);
                    match (val1, val2) {
                        (Some(v1), Some(v2)) => Some(v1 == v2),
                        _ => None,
                    }
                }
                (Expr::Enum(e1), Expr::Enum(e2)) => {
                    let val1 = self.get_enum_val(e1);
                    let val2 = self.get_enum_val(e2);
                    match (val1, val2) {
                        (Some(v1), Some(v2)) => Some(v1 == v2),
                        _ => None,
                    }
                }
                _ => None,
            },
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
                    sum += self.get_arith_val(term)?;
                }
                Some(sum)
            }
            ArithExpr::Neg(term) => self.get_arith_val(term).map(|val| -val),
            _ => None,
        }
    }

    /// Returns the current lower and upper bounds of an arithmetic expression when they are fixed by the model.
    pub fn get_arith_bounds(&self, expr: &ArithExpr) -> Option<(InfRational, InfRational)> {
        match expr {
            ArithExpr::Const(c) => {
                let val = InfRational::new(Rational::Finite(c.clone()), rug::Rational::from(0));
                Some((val.clone(), val))
            }
            ArithExpr::RealVar(v) | ArithExpr::IntVar(v) => Some((self.lra_theory.lb(*v).clone(), self.lra_theory.ub(*v).clone())),
            ArithExpr::Add(terms) => {
                let mut sum_lb = InfRational::new(Rational::Finite(rug::Rational::from(0)), rug::Rational::from(0));
                let mut sum_ub = sum_lb.clone();
                for term in terms {
                    let (lb, ub) = self.get_arith_bounds(term)?;
                    sum_lb += lb;
                    sum_ub += ub;
                }
                Some((sum_lb, sum_ub))
            }
            ArithExpr::Neg(term) => {
                let (lb, ub) = self.get_arith_bounds(term)?;
                Some((-ub, -lb))
            }
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

    /// Returns the current lower and upper bounds of a difference logic variable.
    pub fn get_time_bounds(&self, tp: usize) -> (InfRational, InfRational) {
        (self.dl_theory.lb(tp), self.dl_theory.ub(tp))
    }

    /// Opens a new incremental user scope for assertions and decisions.
    ///
    /// All constraints/decisions added after this call can be discarded by
    /// [`SeMiTONE::pop`].
    pub fn push(&mut self) {
        let clauses_len = self.sat_solver.clauses.len();

        self.sat_solver.push();
        self.lra_theory.push();
        self.enum_theory.push();
        self.dl_theory.push();

        let current_level = self.sat_solver.decision_level();
        self.user_scopes.push((current_level, clauses_len));
    }

    /// Restores the previous user scope and discards assertions added in it.
    ///
    /// If no user scope is open, this is a no-op.
    pub fn pop(&mut self) {
        if let Some((saved_level, saved_clauses_len)) = self.user_scopes.pop() {
            self.cancel_until(saved_level - 1);
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

    /// Checks integrality of integer variables under the current rational model.
    ///
    /// Returns `Ok(())` if all integer variables are integral.
    /// Otherwise returns `Err((backtrack_level, lemma))`, where `lemma` is either
    /// a generated Gomory cut or a branching disjunction for branch-and-bound.
    pub fn check_ints(&mut self) -> Result<(), (usize, Vec<Lit>)> {
        if let Err((var, val)) = self.lra_theory.check_ints() {
            println!("Integer variable {} has fractional value {}", var, val);
            let base_level = self.user_scopes.last().map(|&(lvl, _)| lvl).unwrap_or(0);

            if let Some((cut_row, f0)) = self.lra_theory.generate_gomory_cut(var) {
                let cut_slack = self.lra_theory.get_or_create_slack(cut_row);
                let bound = InfRational::new(Rational::Finite(f0), rug::Rational::from(0));
                let cut_lit = self.get_or_create_proxy(TheoryConstraint::LraLb(cut_slack, bound));

                let lemma = vec![cut_lit];
                return Err((base_level, lemma));
            }

            let Rational::Finite(inner_frac) = val.rational_part() else {
                unreachable!("Fractional variable in Branch & Bound must be finite");
            };

            let mut floor_val = inner_frac.clone();
            floor_val.floor_mut();
            let mut ceil_val = inner_frac.clone();
            ceil_val.ceil_mut();

            if floor_val == ceil_val {
                let inf_part = val.infinitesimal_part();
                if inf_part > &rug::Rational::from(0) {
                    ceil_val += rug::Rational::from(1);
                } else if inf_part < &rug::Rational::from(0) {
                    floor_val -= rug::Rational::from(1);
                }
            }

            let ub = InfRational::new(Rational::Finite(floor_val), rug::Rational::from(0));
            let lb = InfRational::new(Rational::Finite(ceil_val), rug::Rational::from(0));
            println!("Branching on variable {}: x <= {} or x >= {}", var, ub, lb);

            let lit_ub = self.get_or_create_proxy(TheoryConstraint::LraUb(var, ub));
            let lit_lb = self.get_or_create_proxy(TheoryConstraint::LraLb(var, lb));
            let lemma = vec![lit_ub, lit_lb];

            let current_level = self.sat_solver.decision_level();
            return Err((current_level, lemma));
        }
        Ok(())
    }
}

#[cold]
#[inline(never)]
pub(crate) fn out_of_bounds(var: usize) -> ! {
    panic!("variable index out of bounds: {}", var);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pure_sat_resolution() {
        let mut solver = SeMiTONE::new();

        let a = solver.new_bool();
        let b = solver.new_bool();
        let c = solver.new_bool();

        // (A ∨ B) ∧ (¬B ∨ C) ∧ (¬B ∨ ¬C) ∧ (¬A)
        // With ¬A, clause (A ∨ B) forces B; then B forces both C and ¬C.
        let expr = (&a | &b) & (&!&b | &c) & (!&b | !&c) & !&a;

        let _ = solver.assert(expr);
        assert!(solver.propagate().is_err(), "The solver should detect that the system is unsatisfiable");
    }

    #[test]
    fn test_early_bounding_unsat() {
        let mut solver = SeMiTONE::new();
        let x = solver.new_real();

        // x > 10 ∧ x < 5
        let expr = (x.clone().gt(10)) & (x.lt(5));

        let result = solver.assert(expr);
        assert!(!result, "The solver should detect that the system is unsatisfiable");
    }

    #[test]
    fn test_equality_mutually_exclusive() {
        let mut solver = SeMiTONE::new();
        let x = solver.new_real();

        // x == 5 ∧ x > 6
        let expr = (x.clone().eq(5)) & (x.gt(6));

        let result = solver.assert(expr);
        assert!(!result, "The solver should detect that the system is unsatisfiable");
    }

    #[test]
    fn test_simplex_system_unsat() {
        let mut solver = SeMiTONE::new();
        let x = solver.new_real();
        let y = solver.new_real();

        // x + y == 10
        let eq_expr = (x.clone() + y.clone()).eq(10);
        // x > 6
        let gt_x = x.clone().gt(6);
        // y > 6
        let gt_y = y.clone().gt(6);

        let expr = eq_expr & gt_x & gt_y;

        let _ = solver.assert(expr);
        assert!(solver.propagate().is_err(), "The solver should detect that the system is unsatisfiable");
    }

    #[test]
    fn test_constant_arithmetic_evaluations() {
        let mut solver = SeMiTONE::new();

        assert!(solver.assert(ArithExpr::from(5).lt(10)));
        assert!(solver.assert(ArithExpr::from(5).le(5)));
        assert!(solver.assert(ArithExpr::from(10).ge(5)));
        assert!(solver.assert(ArithExpr::from(10).gt(5)));

        assert!(!solver.assert(ArithExpr::from(10).lt(5)));
        assert!(!solver.assert(ArithExpr::from(10).le(5)));
        assert!(!solver.assert(ArithExpr::from(5).ge(10)));
        assert!(!solver.assert(ArithExpr::from(5).gt(10)));

        assert!(solver.assert(!ArithExpr::from(10).lt(5)));
        assert!(!solver.assert(!ArithExpr::from(5).lt(10)));
    }

    #[test]
    fn test_negated_variable_inequalities() {
        let mut solver = SeMiTONE::new();
        let x = solver.new_real();

        solver.push();
        assert!(solver.assert(!x.clone().lt(5)));
        assert!(!solver.assert(x.clone().lt(4)));
        solver.pop();

        solver.push();
        assert!(solver.assert(!x.clone().le(5)));
        assert!(!solver.assert(x.clone().le(5)));
        solver.pop();

        solver.push();
        assert!(solver.assert(!x.clone().ge(5)));
        assert!(!solver.assert(x.clone().ge(5)));
        solver.pop();

        solver.push();
        assert!(solver.assert(!x.clone().gt(5)));
        assert!(!solver.assert(x.clone().gt(5)));
        solver.pop();
    }

    #[test]
    #[should_panic(expected = "Type mismatch in Eq")]
    fn test_encode_eq_type_mismatch_panic() {
        let mut solver = SeMiTONE::new();
        let a = solver.new_bool();
        let x = solver.new_real();

        let bad_eq = BoolExpr::Eq(Box::new(Expr::Bool(a)), Box::new(Expr::Arith(x)));

        let _ = solver.assert(bad_eq);
    }

    #[test]
    fn test_enum_out_of_domain_unsat() {
        let mut solver = SeMiTONE::new();
        let e = solver.new_enum(vec![1, 2]);

        let expr = e.eq(3);

        let _ = solver.assert(expr);
        assert!(solver.propagate().is_err(), "The solver should detect that the enum variable cannot take a value outside its domain");
    }

    #[test]
    fn test_enum_exhaustive_denial_integration() {
        let mut solver = SeMiTONE::new();
        let e = solver.new_enum(vec![1, 2]);

        // (e != 1) AND (e != 2)
        let expr = !(e.clone().eq(1)) & !(e.clone().eq(2));

        let _ = solver.assert(expr);
        assert!(solver.propagate().is_err(), "The solver should detect that the enum variable cannot take a value outside its domain");
    }

    #[test]
    fn test_dl_chain_upper_bounds() {
        let mut solver = SeMiTONE::new();
        let zero = solver.new_time_point(); // first time point created = reference 0 in the DL theory
        let t1 = solver.new_time_point();
        let t2 = solver.new_time_point();

        let _ = solver.assert(BoolExpr::DlLe(zero, t1, rug::Rational::from(10))); // t1 - zero <= 10
        let _ = solver.assert(BoolExpr::DlLe(t1, t2, rug::Rational::from(5))); // t2 - t1 <= 5

        assert!(solver.propagate().is_ok());

        assert_eq!(solver.get_time_bounds(t1).1, InfRational::from(10));
        assert_eq!(solver.get_time_bounds(t2).1, InfRational::from(15));
        assert_eq!(solver.get_time_bounds(t1).0, InfRational::from(Rational::NegativeInf), "no lower bound imposed");
    }

    #[test]
    fn test_dl_lower_and_upper_bound_interval() {
        let mut solver = SeMiTONE::new();
        let zero = solver.new_time_point();
        let t1 = solver.new_time_point();

        let _ = solver.assert(BoolExpr::DlLe(zero, t1, rug::Rational::from(8))); // t1 <= 8
        let _ = solver.assert(BoolExpr::DlGe(zero, t1, rug::Rational::from(3))); // t1 >= 3

        assert!(solver.propagate().is_ok());
        assert_eq!(solver.get_time_bounds(t1), (InfRational::from(3), InfRational::from(8)));
    }

    #[test]
    fn test_dl_eq_pins_value() {
        let mut solver = SeMiTONE::new();
        let zero = solver.new_time_point();
        let t1 = solver.new_time_point();

        let _ = solver.assert(BoolExpr::DlEq(zero, t1, rug::Rational::from(7)));
        assert!(solver.propagate().is_ok());

        assert_eq!(solver.get_time_bounds(t1), (InfRational::from(7), InfRational::from(7)));
    }

    #[test]
    fn test_dl_negative_cycle_conflict() {
        let mut solver = SeMiTONE::new();
        let a = solver.new_time_point();
        let b = solver.new_time_point();

        // b - a <= 5 and b - a >= 10 (via a - b <= -10): irreconcilable
        let _ = solver.assert(BoolExpr::DlLe(a, b, rug::Rational::from(5)));
        let _ = solver.assert(BoolExpr::DlLe(b, a, rug::Rational::from(-10)));

        assert!(solver.propagate().is_err(), "the negative cycle must produce a conflict");
    }

    #[test]
    fn test_dl_strict_boundary_conflict() {
        let mut solver = SeMiTONE::new();
        let a = solver.new_time_point();
        let b = solver.new_time_point();

        // b - a <= 0 (non-strict) and a - b < 0, i.e. b - a > 0 (strict):
        // the weights sum to 0 but the conflict must be detected via the infinitesimal trick
        let _ = solver.assert(BoolExpr::DlLe(a, b, rug::Rational::from(0)));
        let _ = solver.assert(BoolExpr::DlLt(b, a, rug::Rational::from(0)));

        assert!(solver.propagate().is_err());
    }

    #[test]
    fn test_dl_non_strict_boundary_is_sat() {
        let mut solver = SeMiTONE::new();
        let a = solver.new_time_point();
        let b = solver.new_time_point();

        let _ = solver.assert(BoolExpr::DlLe(a, b, rug::Rational::from(0)));
        let _ = solver.assert(BoolExpr::DlLe(b, a, rug::Rational::from(0)));

        assert!(solver.propagate().is_ok());
        assert_eq!(solver.get_time_bounds(b), solver.get_time_bounds(a), "b == a == 0");
    }

    #[test]
    fn test_dl_backtracking_via_push_pop() {
        let mut solver = SeMiTONE::new();
        let zero = solver.new_time_point();
        let t1 = solver.new_time_point();

        solver.push();
        let _ = solver.assert(BoolExpr::DlLe(zero, t1, rug::Rational::from(4)));
        assert!(solver.propagate().is_ok());
        assert_eq!(solver.get_time_bounds(t1).1, InfRational::from(4));
        solver.pop();

        assert_eq!(solver.get_time_bounds(t1).1, InfRational::from(Rational::PositiveInf), "the constraint must disappear after the pop");
    }

    #[test]
    fn test_dl_negated_le_forces_strict_gt() {
        // `assert(!expr)` goes through the catch-all branch of `assert_internal`, which negates
        // at the SAT level the literal already registered for DlLe (it does not call mk_dl_ge).
        // This exercises the `(DlLeq(..), false)` branch of `propagate()`.
        let mut solver = SeMiTONE::new();
        let a = solver.new_time_point();
        let b = solver.new_time_point();

        let neg_le = BoolExpr::Not(Box::new(BoolExpr::DlLe(a, b, rug::Rational::from(4))));
        let _ = solver.assert(neg_le);
        assert!(solver.propagate().is_ok());

        let (lb_b, _) = solver.get_time_bounds(b);
        assert!(lb_b > InfRational::from(4), "!(b - a <= 4) must imply b - a > 4, found lb(b) = {:?}", lb_b);
    }
}
