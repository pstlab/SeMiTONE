use std::{fmt, ops};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoolVar(pub(crate) usize);

impl fmt::Display for BoolVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumVar(pub(crate) usize);

impl fmt::Display for EnumVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntVar(pub(crate) usize);

impl fmt::Display for IntVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "i{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RealVar(pub(crate) usize);

impl fmt::Display for RealVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DlVar(pub(crate) usize);

impl fmt::Display for DlVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "d{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncId(pub(crate) usize);

impl fmt::Display for FuncId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "f{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EufVar(pub(crate) usize);

impl fmt::Display for EufVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "u{}", self.0)
    }
}

/// A typed expression that can be embedded in a generic equality.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// A Boolean expression.
    Bool(BoolExpr),
    /// A finite-domain enum expression.
    Enum(EnumExpr),
    /// An integer or real arithmetic expression.
    Arith(ArithExpr),
    /// An expression in the EUF theory.
    Euf(EufExpr),
}

impl Expr {
    /// Builds a typed equality constraint between two expressions.
    pub fn eq(self, other: Expr) -> BoolExpr {
        BoolExpr::Eq(Box::new(self), Box::new(other))
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Expr::Bool(BoolExpr::from(b))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Enum(e) => write!(f, "{}", e),
            Expr::Arith(a) => write!(f, "{}", a),
            Expr::Euf(e) => write!(f, "{}", e),
        }
    }
}

/// A Boolean formula accepted by [`crate::SeMiTONE::assert`].
///
/// Use `!`, `&`, and `|` to construct negations, conjunctions, and
/// disjunctions. The `&` and `|` operators flatten nested expressions of the
/// same kind while preserving operand order.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoolExpr {
    /// The Boolean constant `true`.
    True,
    /// The Boolean constant `false`.
    False,
    /// A Boolean variable allocated by [`crate::SeMiTONE::new_bool`].
    Var(BoolVar),
    /// Logical negation.
    Not(Box<BoolExpr>),
    /// Logical conjunction.
    And(Vec<BoolExpr>),
    /// Logical disjunction.
    Or(Vec<BoolExpr>),
    /// Strict arithmetic comparison.
    Lt(ArithExpr, ArithExpr),
    /// Non-strict arithmetic comparison.
    Le(ArithExpr, ArithExpr),
    /// Non-strict arithmetic comparison.
    Ge(ArithExpr, ArithExpr),
    /// Strict arithmetic comparison.
    Gt(ArithExpr, ArithExpr),
    /// Equality between expressions of the same theory.
    Eq(Box<Expr>, Box<Expr>),
    /// A strict difference logic constraint.
    DlLt(DlVar, DlVar, rug::Rational),
    /// A non-strict difference logic constraint.
    DlLe(DlVar, DlVar, rug::Rational),
    /// An equality difference logic constraint.
    DlEq(DlVar, DlVar, rug::Rational),
    /// A non-strict difference logic constraint.
    DlGe(DlVar, DlVar, rug::Rational),
    /// A strict difference logic constraint.
    DlGt(DlVar, DlVar, rug::Rational),
}

impl BoolExpr {
    /// Builds an equality constraint between two Boolean formulas.
    pub fn eq(&self, other: &BoolExpr) -> BoolExpr {
        BoolExpr::Eq(Box::new(Expr::Bool(self.clone())), Box::new(Expr::Bool(other.clone())))
    }
}

impl From<bool> for BoolExpr {
    fn from(b: bool) -> Self {
        if b { BoolExpr::True } else { BoolExpr::False }
    }
}

impl ops::Not for BoolExpr {
    type Output = Self;

    fn not(self) -> Self {
        BoolExpr::Not(Box::new(self))
    }
}

impl ops::Not for &BoolExpr {
    type Output = BoolExpr;

    fn not(self) -> Self::Output {
        !(*self).clone()
    }
}

impl ops::BitAnd for BoolExpr {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (BoolExpr::And(mut left_vec), BoolExpr::And(mut right_vec)) => {
                left_vec.append(&mut right_vec);
                BoolExpr::And(left_vec)
            }
            (BoolExpr::And(mut left_vec), rhs_expr) => {
                left_vec.push(rhs_expr);
                BoolExpr::And(left_vec)
            }
            (lhs_expr, BoolExpr::And(mut right_vec)) => {
                right_vec.insert(0, lhs_expr);
                BoolExpr::And(right_vec)
            }
            (lhs_expr, rhs_expr) => BoolExpr::And(vec![lhs_expr, rhs_expr]),
        }
    }
}

impl ops::BitAnd<&BoolExpr> for &BoolExpr {
    type Output = BoolExpr;

    fn bitand(self, rhs: &BoolExpr) -> Self::Output {
        self.clone() & rhs.clone()
    }
}

impl ops::BitOr for BoolExpr {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (BoolExpr::Or(mut left_vec), BoolExpr::Or(mut right_vec)) => {
                left_vec.append(&mut right_vec);
                BoolExpr::Or(left_vec)
            }
            (BoolExpr::Or(mut left_vec), rhs_expr) => {
                left_vec.push(rhs_expr);
                BoolExpr::Or(left_vec)
            }
            (lhs_expr, BoolExpr::Or(mut right_vec)) => {
                right_vec.insert(0, lhs_expr);
                BoolExpr::Or(right_vec)
            }
            (lhs_expr, rhs_expr) => BoolExpr::Or(vec![lhs_expr, rhs_expr]),
        }
    }
}

impl ops::BitOr<&BoolExpr> for &BoolExpr {
    type Output = BoolExpr;

    fn bitor(self, rhs: &BoolExpr) -> Self::Output {
        self.clone() | rhs.clone()
    }
}

impl AsRef<BoolExpr> for BoolExpr {
    fn as_ref(&self) -> &BoolExpr {
        self
    }
}

impl fmt::Display for BoolExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoolExpr::True => write!(f, "true"),
            BoolExpr::False => write!(f, "false"),
            BoolExpr::Var(v) => write!(f, "{}", v),
            BoolExpr::Not(e) => write!(f, "¬{}", e),
            BoolExpr::And(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" ∧ "))
            }
            BoolExpr::Or(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" ∨ "))
            }
            BoolExpr::Lt(a1, a2) => write!(f, "{} < {}", a1, a2),
            BoolExpr::Le(a1, a2) => write!(f, "{} ≤ {}", a1, a2),
            BoolExpr::Ge(a1, a2) => write!(f, "{} ≥ {}", a1, a2),
            BoolExpr::Gt(a1, a2) => write!(f, "{} > {}", a1, a2),
            BoolExpr::Eq(e1, e2) => write!(f, "{} = {}", e1, e2),
            BoolExpr::DlLt(from, to, bound) => write!(f, "{} - {} < {}", to, from, bound),
            BoolExpr::DlLe(from, to, bound) => write!(f, "{} - {} ≤ {}", to, from, bound),
            BoolExpr::DlEq(from, to, bound) => write!(f, "{} - {} = {}", to, from, bound),
            BoolExpr::DlGe(from, to, bound) => write!(f, "{} - {} ≥ {}", to, from, bound),
            BoolExpr::DlGt(from, to, bound) => write!(f, "{} - {} > {}", to, from, bound),
        }
    }
}

/// A finite-domain enum variable or integer constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EnumExpr {
    /// An enum variable allocated by [`crate::SeMiTONE::new_enum`].
    Var(EnumVar),
    /// An enum constant.
    Const(i32),
}

impl From<i32> for EnumExpr {
    fn from(n: i32) -> Self {
        EnumExpr::Const(n)
    }
}

impl From<&EnumExpr> for EnumExpr {
    fn from(expr: &EnumExpr) -> Self {
        expr.clone()
    }
}

impl EnumExpr {
    /// Builds an equality constraint between two enum expressions.
    pub fn eq(&self, other: impl Into<EnumExpr>) -> BoolExpr {
        BoolExpr::Eq(Box::new(Expr::Enum(self.clone())), Box::new(Expr::Enum(other.into())))
    }
}

impl AsRef<EnumExpr> for EnumExpr {
    fn as_ref(&self) -> &EnumExpr {
        self
    }
}

impl fmt::Display for EnumExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EnumExpr::Var(n) => write!(f, "{}", n),
            EnumExpr::Const(n) => write!(f, "#{}", n),
        }
    }
}

/// An arithmetic expression over integer and real solver variables.
///
/// Use `+`, `-`, `*`, `/`, and unary `-` to compose expressions. Arithmetic
/// comparisons are constructed with [`ArithExpr::lt`], [`ArithExpr::le`],
/// [`ArithExpr::ge`], [`ArithExpr::gt`], and [`ArithExpr::eq`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArithExpr {
    /// A rational constant.
    Const(rug::Rational),
    /// An integer variable allocated by [`crate::SeMiTONE::new_int`].
    IntVar(IntVar),
    /// A real variable allocated by [`crate::SeMiTONE::new_real`].
    RealVar(RealVar),
    /// A sum of arithmetic terms.
    Add(Vec<ArithExpr>),
    /// A product of arithmetic terms.
    Mul(Vec<ArithExpr>),
    /// Division of two arithmetic expressions.
    Div(Box<ArithExpr>, Box<ArithExpr>),
    /// Arithmetic negation.
    Neg(Box<ArithExpr>),
}

impl ArithExpr {
    /// Builds the constraint `self < other`.
    pub fn lt(&self, other: impl Into<ArithExpr>) -> BoolExpr {
        BoolExpr::Lt(self.clone(), other.into())
    }

    /// Builds the constraint `self <= other`.
    pub fn le(&self, other: impl Into<ArithExpr>) -> BoolExpr {
        BoolExpr::Le(self.clone(), other.into())
    }

    /// Builds the constraint `self > other`.
    pub fn gt(&self, other: impl Into<ArithExpr>) -> BoolExpr {
        BoolExpr::Gt(self.clone(), other.into())
    }

    /// Builds the constraint `self >= other`.
    pub fn ge(&self, other: impl Into<ArithExpr>) -> BoolExpr {
        BoolExpr::Ge(self.clone(), other.into())
    }

    /// Builds the constraint `self = other`.
    pub fn eq(&self, other: impl Into<ArithExpr>) -> BoolExpr {
        BoolExpr::Eq(Box::new(Expr::Arith(self.clone())), Box::new(Expr::Arith(other.into())))
    }
}

impl From<i32> for ArithExpr {
    fn from(n: i32) -> Self {
        ArithExpr::Const(rug::Rational::from(n))
    }
}

impl From<(i32, i32)> for ArithExpr {
    fn from((num, denom): (i32, i32)) -> Self {
        ArithExpr::Const(rug::Rational::from((num, denom)))
    }
}

impl From<&ArithExpr> for ArithExpr {
    fn from(expr: &ArithExpr) -> Self {
        expr.clone()
    }
}

impl ops::Add for ArithExpr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ArithExpr::Add(mut left_vec), ArithExpr::Add(mut right_vec)) => {
                left_vec.append(&mut right_vec);
                ArithExpr::Add(left_vec)
            }
            (ArithExpr::Add(mut left_vec), rhs_expr) => {
                left_vec.push(rhs_expr);
                ArithExpr::Add(left_vec)
            }
            (lhs_expr, ArithExpr::Add(mut right_vec)) => {
                right_vec.insert(0, lhs_expr);
                ArithExpr::Add(right_vec)
            }
            (lhs_expr, rhs_expr) => ArithExpr::Add(vec![lhs_expr, rhs_expr]),
        }
    }
}

impl ops::Add<&ArithExpr> for &ArithExpr {
    type Output = ArithExpr;

    fn add(self, rhs: &ArithExpr) -> Self::Output {
        self.clone() + rhs.clone()
    }
}

impl ops::Sub for ArithExpr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + -rhs
    }
}

impl ops::Sub<&ArithExpr> for &ArithExpr {
    type Output = ArithExpr;

    fn sub(self, rhs: &ArithExpr) -> Self::Output {
        self.clone() - rhs.clone()
    }
}

impl ops::Mul for ArithExpr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ArithExpr::Mul(mut left_vec), ArithExpr::Mul(mut right_vec)) => {
                left_vec.append(&mut right_vec);
                ArithExpr::Mul(left_vec)
            }
            (ArithExpr::Mul(mut left_vec), rhs_expr) => {
                left_vec.push(rhs_expr);
                ArithExpr::Mul(left_vec)
            }
            (lhs_expr, ArithExpr::Mul(mut right_vec)) => {
                right_vec.insert(0, lhs_expr);
                ArithExpr::Mul(right_vec)
            }
            (lhs_expr, rhs_expr) => ArithExpr::Mul(vec![lhs_expr, rhs_expr]),
        }
    }
}

impl ops::Mul<&ArithExpr> for &ArithExpr {
    type Output = ArithExpr;

    fn mul(self, rhs: &ArithExpr) -> Self::Output {
        self.clone() * rhs.clone()
    }
}

impl ops::Div for ArithExpr {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        ArithExpr::Div(Box::new(self), Box::new(rhs))
    }
}

impl ops::Div<&ArithExpr> for &ArithExpr {
    type Output = ArithExpr;

    fn div(self, rhs: &ArithExpr) -> Self::Output {
        self.clone() / rhs.clone()
    }
}

impl ops::Neg for ArithExpr {
    type Output = Self;

    fn neg(self) -> Self {
        ArithExpr::Neg(Box::new(self))
    }
}

impl ops::Neg for &ArithExpr {
    type Output = ArithExpr;

    fn neg(self) -> Self::Output {
        -(*self).clone()
    }
}

impl fmt::Display for ArithExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArithExpr::Const(r) => write!(f, "{}", r),
            ArithExpr::IntVar(n) => write!(f, "{}", n),
            ArithExpr::RealVar(n) => write!(f, "{}", n),
            ArithExpr::Add(es) => {
                let mut it = es.iter();
                let Some(first) = it.next() else { return write!(f, "()") };

                write!(f, "({}", first)?;
                for term in it {
                    match term {
                        ArithExpr::Neg(inner) => write!(f, " - {}", inner)?,
                        _ => write!(f, " + {}", term)?,
                    }
                }
                write!(f, ")")
            }
            ArithExpr::Neg(e) => write!(f, "-{}", e),
            ArithExpr::Mul(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" * "))
            }
            ArithExpr::Div(e1, e2) => write!(f, "({} / {})", e1, e2),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EufExpr {
    Var(EufVar),
    App(FuncId, Vec<Expr>),
}

impl EufExpr {
    pub fn eq(&self, other: impl Into<EufExpr>) -> BoolExpr {
        BoolExpr::Eq(Box::new(Expr::Euf(self.clone())), Box::new(Expr::Euf(other.into())))
    }
}

impl fmt::Display for EufExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EufExpr::Var(n) => write!(f, "{}", n),
            EufExpr::App(func_id, args) => {
                let args_str: Vec<String> = args.iter().map(|a| format!("{}", a)).collect();
                write!(f, "{}({})", func_id, args_str.join(", "))
            }
        }
    }
}

fn push_negations(expr: &BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::Not(inner) => push_inverted(inner),
        BoolExpr::And(terms) => BoolExpr::And(terms.iter().map(push_negations).collect()),
        BoolExpr::Or(terms) => BoolExpr::Or(terms.iter().map(push_negations).collect()),
        _ => expr.clone(),
    }
}

fn push_inverted(expr: &BoolExpr) -> BoolExpr {
    match expr {
        // Double negation elimination: Not(Not(x)) => x
        BoolExpr::Not(inner) => push_negations(inner),

        // De Morgan: Not(And(a, b, ...)) => Or(Not(a), Not(b), ...)
        BoolExpr::And(terms) => BoolExpr::Or(terms.iter().map(push_inverted).collect()),

        // De Morgan: Not(Or(a, b, ...)) => And(Not(a), Not(b), ...)
        BoolExpr::Or(terms) => BoolExpr::And(terms.iter().map(push_inverted).collect()),

        // Negate comparisons by flipping to their complement
        BoolExpr::Lt(a, b) => BoolExpr::Ge(a.clone(), b.clone()),
        BoolExpr::Le(a, b) => BoolExpr::Gt(a.clone(), b.clone()),
        BoolExpr::Ge(a, b) => BoolExpr::Lt(a.clone(), b.clone()),
        BoolExpr::Gt(a, b) => BoolExpr::Le(a.clone(), b.clone()),
        BoolExpr::Eq(a, b) => BoolExpr::Not(Box::new(BoolExpr::Eq(a.clone(), b.clone()))),

        // Literals, variables: wrap in Not
        _ => BoolExpr::Not(Box::new(expr.clone())),
    }
}

fn distribute(expr: &BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::Or(terms) => {
            // Step 1: Recursively distribute children, flatten nested Ors
            let mut distributed_terms = Vec::new();
            for t in terms {
                let dist = distribute(t);
                if let BoolExpr::Or(inner_terms) = dist {
                    distributed_terms.extend(inner_terms);
                } else {
                    distributed_terms.push(dist);
                }
            }

            // Step 2: Cartesian product over And boundaries
            let mut result_ands: Vec<Vec<BoolExpr>> = vec![vec![]];

            for term in distributed_terms {
                if let BoolExpr::And(and_terms) = term {
                    let mut next_ands = Vec::new();
                    for existing_and in &result_ands {
                        for and_term in &and_terms {
                            let mut combo = existing_and.clone();
                            combo.push(and_term.clone());
                            next_ands.push(combo);
                        }
                    }
                    result_ands = next_ands;
                } else {
                    for existing_and in &mut result_ands {
                        existing_and.push(term.clone());
                    }
                }
            }

            // Step 3: Wrap combinations back into Or nodes inside a master And
            let cnf_or_nodes: Vec<BoolExpr> = result_ands.into_iter().map(BoolExpr::Or).collect();

            if cnf_or_nodes.len() == 1 { cnf_or_nodes.into_iter().next().unwrap() } else { BoolExpr::And(cnf_or_nodes) }
        }

        BoolExpr::And(terms) => {
            // Flatten nested Ands
            let mut distributed_terms = Vec::new();
            for t in terms {
                let dist = distribute(t);
                if let BoolExpr::And(inner_terms) = dist {
                    distributed_terms.extend(inner_terms);
                } else {
                    distributed_terms.push(dist);
                }
            }
            BoolExpr::And(distributed_terms)
        }

        _ => expr.clone(),
    }
}

/// Converts a boolean formula to conjunctive normal form.
///
/// This rewrites the expression by pushing negations downward and distributing
/// logical operators until the result is represented as a CNF formula.
pub fn to_cnf(expr: &BoolExpr) -> BoolExpr {
    distribute(&push_negations(expr))
}

/// Constrains `z` to be the minimum of a non-empty set of arithmetic values.
pub fn min(z: ArithExpr, args: impl IntoIterator<Item = ArithExpr>) -> BoolExpr {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.is_empty() {
        panic!("min constraint requires at least one argument");
    }

    let mut and_terms = Vec::with_capacity(args.len() + 1);
    let mut or_terms = Vec::with_capacity(args.len());

    for arg in args {
        and_terms.push(BoolExpr::Le(z.clone(), arg.clone()));

        let eq_expr = BoolExpr::Eq(Box::new(Expr::Arith(z.clone())), Box::new(Expr::Arith(arg)));
        or_terms.push(eq_expr);
    }

    and_terms.push(BoolExpr::Or(or_terms));

    BoolExpr::And(and_terms)
}

/// Constrains `z` to be the maximum of a non-empty set of arithmetic values.
pub fn max(z: ArithExpr, args: impl IntoIterator<Item = ArithExpr>) -> BoolExpr {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.is_empty() {
        panic!("max constraint requires at least one argument");
    }

    let mut and_terms = Vec::with_capacity(args.len() + 1);
    let mut or_terms = Vec::with_capacity(args.len());

    for arg in args {
        and_terms.push(BoolExpr::Ge(z.clone(), arg.clone()));

        let eq_expr = BoolExpr::Eq(Box::new(Expr::Arith(z.clone())), Box::new(Expr::Arith(arg)));
        or_terms.push(eq_expr);
    }

    and_terms.push(BoolExpr::Or(or_terms));

    BoolExpr::And(and_terms)
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- BoolExpr Display ---

    #[test]
    fn bool_display_lit() {
        assert_eq!(BoolExpr::True.to_string(), "true");
        assert_eq!(BoolExpr::False.to_string(), "false");
    }

    #[test]
    fn bool_display_var() {
        assert_eq!(BoolExpr::Var(BoolVar(3)).to_string(), "b3");
    }

    #[test]
    fn bool_display_not() {
        assert_eq!((!BoolExpr::Var(BoolVar(0))).to_string(), "¬b0");
    }

    #[test]
    fn bool_display_and() {
        assert_eq!((BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1))).to_string(), "(b0 ∧ b1)");
    }

    #[test]
    fn bool_display_or() {
        assert_eq!((BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1))).to_string(), "(b0 ∨ b1)");
    }

    #[test]
    fn bool_display_comparisons() {
        assert_eq!(BoolExpr::Lt(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))).to_string(), "i0 < i1");
        assert_eq!(BoolExpr::Le(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))).to_string(), "i0 ≤ i1");
        assert_eq!(BoolExpr::Ge(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))).to_string(), "i0 ≥ i1");
        assert_eq!(BoolExpr::Gt(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))).to_string(), "i0 > i1");
    }

    #[test]
    fn bool_display_eq() {
        let e = BoolExpr::Eq(Box::new(Expr::Bool(BoolExpr::Var(BoolVar(0)))), Box::new(Expr::Bool(BoolExpr::Var(BoolVar(1)))));
        assert_eq!(e.to_string(), "b0 = b1");
    }

    // --- ArithExpr Display ---

    #[test]
    fn arith_display_lit() {
        assert_eq!(ArithExpr::Const(rug::Rational::from(5)).to_string(), "5");
    }

    #[test]
    fn arith_display_int_real() {
        assert_eq!(ArithExpr::IntVar(IntVar(2)).to_string(), "i2");
        assert_eq!(ArithExpr::RealVar(RealVar(5)).to_string(), "r5");
    }

    #[test]
    fn arith_display_add() {
        let e = ArithExpr::IntVar(IntVar(0)) + ArithExpr::IntVar(IntVar(1));
        assert_eq!(e.to_string(), "(i0 + i1)");
    }

    #[test]
    fn arith_display_sub() {
        let e = ArithExpr::IntVar(IntVar(0)) - ArithExpr::IntVar(IntVar(1));
        assert_eq!(e.to_string(), "(i0 - i1)");
    }

    #[test]
    fn arith_display_mul() {
        let e = ArithExpr::IntVar(IntVar(0)) * ArithExpr::IntVar(IntVar(1));
        assert_eq!(e.to_string(), "(i0 * i1)");
    }

    #[test]
    fn arith_display_div() {
        let e = ArithExpr::Div(Box::new(ArithExpr::IntVar(IntVar(0))), Box::new(ArithExpr::IntVar(IntVar(1))));
        assert_eq!(e.to_string(), "(i0 / i1)");
    }

    // --- push_negations ---

    #[test]
    fn push_negations_literal_unchanged() {
        assert_eq!(push_negations(&BoolExpr::True), BoolExpr::True);
    }

    #[test]
    fn push_negations_var_unchanged() {
        assert_eq!(push_negations(&BoolExpr::Var(BoolVar(0))), BoolExpr::Var(BoolVar(0)));
    }

    #[test]
    fn push_negations_not_var_becomes_not_var() {
        // Not(var) has no inner Not, so stays as Not(var)
        assert_eq!(push_negations(&!BoolExpr::Var(BoolVar(0))), !BoolExpr::Var(BoolVar(0)));
    }

    #[test]
    fn push_negations_double_not_eliminates() {
        // Not(Not(x)) => x
        assert_eq!(push_negations(&!(!BoolExpr::Var(BoolVar(0)))), BoolExpr::Var(BoolVar(0)));
    }

    #[test]
    fn push_negations_triple_not() {
        // Not(Not(Not(x))) => Not(x)
        assert_eq!(push_negations(&!(!(!BoolExpr::Var(BoolVar(0))))), !BoolExpr::Var(BoolVar(0)));
    }

    #[test]
    fn push_negations_recurses_into_and() {
        let expr = !(!BoolExpr::Var(BoolVar(0))) & !(!BoolExpr::Var(BoolVar(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn push_negations_recurses_into_or() {
        let expr = !(!BoolExpr::Var(BoolVar(0))) | BoolExpr::Var(BoolVar(1));
        assert_eq!(push_negations(&expr), BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn push_negations_not_and_demorgan() {
        // Not(And(a, b)) => Or(Not(a), Not(b))
        let expr = !(BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1)));
        assert_eq!(push_negations(&expr), !BoolExpr::Var(BoolVar(0)) | !BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn push_negations_not_or_demorgan() {
        // Not(Or(a, b)) => And(Not(a), Not(b))
        let expr = !(BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1)));
        assert_eq!(push_negations(&expr), !BoolExpr::Var(BoolVar(0)) & !BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn push_negations_not_lt_becomes_ge() {
        let expr = !BoolExpr::Lt(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Ge(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))));
    }

    #[test]
    fn push_negations_not_le_becomes_gt() {
        let expr = !BoolExpr::Le(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Gt(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))));
    }

    #[test]
    fn push_negations_not_ge_becomes_lt() {
        let expr = !BoolExpr::Ge(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Lt(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))));
    }

    #[test]
    fn push_negations_not_gt_becomes_le() {
        let expr = !BoolExpr::Gt(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Le(ArithExpr::IntVar(IntVar(0)), ArithExpr::IntVar(IntVar(1))));
    }

    #[test]
    fn push_negations_not_eq_stays_not_eq() {
        let inner = BoolExpr::Eq(Box::new(Expr::Bool(BoolExpr::Var(BoolVar(0)))), Box::new(Expr::Bool(BoolExpr::Var(BoolVar(1)))));
        let expr = !inner.clone();
        assert_eq!(push_negations(&expr), !inner);
    }

    // --- distribute ---

    #[test]
    fn distribute_atom_unchanged() {
        assert_eq!(distribute(&BoolExpr::Var(BoolVar(0))), BoolExpr::Var(BoolVar(0)));
        assert_eq!(distribute(&BoolExpr::True), BoolExpr::True);
    }

    #[test]
    fn distribute_and_of_atoms() {
        let expr = BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1));
        assert_eq!(distribute(&expr), BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn distribute_or_of_atoms() {
        let expr = BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1));
        // Or(a, b) with no And inside stays as-is (wrapped in And with one element, unwrapped)
        assert_eq!(distribute(&expr), BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn distribute_or_over_and() {
        // Or(a, And(b, c)) => And(Or(a, b), Or(a, c))
        let expr = BoolExpr::Var(BoolVar(0)) | (BoolExpr::Var(BoolVar(1)) & BoolExpr::Var(BoolVar(2)));
        let expected = (BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1))) & (BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(2)));
        assert_eq!(distribute(&expr), expected);
    }

    #[test]
    fn distribute_flattens_nested_or() {
        // Or(Or(a, b), c) => Or(a, b, c)
        let expr = (BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1))) | BoolExpr::Var(BoolVar(2));
        assert_eq!(distribute(&expr), BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1)) | BoolExpr::Var(BoolVar(2)));
    }

    #[test]
    fn distribute_flattens_nested_and() {
        // And(And(a, b), c) => And(a, b, c)
        let expr = BoolExpr::Var(BoolVar(0)) & (BoolExpr::Var(BoolVar(1)) & BoolExpr::Var(BoolVar(2)));
        assert_eq!(distribute(&expr), BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1)) & BoolExpr::Var(BoolVar(2)));
    }

    #[test]
    fn distribute_and_inside_and_flattened() {
        let expr = BoolExpr::Var(BoolVar(0)) & (BoolExpr::Var(BoolVar(1)) & BoolExpr::Var(BoolVar(2)));
        assert_eq!(distribute(&expr), BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1)) & BoolExpr::Var(BoolVar(2)));
    }

    #[test]
    fn distribute_cartesian_product_two_ands() {
        // Or(And(a, b), And(c, d)) => And(Or(a,c), Or(a,d), Or(b,c), Or(b,d))
        let expr = (BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1))) | (BoolExpr::Var(BoolVar(2)) & BoolExpr::Var(BoolVar(3)));
        let result = distribute(&expr);
        // Should be an And of four Or clauses
        if let BoolExpr::And(clauses) = result {
            assert_eq!(clauses.len(), 4);
            for clause in &clauses {
                assert!(matches!(clause, BoolExpr::Or(_)));
            }
        } else {
            panic!("expected And");
        }
    }

    // --- to_cnf ---

    #[test]
    fn to_cnf_atom_unchanged() {
        assert_eq!(to_cnf(&BoolExpr::Var(BoolVar(0))), BoolExpr::Var(BoolVar(0)));
    }

    #[test]
    fn to_cnf_already_cnf() {
        // And(Or(a, b), Or(c, d)) is already CNF
        let expr = (BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1))) & (BoolExpr::Var(BoolVar(2)) | BoolExpr::Var(BoolVar(3)));
        assert_eq!(to_cnf(&expr), expr);
    }

    #[test]
    fn to_cnf_double_negation() {
        assert_eq!(to_cnf(&!(!BoolExpr::Var(BoolVar(0)))), BoolExpr::Var(BoolVar(0)));
    }

    #[test]
    fn to_cnf_not_and_demorgan_then_distribute() {
        // Not(And(a, b)) => Or(Not(a), Not(b)) — already a single clause
        let expr = !(BoolExpr::Var(BoolVar(0)) & BoolExpr::Var(BoolVar(1)));
        assert_eq!(to_cnf(&expr), !BoolExpr::Var(BoolVar(0)) | !BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn to_cnf_not_or_demorgan() {
        // Not(Or(a, b)) => And(Not(a), Not(b))
        let expr = !(BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1)));
        assert_eq!(to_cnf(&expr), !BoolExpr::Var(BoolVar(0)) & !BoolExpr::Var(BoolVar(1)));
    }

    #[test]
    fn to_cnf_or_over_and_distributes() {
        // Or(a, And(b, c)) => And(Or(a, b), Or(a, c))
        let expr = BoolExpr::Var(BoolVar(0)) | (BoolExpr::Var(BoolVar(1)) & BoolExpr::Var(BoolVar(2)));
        let expected = (BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(1))) & (BoolExpr::Var(BoolVar(0)) | BoolExpr::Var(BoolVar(2)));
        assert_eq!(to_cnf(&expr), expected);
    }

    #[test]
    fn to_cnf_not_comparison_flipped() {
        assert_eq!(to_cnf(&!(BoolExpr::Lt(ArithExpr::from(0), ArithExpr::from(1)))), BoolExpr::Ge(ArithExpr::from(0), ArithExpr::from(1)));
        assert_eq!(to_cnf(&!(BoolExpr::Ge(ArithExpr::from(0), ArithExpr::from(1)))), BoolExpr::Lt(ArithExpr::from(0), ArithExpr::from(1)));
    }

    #[test]
    fn to_cnf_nested_not_and_or() {
        // Not(Or(And(a,b), c)) => And(Or(Not(a), Not(c)), Or(Not(b), Not(c)))
        let expr = !(BoolExpr::Var(BoolVar(0)) | (BoolExpr::Var(BoolVar(1)) & BoolExpr::Var(BoolVar(2))));
        // push_negations: And(Or(Not(a), Not(b)), Not(c))
        // distribute: And of Or(Not(a),Not(b)) and Not(c) — already flat
        let result = to_cnf(&expr);
        if let BoolExpr::And(clauses) = result {
            assert_eq!(clauses.len(), 2);
        } else {
            panic!("expected And, got: {}", result);
        }
    }
}
