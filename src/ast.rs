use std::{fmt, ops};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Bool(BoolExpr),
    Enum(EnumExpr),
    Arith(ArithExpr),
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Expr::Bool(BoolExpr::from(b))
    }
}

impl From<rug::Rational> for Expr {
    fn from(r: rug::Rational) -> Self {
        Expr::Arith(ArithExpr::from(r))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Enum(e) => write!(f, "{}", e),
            Expr::Arith(a) => write!(f, "{}", a),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoolExpr {
    True,
    False,
    Var(usize),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Lt(ArithExpr, ArithExpr),
    Le(ArithExpr, ArithExpr),
    Ge(ArithExpr, ArithExpr),
    Gt(ArithExpr, ArithExpr),
    Eq(Box<Expr>, Box<Expr>),
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

impl fmt::Display for BoolExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoolExpr::True => write!(f, "true"),
            BoolExpr::False => write!(f, "false"),
            BoolExpr::Var(v) => write!(f, "b{}", v),
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
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EnumExpr {
    Var(usize),
    Const(i32),
}

impl fmt::Display for EnumExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EnumExpr::Var(n) => write!(f, "e{}", n),
            EnumExpr::Const(n) => write!(f, "#{}", n),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArithExpr {
    Const(rug::Rational),
    IntVar(usize),
    RealVar(usize),
    Add(Vec<ArithExpr>),
    Mul(Vec<ArithExpr>),
    Div(Box<ArithExpr>, Box<ArithExpr>),
    Neg(Box<ArithExpr>),
}

impl From<i32> for ArithExpr {
    fn from(n: i32) -> Self {
        ArithExpr::Const(rug::Rational::from(n))
    }
}

impl From<rug::Rational> for ArithExpr {
    fn from(r: rug::Rational) -> Self {
        ArithExpr::Const(r)
    }
}

impl ops::Neg for ArithExpr {
    type Output = Self;

    fn neg(self) -> Self {
        ArithExpr::Neg(Box::new(self))
    }
}

impl fmt::Display for ArithExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArithExpr::Const(r) => write!(f, "{}", r),
            ArithExpr::IntVar(n) => write!(f, "i{}", n),
            ArithExpr::RealVar(n) => write!(f, "r{}", n),
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

pub fn to_cnf(expr: &BoolExpr) -> BoolExpr {
    distribute(&push_negations(expr))
}

pub fn cst_arith(val: i32) -> ArithExpr {
    ArithExpr::Const(rug::Rational::from(val))
}
pub fn cst_frac(num: i32, denom: i32) -> ArithExpr {
    ArithExpr::Const(rug::Rational::from((num, denom)))
}
pub fn cst_enum(val: i32) -> EnumExpr {
    EnumExpr::Const(val)
}
pub fn and(es: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
    BoolExpr::And(es.into_iter().collect())
}
pub fn or(es: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
    BoolExpr::Or(es.into_iter().collect())
}
pub fn add(es: impl IntoIterator<Item = ArithExpr>) -> ArithExpr {
    ArithExpr::Add(es.into_iter().collect())
}
pub fn mul(es: impl IntoIterator<Item = ArithExpr>) -> ArithExpr {
    ArithExpr::Mul(es.into_iter().collect())
}
pub fn lt(e1: ArithExpr, e2: ArithExpr) -> BoolExpr {
    BoolExpr::Lt(e1, e2)
}
pub fn le(e1: ArithExpr, e2: ArithExpr) -> BoolExpr {
    BoolExpr::Le(e1, e2)
}
pub fn eq(e1: Expr, e2: Expr) -> BoolExpr {
    BoolExpr::Eq(Box::new(e1), Box::new(e2))
}
pub fn eq_arith(e1: ArithExpr, e2: ArithExpr) -> BoolExpr {
    BoolExpr::Eq(Box::new(Expr::Arith(e1)), Box::new(Expr::Arith(e2)))
}
pub fn eq_enum(e1: EnumExpr, e2: EnumExpr) -> BoolExpr {
    BoolExpr::Eq(Box::new(Expr::Enum(e1)), Box::new(Expr::Enum(e2)))
}
pub fn ge(e1: ArithExpr, e2: ArithExpr) -> BoolExpr {
    BoolExpr::Ge(e1, e2)
}
pub fn gt(e1: ArithExpr, e2: ArithExpr) -> BoolExpr {
    BoolExpr::Gt(e1, e2)
}
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
        assert_eq!(BoolExpr::Var(3).to_string(), "b3");
    }

    #[test]
    fn bool_display_not() {
        assert_eq!((!BoolExpr::Var(0)).to_string(), "¬b0");
    }

    #[test]
    fn bool_display_and() {
        assert_eq!(and([BoolExpr::Var(0), BoolExpr::Var(1)]).to_string(), "(b0 ∧ b1)");
    }

    #[test]
    fn bool_display_or() {
        assert_eq!(or([BoolExpr::Var(0), BoolExpr::Var(1)]).to_string(), "(b0 ∨ b1)");
    }

    #[test]
    fn bool_display_comparisons() {
        assert_eq!(BoolExpr::Lt(ArithExpr::IntVar(0), ArithExpr::IntVar(1)).to_string(), "i0 < i1");
        assert_eq!(BoolExpr::Le(ArithExpr::IntVar(0), ArithExpr::IntVar(1)).to_string(), "i0 ≤ i1");
        assert_eq!(BoolExpr::Ge(ArithExpr::IntVar(0), ArithExpr::IntVar(1)).to_string(), "i0 ≥ i1");
        assert_eq!(BoolExpr::Gt(ArithExpr::IntVar(0), ArithExpr::IntVar(1)).to_string(), "i0 > i1");
    }

    #[test]
    fn bool_display_eq() {
        let e = BoolExpr::Eq(Box::new(Expr::Bool(BoolExpr::Var(0))), Box::new(Expr::Bool(BoolExpr::Var(1))));
        assert_eq!(e.to_string(), "b0 = b1");
    }

    // --- ArithExpr Display ---

    #[test]
    fn arith_display_lit() {
        assert_eq!(ArithExpr::Const(rug::Rational::from(5)).to_string(), "5");
    }

    #[test]
    fn arith_display_int_real() {
        assert_eq!(ArithExpr::IntVar(2).to_string(), "i2");
        assert_eq!(ArithExpr::RealVar(5).to_string(), "r5");
    }

    #[test]
    fn arith_display_add() {
        let e = add([ArithExpr::IntVar(0), ArithExpr::IntVar(1)]);
        assert_eq!(e.to_string(), "(i0 + i1)");
    }

    #[test]
    fn arith_display_sub() {
        let e = add([ArithExpr::IntVar(0), ArithExpr::Neg(Box::new(ArithExpr::IntVar(1)))]);
        assert_eq!(e.to_string(), "(i0 - i1)");
    }

    #[test]
    fn arith_display_mul() {
        let e = mul([ArithExpr::IntVar(0), ArithExpr::IntVar(1)]);
        assert_eq!(e.to_string(), "(i0 * i1)");
    }

    #[test]
    fn arith_display_div() {
        let e = ArithExpr::Div(Box::new(ArithExpr::IntVar(0)), Box::new(ArithExpr::IntVar(1)));
        assert_eq!(e.to_string(), "(i0 / i1)");
    }

    // --- push_negations ---

    #[test]
    fn push_negations_literal_unchanged() {
        assert_eq!(push_negations(&BoolExpr::True), BoolExpr::True);
    }

    #[test]
    fn push_negations_var_unchanged() {
        assert_eq!(push_negations(&BoolExpr::Var(0)), BoolExpr::Var(0));
    }

    #[test]
    fn push_negations_not_var_becomes_not_var() {
        // Not(var) has no inner Not, so stays as Not(var)
        assert_eq!(push_negations(&!BoolExpr::Var(0)), !BoolExpr::Var(0));
    }

    #[test]
    fn push_negations_double_not_eliminates() {
        // Not(Not(x)) => x
        assert_eq!(push_negations(&!(!BoolExpr::Var(0))), BoolExpr::Var(0));
    }

    #[test]
    fn push_negations_triple_not() {
        // Not(Not(Not(x))) => Not(x)
        assert_eq!(push_negations(&!(!(!BoolExpr::Var(0)))), !BoolExpr::Var(0));
    }

    #[test]
    fn push_negations_recurses_into_and() {
        let expr = and([!(!BoolExpr::Var(0)), !(!BoolExpr::Var(1))]);
        assert_eq!(push_negations(&expr), and([BoolExpr::Var(0), BoolExpr::Var(1)]));
    }

    #[test]
    fn push_negations_recurses_into_or() {
        let expr = or([!(!BoolExpr::Var(0)), BoolExpr::Var(1)]);
        assert_eq!(push_negations(&expr), or([BoolExpr::Var(0), BoolExpr::Var(1)]));
    }

    #[test]
    fn push_negations_not_and_demorgan() {
        // Not(And(a, b)) => Or(Not(a), Not(b))
        let expr = !and([BoolExpr::Var(0), BoolExpr::Var(1)]);
        assert_eq!(push_negations(&expr), or([!BoolExpr::Var(0), !BoolExpr::Var(1)]));
    }

    #[test]
    fn push_negations_not_or_demorgan() {
        // Not(Or(a, b)) => And(Not(a), Not(b))
        let expr = !or([BoolExpr::Var(0), BoolExpr::Var(1)]);
        assert_eq!(push_negations(&expr), and([!BoolExpr::Var(0), !BoolExpr::Var(1)]));
    }

    #[test]
    fn push_negations_not_lt_becomes_ge() {
        let expr = !BoolExpr::Lt(ArithExpr::IntVar(0), ArithExpr::IntVar(1));
        assert_eq!(push_negations(&expr), BoolExpr::Ge(ArithExpr::IntVar(0), ArithExpr::IntVar(1)));
    }

    #[test]
    fn push_negations_not_le_becomes_gt() {
        let expr = !BoolExpr::Le(ArithExpr::IntVar(0), ArithExpr::IntVar(1));
        assert_eq!(push_negations(&expr), BoolExpr::Gt(ArithExpr::IntVar(0), ArithExpr::IntVar(1)));
    }

    #[test]
    fn push_negations_not_ge_becomes_lt() {
        let expr = !BoolExpr::Ge(ArithExpr::IntVar(0), ArithExpr::IntVar(1));
        assert_eq!(push_negations(&expr), BoolExpr::Lt(ArithExpr::IntVar(0), ArithExpr::IntVar(1)));
    }

    #[test]
    fn push_negations_not_gt_becomes_le() {
        let expr = !BoolExpr::Gt(ArithExpr::IntVar(0), ArithExpr::IntVar(1));
        assert_eq!(push_negations(&expr), BoolExpr::Le(ArithExpr::IntVar(0), ArithExpr::IntVar(1)));
    }

    #[test]
    fn push_negations_not_eq_stays_not_eq() {
        let inner = BoolExpr::Eq(Box::new(Expr::Bool(BoolExpr::Var(0))), Box::new(Expr::Bool(BoolExpr::Var(1))));
        let expr = !inner.clone();
        assert_eq!(push_negations(&expr), !inner);
    }

    // --- distribute ---

    #[test]
    fn distribute_atom_unchanged() {
        assert_eq!(distribute(&BoolExpr::Var(0)), BoolExpr::Var(0));
        assert_eq!(distribute(&BoolExpr::True), BoolExpr::True);
    }

    #[test]
    fn distribute_and_of_atoms() {
        let expr = and([BoolExpr::Var(0), BoolExpr::Var(1)]);
        assert_eq!(distribute(&expr), and([BoolExpr::Var(0), BoolExpr::Var(1)]));
    }

    #[test]
    fn distribute_or_of_atoms() {
        let expr = or([BoolExpr::Var(0), BoolExpr::Var(1)]);
        // Or(a, b) with no And inside stays as-is (wrapped in And with one element, unwrapped)
        assert_eq!(distribute(&expr), or([BoolExpr::Var(0), BoolExpr::Var(1)]));
    }

    #[test]
    fn distribute_or_over_and() {
        // Or(a, And(b, c)) => And(Or(a, b), Or(a, c))
        let expr = or([BoolExpr::Var(0), and([BoolExpr::Var(1), BoolExpr::Var(2)])]);
        let expected = and([or([BoolExpr::Var(0), BoolExpr::Var(1)]), or([BoolExpr::Var(0), BoolExpr::Var(2)])]);
        assert_eq!(distribute(&expr), expected);
    }

    #[test]
    fn distribute_flattens_nested_or() {
        // Or(Or(a, b), c) => Or(a, b, c)
        let expr = or([or([BoolExpr::Var(0), BoolExpr::Var(1)]), BoolExpr::Var(2)]);
        assert_eq!(distribute(&expr), or([BoolExpr::Var(0), BoolExpr::Var(1), BoolExpr::Var(2)]));
    }

    #[test]
    fn distribute_flattens_nested_and() {
        // And(And(a, b), c) => And(a, b, c)
        let expr = and([and([BoolExpr::Var(0), BoolExpr::Var(1)]), BoolExpr::Var(2)]);
        assert_eq!(distribute(&expr), and([BoolExpr::Var(0), BoolExpr::Var(1), BoolExpr::Var(2)]));
    }

    #[test]
    fn distribute_and_inside_and_flattened() {
        let expr = and([BoolExpr::Var(0), and([BoolExpr::Var(1), BoolExpr::Var(2)])]);
        assert_eq!(distribute(&expr), and([BoolExpr::Var(0), BoolExpr::Var(1), BoolExpr::Var(2)]));
    }

    #[test]
    fn distribute_cartesian_product_two_ands() {
        // Or(And(a, b), And(c, d)) => And(Or(a,c), Or(a,d), Or(b,c), Or(b,d))
        let expr = or([and([BoolExpr::Var(0), BoolExpr::Var(1)]), and([BoolExpr::Var(2), BoolExpr::Var(3)])]);
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
        assert_eq!(to_cnf(&BoolExpr::Var(0)), BoolExpr::Var(0));
    }

    #[test]
    fn to_cnf_already_cnf() {
        // And(Or(a, b), Or(c, d)) is already CNF
        let expr = and([or([BoolExpr::Var(0), BoolExpr::Var(1)]), or([BoolExpr::Var(2), BoolExpr::Var(3)])]);
        assert_eq!(to_cnf(&expr), expr);
    }

    #[test]
    fn to_cnf_double_negation() {
        assert_eq!(to_cnf(&!(!BoolExpr::Var(0))), BoolExpr::Var(0));
    }

    #[test]
    fn to_cnf_not_and_demorgan_then_distribute() {
        // Not(And(a, b)) => Or(Not(a), Not(b)) — already a single clause
        let expr = !and([BoolExpr::Var(0), BoolExpr::Var(1)]);
        assert_eq!(to_cnf(&expr), or([!BoolExpr::Var(0), !BoolExpr::Var(1)]));
    }

    #[test]
    fn to_cnf_not_or_demorgan() {
        // Not(Or(a, b)) => And(Not(a), Not(b))
        let expr = !or([BoolExpr::Var(0), BoolExpr::Var(1)]);
        assert_eq!(to_cnf(&expr), and([!BoolExpr::Var(0), !BoolExpr::Var(1)]));
    }

    #[test]
    fn to_cnf_or_over_and_distributes() {
        // Or(a, And(b, c)) => And(Or(a, b), Or(a, c))
        let expr = or([BoolExpr::Var(0), and([BoolExpr::Var(1), BoolExpr::Var(2)])]);
        let expected = and([or([BoolExpr::Var(0), BoolExpr::Var(1)]), or([BoolExpr::Var(0), BoolExpr::Var(2)])]);
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
        let expr = !(or([and([BoolExpr::Var(0), BoolExpr::Var(1)]), BoolExpr::Var(2)]));
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
