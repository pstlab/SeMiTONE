use crate::{
    ast::{ArithExpr, BoolExpr, EufExpr, Expr},
    rational::Rational,
    solver::Solver,
};
use num_traits::ToPrimitive;
use rustc_hash::{FxHashMap, FxHashSet};
use smt2parser::{CommandStream, concrete};
use std::{
    fs::File,
    io::{BufReader, Write},
};

/// SMT-LIB parser built on top of the solver.
///
/// It reads commands from a string or file and writes SAT/UNSAT responses to the
/// configured output sink.
pub struct SmtParser<'a> {
    pub solver: Solver,
    bool_vars: FxHashMap<String, BoolExpr>,
    arith_vars: FxHashMap<String, ArithExpr>,
    euf_vars: FxHashMap<String, EufExpr>,
    euf_funcs: FxHashMap<String, usize>,
    custom_sorts: FxHashSet<String>,
    var_sorts: FxHashMap<String, String>,
    purified_bool_vars: Vec<(EufExpr, BoolExpr)>,
    purified_arith_vars: Vec<(EufExpr, ArithExpr, String)>,
    is_unsat: bool,
    writer: &'a mut dyn Write,
}

impl<'a> SmtParser<'a> {
    /// Creates a parser that writes the SMT response stream to the given writer.
    pub fn new(writer: &'a mut dyn Write) -> Self {
        Self {
            solver: Solver::new(),
            bool_vars: FxHashMap::default(),
            arith_vars: FxHashMap::default(),
            euf_vars: FxHashMap::default(),
            euf_funcs: FxHashMap::default(),
            custom_sorts: FxHashSet::default(),
            var_sorts: FxHashMap::default(),
            purified_bool_vars: Vec::new(),
            purified_arith_vars: Vec::new(),
            is_unsat: false,
            writer,
        }
    }

    /// Parses and executes a full SMT-LIB script from an in-memory string.
    pub fn run_str(&mut self, script: &str) {
        use std::io::Cursor;

        let cursor = Cursor::new(script);
        let reader = std::io::BufReader::new(cursor);
        let stream = smt2parser::CommandStream::new(reader, smt2parser::concrete::SyntaxBuilder, None);

        for command in stream {
            match command {
                Ok(cmd) => self.execute_command(cmd),
                Err(e) => eprintln!("Parser error: {:?}", e),
            }
        }
    }

    /// Parses and executes an SMT-LIB file from disk.
    pub fn run_file(&mut self, path: &str) {
        let file = File::open(path).expect("Failed to open SMT-LIB file");
        let reader = BufReader::new(file);
        let stream = CommandStream::new(reader, concrete::SyntaxBuilder, None);

        for command in stream {
            match command {
                Ok(cmd) => self.execute_command(cmd),
                Err(e) => eprintln!("Parser error: {:?}", e),
            }
        }
    }

    fn execute_command(&mut self, cmd: concrete::Command) {
        match cmd {
            concrete::Command::SetLogic { symbol } => {
                let supported_logics = ["QF_LRA", "QF_LIA", "QF_UF", "QF_UFLRA", "QF_UFLIA", "QF_UFLIRA"];
                if !supported_logics.contains(&symbol.0.as_str()) {
                    println!("Warning: Logic '{}' might not be fully supported by SeMiTONE yet.", symbol.0);
                }
            }
            concrete::Command::DeclareSort { symbol, arity } => {
                if arity.to_usize() != Some(0) {
                    panic!("Parametric sorts are not supported yet.");
                }
                self.custom_sorts.insert(symbol.0.clone());
            }
            concrete::Command::DeclareFun { symbol, parameters, sort, .. } => {
                let name = symbol.0;
                let sort_name = match sort {
                    concrete::Sort::Simple { identifier } => Self::symbol_of_identifier(&identifier).to_string(),
                    _ => panic!("Complex sorts are not supported yet"),
                };

                if parameters.is_empty() {
                    match sort_name.as_str() {
                        "Bool" => {
                            let v = self.solver.smt.new_bool();
                            self.bool_vars.insert(name.clone(), v);
                        }
                        "Real" => {
                            let v = self.solver.smt.new_real();
                            self.arith_vars.insert(name.clone(), v);
                            self.var_sorts.insert(name, "Real".to_string());
                        }
                        "Int" => {
                            let v = self.solver.smt.new_int();
                            self.arith_vars.insert(name.clone(), v);
                            self.var_sorts.insert(name, "Int".to_string());
                        }
                        _ if self.custom_sorts.contains(&sort_name) => {
                            let v = self.solver.smt.new_euf_var();
                            self.euf_vars.insert(name.to_string(), v);
                        }
                        _ => panic!("Unsupported sort: {}", sort_name),
                    }
                } else {
                    let func_id = self.euf_funcs.len();
                    self.euf_funcs.insert(name, func_id);
                }
            }
            concrete::Command::Assert { term } => {
                if self.is_unsat {
                    return; // Skip further assertions if already trivially unsat
                }

                let bool_expr = self.translate_bool_term(&term);
                if !self.solver.smt.assert(&bool_expr) {
                    self.is_unsat = true;
                }
            }
            concrete::Command::CheckSat => {
                if self.is_unsat {
                    writeln!(self.writer, "unsat").unwrap();
                } else {
                    match self.solver.check_sat() {
                        Some(true) => writeln!(self.writer, "sat").unwrap(),
                        Some(false) => writeln!(self.writer, "unsat").unwrap(),
                        None => writeln!(self.writer, "unknown").unwrap(),
                    }
                }
            }
            concrete::Command::GetModel => {
                if self.is_unsat {
                    writeln!(self.writer, "(error \"get-model is only available after a successful check-sat\")").unwrap();
                    return;
                }

                writeln!(self.writer, "(").unwrap();

                // Print Boolean assignments
                for (name, var) in &self.bool_vars {
                    if let Some(val) = self.solver.smt.get_bool_val(var) {
                        writeln!(self.writer, "  (define-fun {} () Bool {})", name, if val { "true" } else { "false" }).unwrap();
                    }
                }

                // Print Real/Integer assignments
                for (name, var) in &self.arith_vars {
                    if let Some(val) = self.solver.smt.get_arith_val(var) {
                        let Rational::Finite(rat) = val.rational_part() else {
                            writeln!(self.writer, "  (define-fun {} () Real <non-finite>)", name).unwrap();
                            continue;
                        };
                        let num = rat.numer();
                        let den = rat.denom();

                        // Format as decimal if the denominator is 1, otherwise as an SMT-LIB division
                        if den == &rug::Integer::from(1) {
                            writeln!(self.writer, "  (define-fun {} () Real {}.0)", name, num).unwrap();
                        } else {
                            writeln!(self.writer, "  (define-fun {} () Real (/ {} {}))", name, num, den).unwrap();
                        }
                    }
                }

                writeln!(self.writer, ")").unwrap();
            }
            concrete::Command::Push { level } => {
                let n = level.to_usize().unwrap_or_else(|| panic!("push level too large for usize: {}", level));
                for _ in 0..n {
                    self.solver.smt.push();
                }
            }
            concrete::Command::Pop { level } => {
                let n = level.to_usize().unwrap_or_else(|| panic!("pop level too large for usize: {}", level));
                for _ in 0..n {
                    self.solver.smt.pop();
                }
                // Reset trivial unsat flag upon popping
                self.is_unsat = false;
            }
            _ => {} // Ignore set-info, get-model, etc. for the moment
        }
    }

    fn symbol_of_identifier(id: &concrete::Identifier) -> &str {
        match id {
            concrete::Identifier::Simple { symbol } => symbol.0.as_str(),
            concrete::Identifier::Indexed { symbol, .. } => symbol.0.as_str(),
        }
    }

    fn symbol_of_qual_identifier(qid: &concrete::QualIdentifier) -> &str {
        match qid {
            concrete::QualIdentifier::Simple { identifier } => Self::symbol_of_identifier(identifier),
            concrete::QualIdentifier::Sorted { identifier, .. } => Self::symbol_of_identifier(identifier),
        }
    }

    fn translate_bool_term(&mut self, term: &concrete::Term) -> BoolExpr {
        match term {
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                if name == "true" {
                    return BoolExpr::True;
                }
                if name == "false" {
                    return BoolExpr::False;
                }
                self.bool_vars.get(name).cloned().unwrap_or_else(|| panic!("Undeclared boolean variable: {}", name))
            }
            concrete::Term::Application { qual_identifier, arguments } => {
                let op = Self::symbol_of_qual_identifier(qual_identifier);
                match op {
                    "and" => BoolExpr::And(arguments.iter().map(|a| self.translate_bool_term(a)).collect()),
                    "or" => BoolExpr::Or(arguments.iter().map(|a| self.translate_bool_term(a)).collect()),
                    "not" => !(self.translate_bool_term(&arguments[0])),
                    "=>" => !self.translate_bool_term(&arguments[0]) | self.translate_bool_term(&arguments[1]),
                    "<=" => self.translate_arith_term(&arguments[0]).le(self.translate_arith_term(&arguments[1])),
                    ">=" => self.translate_arith_term(&arguments[0]).ge(self.translate_arith_term(&arguments[1])),
                    "<" => self.translate_arith_term(&arguments[0]).lt(self.translate_arith_term(&arguments[1])),
                    ">" => self.translate_arith_term(&arguments[0]).gt(self.translate_arith_term(&arguments[1])),
                    "=" => {
                        if self.is_bool_term(&arguments[0]) {
                            let left = self.translate_bool_term(&arguments[0]);
                            let right = self.translate_bool_term(&arguments[1]);
                            left.eq(&right)
                        } else if let concrete::Term::QualIdentifier(id) = &arguments[0] {
                            let name = Self::symbol_of_qual_identifier(id);
                            if self.euf_vars.contains_key(name) || self.euf_funcs.contains_key(name) {
                                let left = self.translate_euf_term(&arguments[0]);
                                let right = self.translate_euf_term(&arguments[1]);
                                left.eq(right)
                            } else {
                                self.translate_arith_term(&arguments[0]).eq(self.translate_arith_term(&arguments[1]))
                            }
                        } else if let concrete::Term::Application { qual_identifier, .. } = &arguments[0] {
                            let name = Self::symbol_of_qual_identifier(qual_identifier);
                            if self.euf_funcs.contains_key(name) {
                                let left = self.translate_euf_term(&arguments[0]);
                                let right = self.translate_euf_term(&arguments[1]);
                                left.eq(right)
                            } else {
                                self.translate_arith_term(&arguments[0]).eq(self.translate_arith_term(&arguments[1]))
                            }
                        } else {
                            self.translate_arith_term(&arguments[0]).eq(self.translate_arith_term(&arguments[1]))
                        }
                    }
                    _ => panic!("Unsupported boolean operator: {}", op),
                }
            }
            _ => panic!("Unsupported boolean term structure"),
        }
    }

    fn translate_arith_term(&self, term: &concrete::Term) -> ArithExpr {
        match term {
            concrete::Term::Constant(c) => match c {
                concrete::Constant::Numeral(num) => {
                    let s = num.to_string();
                    let rat = rug::Rational::from_str_radix(&s, 10).unwrap();
                    ArithExpr::Const(rat)
                }
                concrete::Constant::Decimal(dec) => {
                    let num_str = dec.numer().to_string();
                    let den_str = dec.denom().to_string();

                    let num = rug::Integer::from_str_radix(&num_str, 10).unwrap();
                    let den = rug::Integer::from_str_radix(&den_str, 10).unwrap();

                    ArithExpr::Const(rug::Rational::from((num, den)))
                }
                _ => panic!("Unsupported constant type"),
            },
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                self.arith_vars.get(name).cloned().unwrap_or_else(|| panic!("Undeclared arithmetic variable: {}", name))
            }
            concrete::Term::Application { qual_identifier, arguments } => {
                let op = Self::symbol_of_qual_identifier(qual_identifier);
                let args: Vec<_> = arguments.iter().map(|a| self.translate_arith_term(a)).collect();

                match op {
                    "+" => ArithExpr::Add(args),
                    "*" => {
                        if args.iter().all(|a| matches!(a, ArithExpr::Const(_))) {
                            let mut prod = rug::Rational::from(1);
                            for arg in args {
                                if let ArithExpr::Const(c) = arg {
                                    prod *= c;
                                }
                            }
                            ArithExpr::Const(prod)
                        } else {
                            ArithExpr::Mul(args)
                        }
                    }
                    "-" => {
                        if args.len() == 1 {
                            let arg = args.into_iter().next().unwrap();
                            if let ArithExpr::Const(c) = arg { ArithExpr::Const(-c) } else { ArithExpr::Neg(Box::new(arg)) }
                        } else {
                            // Subtraction (a - b - c) -> a + (-b) + (-c)
                            let mut iter = args.into_iter();
                            let first = iter.next().unwrap();
                            let mut sum_args = vec![first];
                            for arg in iter {
                                if let ArithExpr::Const(c) = arg {
                                    sum_args.push(ArithExpr::Const(-c));
                                } else {
                                    sum_args.push(ArithExpr::Neg(Box::new(arg)));
                                }
                            }
                            ArithExpr::Add(sum_args)
                        }
                    }
                    "/" => {
                        assert_eq!(args.len(), 2, "Division expects exactly two arguments");
                        let mut iter = args.into_iter();
                        let num = iter.next().unwrap();
                        let den = iter.next().unwrap();
                        if let (ArithExpr::Const(n), ArithExpr::Const(d)) = (&num, &den) { ArithExpr::Const(n.clone() / d) } else { ArithExpr::Div(Box::new(num), Box::new(den)) }
                    }
                    "div" | "mod" => {
                        assert_eq!(args.len(), 2, "{} expects exactly two arguments", op);
                        let mut iter = args.into_iter();
                        let num = iter.next().unwrap();
                        let den = iter.next().unwrap();

                        match (&num, &den) {
                            (ArithExpr::Const(n), ArithExpr::Const(d)) => {
                                assert!(n.denom() == &rug::Integer::from(1) && d.denom() == &rug::Integer::from(1), "div and mod are only defined for Integers");

                                let (q, r) = euclidean_div_mod(n.numer(), d.numer());

                                if op == "div" { ArithExpr::Const(rug::Rational::from((q, rug::Integer::from(1)))) } else { ArithExpr::Const(rug::Rational::from((r, rug::Integer::from(1)))) }
                            }
                            _ => {
                                unimplemented!("Non-constant div/mod is not implemented yet. Consider using a theory-aware approach for integer division and modulus.");
                            }
                        }
                    }
                    _ => panic!("Unsupported arithmetic operator: {}", op),
                }
            }
            _ => panic!("Unsupported arithmetic term structure"),
        }
    }

    fn translate_euf_term(&mut self, term: &concrete::Term) -> EufExpr {
        match term {
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                self.euf_vars.get(name).cloned().unwrap_or_else(|| panic!("Undeclared EUF variable: {}", name))
            }
            concrete::Term::Application { qual_identifier, arguments } => {
                let func_name = Self::symbol_of_qual_identifier(qual_identifier);

                if let Some(&func_id) = self.euf_funcs.get(func_name) {
                    let mut parsed_args = Vec::with_capacity(arguments.len());

                    for arg in arguments {
                        let generic_expr = self.translate_term(arg);

                        match generic_expr {
                            Expr::Euf(euf_expr) => {
                                parsed_args.push(Expr::Euf(euf_expr));
                            }
                            Expr::Arith(arith_expr) => {
                                let fresh_euf_expr = self.solver.smt.new_euf_var();
                                let sort_type = self.infer_arith_sort(arg).to_owned();
                                let fresh_arith_expr = if sort_type == "Int" { self.solver.smt.new_int() } else { self.solver.smt.new_real() };

                                let bridge_eq = fresh_arith_expr.eq(&arith_expr);
                                self.solver.smt.assert(&bridge_eq);

                                for (old_euf, old_arith, old_sort) in &self.purified_arith_vars {
                                    if old_sort == &sort_type {
                                        let euf_eq = fresh_euf_expr.eq(old_euf.clone());
                                        let arith_eq = fresh_arith_expr.eq(old_arith);
                                        let iff_expr = euf_eq.eq(&arith_eq);
                                        self.solver.smt.assert(&iff_expr);
                                    }
                                }

                                self.purified_arith_vars.push((fresh_euf_expr.clone(), fresh_arith_expr, sort_type.to_string()));

                                parsed_args.push(Expr::Euf(fresh_euf_expr));
                            }
                            Expr::Bool(bool_expr) => {
                                let fresh_euf_expr = self.solver.smt.new_euf_var();
                                let fresh_bool_expr = self.solver.smt.new_bool();

                                let bridge_eq = fresh_bool_expr.eq(&bool_expr);
                                self.solver.smt.assert(&bridge_eq);

                                for (old_euf, old_bool) in &self.purified_bool_vars {
                                    let euf_eq = fresh_euf_expr.eq(old_euf.clone());
                                    let bool_eq = fresh_bool_expr.eq(old_bool);
                                    let iff_expr = euf_eq.eq(&bool_eq);
                                    self.solver.smt.assert(&iff_expr);
                                }

                                self.purified_bool_vars.push((fresh_euf_expr.clone(), fresh_bool_expr));

                                parsed_args.push(Expr::Euf(fresh_euf_expr));
                            }
                            _ => panic!("Unsupported argument type for EUF function: {:?}", generic_expr),
                        }
                    }

                    self.solver.smt.new_euf_app(func_id, parsed_args)
                } else {
                    panic!("Unknown function: {}", func_name);
                }
            }
            _ => panic!("Unsupported EUF term structure"),
        }
    }

    fn translate_term(&mut self, term: &concrete::Term) -> Expr {
        if self.is_bool_term(term) {
            Expr::Bool(self.translate_bool_term(term))
        } else if self.is_arith_term(term) {
            Expr::Arith(self.translate_arith_term(term))
        } else if self.is_euf_term(term) {
            Expr::Euf(self.translate_euf_term(term))
        } else {
            panic!("Termine misto o sconosciuto non identificabile")
        }
    }

    /// Helper function to dynamically infer the sort of a term for overloaded operators like `=`
    fn is_bool_term(&self, term: &concrete::Term) -> bool {
        match term {
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                name == "true" || name == "false" || self.bool_vars.contains_key(name)
            }
            concrete::Term::Application { qual_identifier, .. } => {
                let op = Self::symbol_of_qual_identifier(qual_identifier);
                matches!(op, "and" | "or" | "not" | "=>" | "<=" | ">=" | "<" | ">" | "=")
            }
            _ => false,
        }
    }

    fn is_arith_term(&self, term: &concrete::Term) -> bool {
        match term {
            concrete::Term::Constant(c) => matches!(c, concrete::Constant::Numeral(_) | concrete::Constant::Decimal(_)),
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                self.arith_vars.contains_key(name)
            }
            concrete::Term::Application { qual_identifier, .. } => {
                let op = Self::symbol_of_qual_identifier(qual_identifier);
                matches!(op, "+" | "-" | "*" | "/")
            }
            _ => false,
        }
    }

    fn is_euf_term(&self, term: &concrete::Term) -> bool {
        match term {
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                self.euf_vars.contains_key(name)
            }
            concrete::Term::Application { qual_identifier, .. } => {
                let func_name = Self::symbol_of_qual_identifier(qual_identifier);
                self.euf_funcs.contains_key(func_name)
            }
            _ => false,
        }
    }

    fn infer_arith_sort(&self, term: &concrete::Term) -> &str {
        match term {
            concrete::Term::Constant(c) => match c {
                concrete::Constant::Numeral(_) => "Int",
                concrete::Constant::Decimal(_) => "Real",
                _ => panic!("Unsupported constant type for sort inference"),
            },
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                self.var_sorts.get(name).map(|s| s.as_str()).unwrap_or_else(|| panic!("Undeclared variable for sort inference: {}", name))
            }
            concrete::Term::Application { arguments, .. } => {
                if let Some(first_arg) = arguments.first() {
                    self.infer_arith_sort(first_arg)
                } else {
                    panic!("Cannot infer sort from empty application")
                }
            }
            _ => panic!("Unsupported term structure for sort inference"),
        }
    }
}

fn euclidean_div_mod(a: &rug::Integer, b: &rug::Integer) -> (rug::Integer, rug::Integer) {
    if *b == 0 {
        panic!("Division by zero in constant evaluation");
    }

    let mut q = a.clone() / b;
    let mut r = a.clone() % b;

    if r < 0 {
        if *b > 0 {
            q -= 1;
            r += b;
        } else {
            q += 1;
            r -= b;
        }
    }

    (q, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_smt_script(script: &str) -> String {
        let mut output = Vec::new();
        {
            let mut parser = SmtParser::new(&mut output);
            parser.run_str(script);
        }
        String::from_utf8(output).expect("Invalid UTF-8 output")
    }

    #[test]
    fn test_euf_congruence() {
        let script = "
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun f (U) U)
            
            (assert (= a b))
            (assert (not (= (f a) (f b))))
            (check-sat)
        ";
        let output = run_smt_script(script);
        assert_eq!(output.trim(), "unsat", "The congruence f(a)=f(b) must be guaranteed");
    }

    #[test]
    fn test_euf_transitivity() {
        let script = "
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun c () U)
            
            (assert (= a b))
            (assert (= b c))
            (assert (not (= a c)))
            (check-sat)
        ";
        let output = run_smt_script(script);
        assert_eq!(output.trim(), "unsat", "Transitivity of a=b and b=c implies a=c");
    }

    #[test]
    fn test_euf_satisfiable_and_model() {
        let script = "
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun x () U)
            (declare-fun y () U)
            
            (assert (not (= x y)))
            (check-sat)
        ";
        let output = run_smt_script(script);
        assert!(output.contains("sat"), "The system should be satisfiable");
    }

    #[test]
    fn test_euf_push_pop_backtracking() {
        let script = "
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun f (U) U)
            
            (push 1)
                (assert (= a b))
                (assert (not (= (f a) (f b))))
                (check-sat) ; This must be unsat
            (pop 1)
            
            (push 1)
                (assert (= a b))
                (assert (= (f a) (f b)))
                (check-sat) ; This must be sat now that the conflict has been popped
            (pop 1)
        ";
        let output = run_smt_script(script);
        let lines: Vec<&str> = output.trim().lines().collect();
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0].trim(), "unsat");
        assert_eq!(lines[1].trim(), "sat");
    }
    #[test]

    fn test_euf_arith_mixed_vars() {
        let script = "
            (set-logic QF_UFLIA)
            (declare-sort U 0)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun f (Int) U)
            
            (assert (= x y))
            (assert (not (= (f x) (f y))))
            (check-sat)
        ";
        assert_eq!(run_smt_script(script).trim(), "unsat");
    }

    #[test]
    fn test_euf_arith_mixed_complex_flattening() {
        let script = "
            (set-logic QF_UFLIA)
            (declare-sort U 0)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun f (Int) U)
            
            (assert (= x 2))
            (assert (= y 4))
            
            ; (+ x 1) fa 3. (- y 1) fa 3. La disuguaglianza è un assurdo.
            (assert (not (= (f (+ x 1)) (f (- y 1)))))
            (check-sat)
        ";
        assert_eq!(run_smt_script(script).trim(), "unsat");
    }

    #[test]
    fn test_euf_bool_mixed_flattening() {
        let script = "
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun f (Bool) U)
            
            ; p e q sono entrambi veri
            (assert p)
            (assert q)
            
            ; Se sono entrambi veri, p == q. Quindi f(p) deve essere uguale a f(q).
            (assert (not (= (f p) (f q))))
            (check-sat)
        ";
        assert_eq!(run_smt_script(script).trim(), "unsat");
    }

    #[test]
    fn test_mixed_satisfiable_model() {
        let script = "
            (set-logic QF_UFLIA)
            (declare-sort U 0)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun f (Int) U)
            
            (assert (= x 2))
            (assert (= y 3))
            (assert (not (= (f x) (f y))))
            (check-sat)
        ";
        assert!(run_smt_script(script).contains("sat"));
    }

    #[test]
    fn test_diophantine_equation_unsat() {
        let script = "
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (declare-fun y () Int)
            
            ; 3x + y = 7
            (assert (= y (- 7 (* 3 x))))
            (check-sat)
        ";
        assert_eq!(run_smt_script(script).trim(), "sat", "There are integer solutions to 3x + y = 7");
    }

    #[test]
    fn test_diophantine_equation_unsat_example() {
        let script = "
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (declare-fun y () Int)

            ; 3x + y = 7
            (assert (= y (- 7 (* 3 x))))
            ; 3x + y = 8
            (assert (= y (- 8 (* 3 x))))
            (check-sat)
        ";
        assert_eq!(run_smt_script(script).trim(), "unsat", "There are no integer solutions to the system 3x + y = 7 and 3x + y = 8");
    }

    #[test]
    fn test_complex_mixed_sat() {
        let script = "
            (set-logic QF_UFLIRA)
            (declare-sort U 0)
            (declare-fun v_0 () Bool)
            (declare-fun v_1 () Int)
            (declare-fun v_2 () Real)
            (declare-fun v_3 () U)
            (declare-fun v_4 () Int)
            (declare-fun v_5 () U)
            (declare-fun v_6 () Int)
            (declare-fun v_7 () U)
            (declare-fun v_8 () Int)
            (declare-fun v_9 () Bool)
            (declare-fun f_pure (U) U)
            (declare-fun f_mix_int (Int) U)
            (declare-fun f_mix_bool (Bool) U)
            (assert (=> (not v_0) v_9))
            (assert (or (= (- v_1 v_8) (- v_8 (- 9))) (= (f_mix_int (- 2)) v_7)))
            (assert (not (= v_2 (+ v_2 v_2))))
            (assert (or v_9 (and (=> true v_0) (=> v_0 v_0))))
            (assert v_0)
            (assert (and (not (and true v_9)) true))
            (assert (= (- 5 (+ (- 10) v_6)) (+ (* v_1 3) 8)))
            (assert (and (not (= (- 3) (- 7))) (not (= 5.0 v_2))))
            (assert (and (not v_9) v_0))
            (assert v_0)
            (assert (= 5.0 (* v_2 (- 8.0))))
            (assert v_0)
            (assert (or false v_0))
            (assert true)
            (assert (=> (not (or true v_0)) (and v_0 (=> false v_0))))
            (check-sat)
        ";
        assert_eq!(run_smt_script(script).trim(), "sat", "The complex mixed system should be satisfiable");
    }
}
