use crate::{
    SmtSolver,
    ast::{ArithExpr, BoolExpr, Expr, add, and, eq_arith, ge, gt, le, lt, mul, or},
    rational::Rational,
};
use num_traits::ToPrimitive;
use smt2parser::{CommandStream, concrete};
use std::{collections::HashMap, fs::File, io::BufReader};

pub struct SmtParser {
    pub solver: SmtSolver,
    bool_vars: HashMap<String, BoolExpr>,
    real_vars: HashMap<String, ArithExpr>,
    is_unsat: bool,
}

impl Default for SmtParser {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtParser {
    pub fn new() -> Self {
        Self {
            solver: SmtSolver::new(),
            bool_vars: HashMap::new(),
            real_vars: HashMap::new(),
            is_unsat: false,
        }
    }

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
                if symbol.0 != "QF_LRA" && symbol.0 != "QF_LIA" && symbol.0 != "QF_NRA" {
                    println!("Warning: Logic '{}' might not be fully supported by SeMiTONE yet.", symbol.0);
                }
            }
            concrete::Command::DeclareFun { symbol, sort, .. } => {
                let name = symbol.0;
                let sort_name = match sort {
                    concrete::Sort::Simple { identifier } => Self::symbol_of_identifier(&identifier).to_string(),
                    _ => panic!("Complex sorts are not supported yet"),
                };

                match sort_name.as_str() {
                    "Bool" => {
                        let v = self.solver.new_bool();
                        self.bool_vars.insert(name, v);
                    }
                    "Real" => {
                        let v = self.solver.new_real();
                        self.real_vars.insert(name, v);
                    }
                    "Int" => {
                        let v = self.solver.new_int();
                        self.real_vars.insert(name, v);
                    }
                    _ => panic!("Unsupported sort: {}", sort_name),
                }
            }
            concrete::Command::Assert { term } => {
                if self.is_unsat {
                    return; // Skip further assertions if already trivially unsat
                }

                let bool_expr = self.translate_bool_term(&term);
                if self.solver.assert(&bool_expr).is_err() {
                    self.is_unsat = true;
                }
            }
            concrete::Command::CheckSat => {
                if self.is_unsat {
                    println!("unsat");
                } else if self.solver.check_sat() {
                    println!("sat");
                } else {
                    println!("unsat");
                }
            }
            concrete::Command::GetModel => {
                if self.is_unsat {
                    println!("(error \"get-model is only available after a successful check-sat\")");
                    return;
                }

                println!("(");

                // Print Boolean assignments
                for (name, var) in &self.bool_vars {
                    if let Some(val) = self.solver.get_bool_val(var) {
                        println!("  (define-fun {} () Bool {})", name, if val { "true" } else { "false" });
                    }
                }

                // Print Real/Integer assignments
                for (name, var) in &self.real_vars {
                    if let Some(val) = self.solver.get_arith_val(var) {
                        let Rational::Finite(rat) = val.rational_part() else {
                            println!("  (define-fun {} () Real <non-finite>)", name);
                            continue;
                        };
                        let num = rat.numer();
                        let den = rat.denom();

                        // Format as decimal if the denominator is 1, otherwise as an SMT-LIB division
                        if den == &rug::Integer::from(1) {
                            println!("  (define-fun {} () Real {}.0)", name, num);
                        } else {
                            println!("  (define-fun {} () Real (/ {} {}))", name, num, den);
                        }
                    }
                }

                println!(")");
            }
            concrete::Command::Push { level } => {
                let n = level.to_usize().unwrap_or_else(|| panic!("push level too large for usize: {}", level));
                for _ in 0..n {
                    self.solver.push();
                }
            }
            concrete::Command::Pop { level } => {
                let n = level.to_usize().unwrap_or_else(|| panic!("pop level too large for usize: {}", level));
                for _ in 0..n {
                    self.solver.pop();
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

    fn translate_bool_term(&self, term: &concrete::Term) -> BoolExpr {
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
                    "and" => and(arguments.iter().map(|a| self.translate_bool_term(a))),
                    "or" => or(arguments.iter().map(|a| self.translate_bool_term(a))),
                    "not" => !(self.translate_bool_term(&arguments[0])),
                    "=>" => {
                        // A => B is equivalent to (not A) or B
                        let a = self.translate_bool_term(&arguments[0]);
                        let b = self.translate_bool_term(&arguments[1]);
                        or([!(a), b])
                    }
                    "<=" => le(self.translate_arith_term(&arguments[0]), self.translate_arith_term(&arguments[1])),
                    ">=" => ge(self.translate_arith_term(&arguments[0]), self.translate_arith_term(&arguments[1])),
                    "<" => lt(self.translate_arith_term(&arguments[0]), self.translate_arith_term(&arguments[1])),
                    ">" => gt(self.translate_arith_term(&arguments[0]), self.translate_arith_term(&arguments[1])),
                    "=" => {
                        // SMT-LIB '=' is overloaded for both Booleans and Reals/Ints.
                        // We attempt to parse the first argument as Arith. If it fails (panics),
                        // it should theoretically be handled as Bool.
                        // For a robust implementation, checking the symbol map is safer.
                        let first_arg_is_bool = self.is_bool_term(&arguments[0]);

                        if first_arg_is_bool {
                            let b1 = self.translate_bool_term(&arguments[0]);
                            let b2 = self.translate_bool_term(&arguments[1]);
                            BoolExpr::Eq(Box::new(Expr::Bool(b1)), Box::new(Expr::Bool(b2)))
                        } else {
                            eq_arith(self.translate_arith_term(&arguments[0]), self.translate_arith_term(&arguments[1]))
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
                    // smt2parser handles decimals as rational representations if needed,
                    // but usually parsing the float string into rug::Rational works beautifully.
                    // E.g., "10.5" -> 21/2
                    let rat = rug::Rational::from_f64(dec.to_string().parse::<f64>().unwrap()).unwrap();
                    ArithExpr::Const(rat)
                }
                _ => panic!("Unsupported constant type"),
            },
            concrete::Term::QualIdentifier(id) => {
                let name = Self::symbol_of_qual_identifier(id);
                self.real_vars.get(name).cloned().unwrap_or_else(|| panic!("Undeclared arithmetic variable: {}", name))
            }
            concrete::Term::Application { qual_identifier, arguments } => {
                let op = Self::symbol_of_qual_identifier(qual_identifier);
                let args: Vec<_> = arguments.iter().map(|a| self.translate_arith_term(a)).collect();

                match op {
                    "+" => add(args),
                    "*" => mul(args),
                    "-" => {
                        if args.len() == 1 {
                            ArithExpr::Neg(Box::new(args.into_iter().next().unwrap()))
                        } else {
                            // Subtraction (a - b - c) -> a + (-b) + (-c)
                            let mut iter = args.into_iter();
                            let first = iter.next().unwrap();
                            let mut sum_args = vec![first];
                            for arg in iter {
                                sum_args.push(ArithExpr::Neg(Box::new(arg)));
                            }
                            add(sum_args)
                        }
                    }
                    "/" => {
                        assert_eq!(args.len(), 2, "Division expects exactly two arguments");
                        let mut iter = args.into_iter();
                        let num = iter.next().unwrap();
                        let den = iter.next().unwrap();
                        ArithExpr::Div(Box::new(num), Box::new(den))
                    }
                    _ => panic!("Unsupported arithmetic operator: {}", op),
                }
            }
            _ => panic!("Unsupported arithmetic term structure"),
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
}
