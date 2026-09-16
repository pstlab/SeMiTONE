use rand::{Rng, RngExt, seq::IndexedRandom};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sort {
    Bool,
    Int,
    Real,
    U,
}

pub struct SmtFuzzer {
    vars: Vec<(String, Sort)>,
    funcs: Vec<(String, Vec<Sort>, Sort)>,
}

impl SmtFuzzer {
    pub fn new() -> Self {
        Self { vars: Vec::new(), funcs: Vec::new() }
    }

    pub fn generate_declarations(&mut self, rng: &mut impl Rng) -> String {
        let mut script = String::from("(set-logic QF_UFLIRA)\n(declare-sort U 0)\n");

        let sorts = [("Bool", Sort::Bool), ("Int", Sort::Int), ("Real", Sort::Real), ("U", Sort::U)];

        for (i, (name, sort)) in sorts.iter().enumerate() {
            let var_name = format!("v_{}", i);
            script.push_str(&format!("(declare-fun {} () {})\n", var_name, name));
            self.vars.push((var_name, *sort));
        }

        for i in 4..10 {
            let (name, sort) = sorts.choose(rng).unwrap();
            let var_name = format!("v_{}", i);
            script.push_str(&format!("(declare-fun {} () {})\n", var_name, name));
            self.vars.push((var_name, *sort));
        }

        self.funcs.push(("f_pure".to_string(), vec![Sort::U], Sort::U));
        self.funcs.push(("f_mix_int".to_string(), vec![Sort::Int], Sort::U));
        self.funcs.push(("f_mix_bool".to_string(), vec![Sort::Bool], Sort::U));

        for (name, args, ret) in &self.funcs {
            let arg_names: Vec<&str> = args
                .iter()
                .map(|s| match s {
                    Sort::Bool => "Bool",
                    Sort::Int => "Int",
                    Sort::Real => "Real",
                    Sort::U => "U",
                })
                .collect();
            let ret_name = match ret {
                Sort::Bool => "Bool",
                Sort::Int => "Int",
                Sort::Real => "Real",
                Sort::U => "U",
            };
            script.push_str(&format!("(declare-fun {} ({}) {})\n", name, arg_names.join(" "), ret_name));
        }

        script
    }

    fn generate_term(&self, rng: &mut impl Rng, target_sort: Sort, depth: usize) -> String {
        if depth == 0 {
            return self.generate_leaf(rng, target_sort);
        }

        if rng.random_bool(0.3) {
            return self.generate_leaf(rng, target_sort);
        }

        match target_sort {
            Sort::Bool => {
                let ops = ["and", "or", "not", "=>", "="];
                let op = ops.choose(rng).unwrap();

                if *op == "not" {
                    format!("(not {})", self.generate_term(rng, Sort::Bool, depth - 1))
                } else if *op == "=" {
                    let cmp_sort = *[Sort::Int, Sort::Real, Sort::U].choose(rng).unwrap();
                    let left = self.generate_term(rng, cmp_sort, depth - 1);
                    let right = self.generate_term(rng, cmp_sort, depth - 1);
                    format!("(= {} {})", left, right)
                } else {
                    let left = self.generate_term(rng, Sort::Bool, depth - 1);
                    let right = self.generate_term(rng, Sort::Bool, depth - 1);
                    format!("({} {} {})", op, left, right)
                }
            }
            Sort::Int | Sort::Real => {
                let ops = ["+", "-", "*"];
                let op = ops.choose(rng).unwrap();
                if *op == "*" {
                    let is_left_const = rng.random_bool(0.5);
                    let left = if is_left_const { self.generate_const_leaf(target_sort) } else { self.generate_term(rng, target_sort, depth - 1) };
                    let right = if is_left_const { self.generate_term(rng, target_sort, depth - 1) } else { self.generate_const_leaf(target_sort) };
                    format!("(* {} {})", left, right)
                } else {
                    let left = self.generate_term(rng, target_sort, depth - 1);
                    let right = self.generate_term(rng, target_sort, depth - 1);
                    format!("({} {} {})", op, left, right)
                }
            }
            Sort::U => {
                let valid_funcs: Vec<_> = self.funcs.iter().filter(|f| matches!(f.2, Sort::U)).collect();
                let func = valid_funcs.choose(rng).unwrap();

                let mut args_str = Vec::new();
                for &arg_sort in &func.1 {
                    args_str.push(self.generate_term(rng, arg_sort, depth - 1));
                }
                format!("({} {})", func.0, args_str.join(" "))
            }
        }
    }

    fn generate_leaf(&self, rng: &mut impl Rng, sort: Sort) -> String {
        let valid_vars: Vec<_> = self.vars.iter().filter(|v| v.1 == sort).collect();

        let use_const = rng.random_bool(0.5);

        if use_const || valid_vars.is_empty() {
            match sort {
                Sort::Bool => {
                    if rng.random_bool(0.5) {
                        "true".to_string()
                    } else {
                        "false".to_string()
                    }
                }
                Sort::Int => {
                    let val = rng.random_range(-10..10);
                    if val < 0 { format!("(- {})", -val) } else { format!("{}", val) }
                }
                Sort::Real => {
                    let val = rng.random_range(-10..10);
                    if val < 0 { format!("(- {}.0)", -val) } else { format!("{}.0", val) }
                }
                Sort::U => valid_vars.choose(rng).map(|v| v.0.clone()).unwrap_or_else(|| panic!("No U vars available")),
            }
        } else {
            valid_vars.choose(rng).unwrap().0.clone()
        }
    }

    fn generate_const_leaf(&self, sort: Sort) -> String {
        let mut rng = rand::rng();
        match sort {
            Sort::Int => {
                let val = rng.random_range(-10..10);
                if val < 0 { format!("(- {})", -val) } else { format!("{}", val) }
            }
            Sort::Real => {
                let val = rng.random_range(-10..10);
                if val < 0 { format!("(- {}.0)", -val) } else { format!("{}.0", val) }
            }
            _ => panic!("Only Int and Real sorts can have constant leaves"),
        }
    }

    pub fn generate_script(&mut self, rng: &mut impl Rng, num_asserts: usize) -> String {
        self.vars.clear();
        self.funcs.clear();
        let mut script = self.generate_declarations(rng);

        for _ in 0..num_asserts {
            let expr = self.generate_term(rng, Sort::Bool, 3);
            script.push_str(&format!("(assert {})\n", expr));
        }

        script.push_str("(check-sat)\n");
        script
    }
}
