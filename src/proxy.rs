use crate::{dl_theory::DlVar, enum_theory::EnumVar, euf_theory::EufNode, lra_theory::ArithVar, rational::InfRational, sat_solver::BoolVar};
use rustc_hash::FxHashMap;
use std::collections::HashMap;

pub struct ProxyRegistry {
    pub proxy_to_constraint: FxHashMap<BoolVar, TheoryConstraint>,
    pub constraint_to_proxy: FxHashMap<TheoryConstraint, BoolVar>,
}

impl ProxyRegistry {
    pub fn new() -> Self {
        Self { proxy_to_constraint: HashMap::default(), constraint_to_proxy: HashMap::default() }
    }

    pub fn get_proxy(&self, constraint: &TheoryConstraint) -> Option<BoolVar> {
        self.constraint_to_proxy.get(constraint).copied()
    }

    pub fn get_constraint(&self, var: BoolVar) -> Option<&TheoryConstraint> {
        self.proxy_to_constraint.get(&var)
    }

    pub fn register(&mut self, constraint: TheoryConstraint, var: BoolVar) {
        self.proxy_to_constraint.insert(var, constraint.clone());
        self.constraint_to_proxy.insert(constraint, var);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum TheoryConstraint {
    LraLb(ArithVar, InfRational),
    LraUb(ArithVar, InfRational),
    EnumEq(EnumVar, usize),
    DlLeq(DlVar, DlVar, InfRational),
    EufEq(EufNode, EufNode),
}
