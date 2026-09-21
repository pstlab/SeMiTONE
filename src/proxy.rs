use crate::rational::InfRational;
use rustc_hash::FxHashMap;
use std::collections::HashMap;

pub struct ProxyRegistry {
    pub proxy_to_constraint: FxHashMap<usize, TheoryConstraint>,
    pub constraint_to_proxy: FxHashMap<TheoryConstraint, usize>,
}

impl ProxyRegistry {
    pub fn new() -> Self {
        Self { proxy_to_constraint: HashMap::default(), constraint_to_proxy: HashMap::default() }
    }

    pub fn get_proxy(&self, constraint: &TheoryConstraint) -> Option<usize> {
        self.constraint_to_proxy.get(constraint).copied()
    }

    pub fn get_constraint(&self, lit: usize) -> Option<&TheoryConstraint> {
        self.proxy_to_constraint.get(&lit)
    }

    pub fn register(&mut self, constraint: TheoryConstraint, lit: usize) {
        self.proxy_to_constraint.insert(lit, constraint.clone());
        self.constraint_to_proxy.insert(constraint, lit);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum TheoryConstraint {
    LraLb(usize, InfRational),
    LraUb(usize, InfRational),
    EnumEq(usize, i32),
    DlLeq(usize, usize, InfRational),
    EufEq(usize, usize),
}
