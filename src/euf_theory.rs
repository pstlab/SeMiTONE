use crate::Lit;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Term {
    Var(usize),
    App(usize, Vec<usize>),
}

#[derive(Clone, Copy)]
enum EufUndoOp {
    Merged { child: usize, old_size: usize, parent: usize },
    AppendedUseList { parent: usize, count: usize },
}

#[derive(Clone, Copy, Debug)]
struct ProofEdge {
    target: usize,
    reason: Option<Lit>,
}

pub(super) struct EufTheory {
    parents: Vec<usize>,
    sizes: Vec<usize>,
    pub(super) terms: Vec<Term>,
    use_list: Vec<Vec<usize>>,
    pending_merges: Vec<(usize, usize)>,
    undo_trail: Vec<EufUndoOp>,
    trail_lim: Vec<usize>,
    proof_tree: Vec<Option<ProofEdge>>,
    disequalities: Vec<(usize, usize, Lit)>,
    diseq_lim: Vec<usize>,
}

impl EufTheory {
    pub(super) fn new() -> Self {
        Self {
            parents: Vec::new(),
            sizes: Vec::new(),
            terms: Vec::new(),
            use_list: Vec::new(),
            pending_merges: Vec::new(),
            undo_trail: Vec::new(),
            trail_lim: Vec::new(),
            proof_tree: Vec::new(),
            disequalities: Vec::new(),
            diseq_lim: Vec::new(),
        }
    }

    pub(super) fn add_term(&mut self, term: Term) -> usize {
        let id = self.terms.len();

        self.parents.push(id);
        self.sizes.push(1);
        self.use_list.push(Vec::new());
        self.proof_tree.push(None);

        if let Term::App(_, ref args) = term {
            for &arg in args {
                self.use_list[arg].push(id);
            }
        }

        self.terms.push(term);
        id
    }

    pub(super) fn find(&self, mut term: usize) -> usize {
        while term != self.parents[term] {
            term = self.parents[term];
        }
        term
    }

    fn are_congruent(&self, t1: usize, t2: usize) -> bool {
        if t1 == t2 {
            return true;
        }

        match (&self.terms[t1], &self.terms[t2]) {
            (Term::App(f1, args1), Term::App(f2, args2)) => {
                if f1 != f2 || args1.len() != args2.len() {
                    return false;
                }
                for i in 0..args1.len() {
                    if self.find(args1[i]) != self.find(args2[i]) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    pub(super) fn merge(&mut self, t1: usize, t2: usize, reason: Option<Lit>) -> bool {
        let root1 = self.find(t1);
        let root2 = self.find(t2);

        if root1 == root2 {
            return false;
        }

        let (parent, child) = if self.sizes[root1] >= self.sizes[root2] { (root1, root2) } else { (root2, root1) };

        self.undo_trail.push(EufUndoOp::Merged { child, old_size: self.sizes[parent], parent });
        self.parents[child] = parent;
        self.sizes[parent] += self.sizes[child];

        self.proof_tree[child] = Some(ProofEdge { target: parent, reason });

        let child_uses = self.use_list[child].clone();
        let parent_uses = self.use_list[parent].clone();

        for &u1 in &child_uses {
            for &u2 in &parent_uses {
                if self.are_congruent(u1, u2) {
                    self.pending_merges.push((u1, u2));
                }
            }
        }

        let count = child_uses.len();
        self.use_list[parent].extend(child_uses);
        self.undo_trail.push(EufUndoOp::AppendedUseList { parent, count });

        true
    }

    pub(super) fn propagate_congruences(&mut self) {
        while let Some((t1, t2)) = self.pending_merges.pop() {
            self.merge(t1, t2, None);
        }
    }

    pub(super) fn assert_disequality(&mut self, t1: usize, t2: usize, reason: Lit) -> Result<bool, Vec<Lit>> {
        if self.find(t1) == self.find(t2) {
            let mut lemma = vec![reason];
            self.explain(t1, t2, &mut lemma);

            Err(lemma.into_iter().map(|l| !l).collect())
        } else {
            self.disequalities.push((t1, t2, reason));
            Ok(true)
        }
    }

    pub(super) fn check_disequalities(&self) -> Result<bool, Vec<Lit>> {
        for &(t1, t2, reason) in &self.disequalities {
            if self.find(t1) == self.find(t2) {
                let mut lemma = vec![reason];
                self.explain(t1, t2, &mut lemma);
                return Err(lemma.into_iter().map(|l| !l).collect());
            }
        }
        Ok(false)
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.undo_trail.len());
        self.diseq_lim.push(self.disequalities.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];

        while self.undo_trail.len() > target_len {
            match self.undo_trail.pop().unwrap() {
                EufUndoOp::Merged { child, old_size, parent } => {
                    self.parents[child] = child;
                    self.sizes[parent] = old_size;

                    self.proof_tree[child] = None;
                }
                EufUndoOp::AppendedUseList { parent, count } => {
                    let new_len = self.use_list[parent].len() - count;
                    self.use_list[parent].truncate(new_len);
                }
            }
        }

        self.trail_lim.truncate(level);
        self.pending_merges.clear();

        let target_diseq = self.diseq_lim[level];
        self.disequalities.truncate(target_diseq);
        self.diseq_lim.truncate(level);
    }

    pub(super) fn explain(&self, t1: usize, t2: usize, explanation: &mut Vec<Lit>) {
        debug_assert_eq!(self.find(t1), self.find(t2), "Cannot explain nodes that are not equal");

        let mut path1 = HashSet::new();
        let mut curr = t1;
        path1.insert(curr);

        while let Some(edge) = &self.proof_tree[curr] {
            curr = edge.target;
            path1.insert(curr);
        }

        let mut lca = t2;
        while !path1.contains(&lca) {
            if let Some(edge) = &self.proof_tree[lca] {
                lca = edge.target;
            } else {
                unreachable!("No LCA found between nodes of the same class");
            }
        }

        curr = t1;
        while curr != lca {
            if let Some(edge) = &self.proof_tree[curr] {
                if let Some(lit) = edge.reason {
                    explanation.push(lit);
                }
                curr = edge.target;
            }
        }

        curr = t2;
        while curr != lca {
            if let Some(edge) = &self.proof_tree[curr] {
                if let Some(lit) = edge.reason {
                    explanation.push(lit);
                }
                curr = edge.target;
            }
        }
    }
}
