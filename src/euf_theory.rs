use crate::Lit;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Term {
    Var(usize),
    App(usize, Vec<usize>),
}

#[derive(Clone)]
enum EufUndoOp {
    Merged { child: usize, old_size: usize, parent: usize },
    AppendedUseList { parent: usize, count: usize },
    ProofRerooted { changes: Vec<(usize, Option<ProofEdge>)> },
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

        // The proof tree must record the actual asserted edge (t1 -> t2), not the union-find
        // root/child choice, otherwise `explain` can lose intermediate reasons on later merges.
        let changes = self.reroot(t1);
        self.undo_trail.push(EufUndoOp::ProofRerooted { changes });
        self.proof_tree[t1] = Some(ProofEdge { target: t2, reason });

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

    /// Reverses the proof-tree edges from `node` up to its current root, so that `node`
    /// becomes the root of its own explanation tree. Returns the previous edges, so the
    /// caller can undo this on backtracking.
    fn reroot(&mut self, node: usize) -> Vec<(usize, Option<ProofEdge>)> {
        let mut changes = Vec::new();
        let mut curr = node;
        let mut incoming: Option<ProofEdge> = None;

        loop {
            let old_edge = self.proof_tree[curr];
            changes.push((curr, old_edge));
            self.proof_tree[curr] = incoming;

            match old_edge {
                Some(edge) => {
                    incoming = Some(ProofEdge { target: curr, reason: edge.reason });
                    curr = edge.target;
                }
                None => break,
            }
        }

        changes
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
                }
                EufUndoOp::AppendedUseList { parent, count } => {
                    let new_len = self.use_list[parent].len() - count;
                    self.use_list[parent].truncate(new_len);
                }
                EufUndoOp::ProofRerooted { changes } => {
                    for (node, old_edge) in changes.into_iter().rev() {
                        self.proof_tree[node] = old_edge;
                    }
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

        self.explain_path_to(t1, lca, explanation);
        self.explain_path_to(t2, lca, explanation);
    }

    fn explain_path_to(&self, mut curr: usize, target: usize, explanation: &mut Vec<Lit>) {
        while curr != target {
            let edge = self.proof_tree[curr].expect("path to LCA must exist");
            match edge.reason {
                Some(lit) => explanation.push(lit),
                None => {
                    if let (Term::App(_, args_a), Term::App(_, args_b)) = (&self.terms[curr], &self.terms[edge.target]) {
                        for (&a, &b) in args_a.iter().zip(args_b.iter()) {
                            self.explain(a, b, explanation);
                        }
                    }
                }
            }
            curr = edge.target;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_union_find() {
        let mut euf = EufTheory::new();
        let a = euf.add_term(Term::Var(0));
        let b = euf.add_term(Term::Var(1));
        let c = euf.add_term(Term::Var(2));

        assert_ne!(euf.find(a), euf.find(b));

        // a = b
        let l1 = Lit::new(1, false);
        assert!(euf.merge(a, b, Some(l1)));
        assert_eq!(euf.find(a), euf.find(b));

        // b = c
        let l2 = Lit::new(2, false);
        assert!(euf.merge(b, c, Some(l2)));
        assert_eq!(euf.find(a), euf.find(c));
    }

    #[test]
    fn test_congruence_closure() {
        let mut euf = EufTheory::new();
        let x = euf.add_term(Term::Var(0));
        let y = euf.add_term(Term::Var(1));

        // f(x) and f(y)
        let f_id = 100;
        let fx = euf.add_term(Term::App(f_id, vec![x]));
        let fy = euf.add_term(Term::App(f_id, vec![y]));

        assert_ne!(euf.find(fx), euf.find(fy));

        // Assert x = y
        euf.merge(x, y, Some(Lit::new(1, false)));

        // The theory must deduce f(x) = f(y)
        euf.propagate_congruences();
        assert_eq!(euf.find(fx), euf.find(fy));
    }

    #[test]
    fn test_nested_congruence_closure() {
        let mut euf = EufTheory::new();
        let x = euf.add_term(Term::Var(0));
        let y = euf.add_term(Term::Var(1));

        // f(x) and f(y)
        let f_id = 100;
        let fx = euf.add_term(Term::App(f_id, vec![x]));
        let fy = euf.add_term(Term::App(f_id, vec![y]));

        // g(f(x)) and g(f(y))
        let g_id = 200;
        let gfx = euf.add_term(Term::App(g_id, vec![fx]));
        let gfy = euf.add_term(Term::App(g_id, vec![fy]));

        // Assert x = y. This must trigger a chain reaction!
        euf.merge(x, y, Some(Lit::new(1, false)));
        euf.propagate_congruences();

        assert_eq!(euf.find(fx), euf.find(fy), "f(x) must equal f(y)");
        assert_eq!(euf.find(gfx), euf.find(gfy), "The chain reaction must also merge g(f(x)) and g(f(y))");
    }

    #[test]
    fn test_backtracking() {
        let mut euf = EufTheory::new();
        let a = euf.add_term(Term::Var(0));
        let b = euf.add_term(Term::Var(1));
        let c = euf.add_term(Term::Var(2));

        // Level 0: a = b
        euf.merge(a, b, Some(Lit::new(1, false)));
        assert_eq!(euf.find(a), euf.find(b));

        // Start level 1
        euf.push();

        // Level 1: b = c
        euf.merge(b, c, Some(Lit::new(2, false)));
        assert_eq!(euf.find(a), euf.find(c));

        // Undo level 1
        euf.cancel_until(0);

        // a must still equal b, but not c
        assert_eq!(euf.find(a), euf.find(b));
        assert_ne!(euf.find(a), euf.find(c));
    }

    #[test]
    fn test_proof_forest_explain() {
        let mut euf = EufTheory::new();
        let a = euf.add_term(Term::Var(0));
        let b = euf.add_term(Term::Var(1));
        let c = euf.add_term(Term::Var(2));
        let d = euf.add_term(Term::Var(3));

        let l1 = Lit::new(1, false);
        let l2 = Lit::new(2, false);
        let l3 = Lit::new(3, false);

        // a = b = c = d
        euf.merge(a, b, Some(l1));
        euf.merge(b, c, Some(l2));
        euf.merge(c, d, Some(l3));

        // Explain why a == d
        let mut lemma = Vec::new();
        euf.explain(a, d, &mut lemma);

        // Must contain exactly the three reasons that link a and d
        assert_eq!(lemma.len(), 3);
        assert!(lemma.contains(&l1));
        assert!(lemma.contains(&l2));
        assert!(lemma.contains(&l3));
    }

    #[test]
    fn test_disequality_conflict() {
        let mut euf = EufTheory::new();
        let a = euf.add_term(Term::Var(0));
        let b = euf.add_term(Term::Var(1));
        let c = euf.add_term(Term::Var(2));

        let lit_a_eq_b = Lit::new(1, false);
        let lit_b_eq_c = Lit::new(2, false);
        let lit_a_neq_c = Lit::new(3, false); // SAT asserts a != c

        // Assert a != c
        assert_eq!(euf.assert_disequality(a, c, lit_a_neq_c), Ok(true));

        // a = b
        euf.merge(a, b, Some(lit_a_eq_b));

        // b = c. This forces a = c, violating the disequality!
        euf.merge(b, c, Some(lit_b_eq_c));

        // check_disequalities must notice this and produce the conflict
        let conflict = euf.check_disequalities();
        assert!(conflict.is_err());

        // The conflict must negate the involved literals: !(a=b) V !(b=c) V (a!=c)
        let lemma = conflict.unwrap_err();
        assert!(lemma.contains(&!lit_a_eq_b));
        assert!(lemma.contains(&!lit_b_eq_c));
        assert!(lemma.contains(&!lit_a_neq_c));
    }

    #[test]
    fn test_disequality_immediate_conflict() {
        let mut euf = EufTheory::new();
        let a = euf.add_term(Term::Var(0));
        let b = euf.add_term(Term::Var(1));

        let lit_a_eq_b = Lit::new(1, false);
        let lit_a_neq_b = Lit::new(2, false);

        // Merge a and b
        euf.merge(a, b, Some(lit_a_eq_b));

        // Then try to force a != b. The error must be immediate.
        let result = euf.assert_disequality(a, b, lit_a_neq_b);
        assert!(result.is_err());

        let lemma = result.unwrap_err();
        assert!(lemma.contains(&!lit_a_eq_b));
        assert!(lemma.contains(&!lit_a_neq_b));
    }

    #[test]
    fn test_explain_through_congruence() {
        let mut euf = EufTheory::new();
        let x = euf.add_term(Term::Var(0));
        let y = euf.add_term(Term::Var(1));

        let f_id = 100;
        let fx = euf.add_term(Term::App(f_id, vec![x]));
        let fy = euf.add_term(Term::App(f_id, vec![y]));

        let lit_xy = Lit::new(1, false);
        let lit_fx_neq_fy = Lit::new(2, false); // SAT asserts f(x) != f(y)

        assert_eq!(euf.assert_disequality(fx, fy, lit_fx_neq_fy), Ok(true));

        // x = y forces f(x) = f(y) by congruence, contradicting the disequality
        euf.merge(x, y, Some(lit_xy));
        euf.propagate_congruences();

        let conflict = euf.check_disequalities();
        assert!(conflict.is_err());

        let lemma = conflict.unwrap_err();
        // The lemma must also explain the congruence step through x = y,
        // even though f(x) = f(y) was derived with reason: None.
        assert!(lemma.contains(&!lit_xy), "incomplete lemma, missing congruence justification: {:?}", lemma);
        assert!(lemma.contains(&!lit_fx_neq_fy));
    }
}
