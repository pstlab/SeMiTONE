use rustc_hash::FxHashMap;

use crate::Lit;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Term {
    Var(usize),
    App(usize, Vec<usize>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Signature {
    f: usize,
    args: Vec<usize>,
}

#[derive(Clone)]
enum EufUndoOp {
    Merged { child: usize, old_size: usize, parent: usize },
    AppendedUseList { parent: usize, count: usize },
    ProofRerooted { changes: Vec<(usize, Option<ProofEdge>)> },
    SigInserted { sig: Signature },
    SigRemoved { sig: Signature, term: usize },
}

#[derive(Clone, Copy, Debug)]
struct ProofEdge {
    target: usize,
    reason: Option<Lit>,
}

pub(super) struct EufTheory {
    parents: Vec<usize>,
    sizes: Vec<usize>,
    terms: Vec<Term>,
    sig_table: FxHashMap<Signature, usize>,
    use_list: Vec<Vec<usize>>,
    pending_merges: Vec<(usize, usize)>,
    undo_trail: Vec<EufUndoOp>,
    trail_lim: Vec<usize>,
    proof_tree: Vec<Option<ProofEdge>>,
    disequalities: Vec<(usize, usize, Lit)>,
    diseq_lim: Vec<usize>,
    next_func_id: usize,
}

impl EufTheory {
    pub(super) fn new() -> Self {
        Self {
            parents: Vec::new(),
            sizes: Vec::new(),
            terms: Vec::new(),
            sig_table: FxHashMap::default(),
            use_list: Vec::new(),
            pending_merges: Vec::new(),
            undo_trail: Vec::new(),
            trail_lim: Vec::new(),
            proof_tree: Vec::new(),
            disequalities: Vec::new(),
            diseq_lim: Vec::new(),
            next_func_id: 0,
        }
    }

    pub(super) fn new_var(&mut self) -> usize {
        let id = self.terms.len();
        self.add_term_internal(Term::Var(id))
    }

    pub(super) fn new_func_id(&mut self) -> usize {
        let id = self.next_func_id;
        self.next_func_id += 1;
        id
    }

    pub(super) fn new_app(&mut self, func_id: usize, args: Vec<usize>) -> usize {
        self.add_term_internal(Term::App(func_id, args))
    }

    fn add_term_internal(&mut self, term: Term) -> usize {
        debug_assert!(self.trail_lim.is_empty(), "terms must be created at decision level 0");
        let id = self.terms.len();

        self.parents.push(id);
        self.sizes.push(1);
        self.use_list.push(Vec::new());
        self.proof_tree.push(None);

        if let Term::App(_, ref args) = term {
            let mut roots: Vec<usize> = args.iter().map(|&a| self.find(a)).collect();
            roots.sort_unstable();
            roots.dedup();
            for r in roots {
                self.use_list[r].push(id);
            }
        }

        self.terms.push(term);
        if let Some(sig) = self.signature(id) {
            if let Some(&existing_term) = self.sig_table.get(&sig) {
                self.pending_merges.push((id, existing_term));
            } else {
                self.sig_table.insert(sig, id);
            }
        }
        id
    }

    pub(super) fn find(&self, mut term: usize) -> usize {
        while term != self.parents[term] {
            term = self.parents[term];
        }
        term
    }

    pub(super) fn merge(&mut self, t1: usize, t2: usize, reason: Option<Lit>) -> bool {
        let root1 = self.find(t1);
        let root2 = self.find(t2);

        if root1 == root2 {
            return false;
        }
        debug_assert!(reason.is_some() || matches!((&self.terms[t1], &self.terms[t2]), (Term::App(..), Term::App(..))), "reason: None is reserved for congruence steps between applications");

        let (parent, child) = if self.sizes[root1] >= self.sizes[root2] { (root1, root2) } else { (root2, root1) };

        let child_uses = self.use_list[child].clone();

        for &u in &child_uses {
            if let Some(old_sig) = self.signature(u) {
                // Only the representative owns the entry: removing someone else's entry
                // (or recording the wrong owner) corrupts the table on undo.
                if self.sig_table.get(&old_sig) == Some(&u) {
                    self.sig_table.remove(&old_sig);
                    self.undo_trail.push(EufUndoOp::SigRemoved { sig: old_sig, term: u });
                }
            }
        }

        self.undo_trail.push(EufUndoOp::Merged { child, old_size: self.sizes[parent], parent });
        self.parents[child] = parent;
        self.sizes[parent] += self.sizes[child];

        let changes = self.reroot(t1);
        self.undo_trail.push(EufUndoOp::ProofRerooted { changes });
        self.proof_tree[t1] = Some(ProofEdge { target: t2, reason });

        for &u in &child_uses {
            if let Some(new_sig) = self.signature(u) {
                match self.sig_table.get(&new_sig) {
                    Some(&existing_term) if existing_term == u => {}
                    Some(&existing_term) => self.pending_merges.push((u, existing_term)),
                    None => {
                        self.sig_table.insert(new_sig.clone(), u);
                        self.undo_trail.push(EufUndoOp::SigInserted { sig: new_sig });
                    }
                }
            }
        }

        let count = child_uses.len();
        self.use_list[parent].extend(child_uses);
        self.undo_trail.push(EufUndoOp::AppendedUseList { parent, count });

        true
    }

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
        // cancel_until() discards pending_merges; that is only correct if none of them
        // belong to the levels that survive, so reach the congruence fixpoint first.
        self.propagate_congruences();
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
                EufUndoOp::SigInserted { sig } => {
                    self.sig_table.remove(&sig);
                }
                EufUndoOp::SigRemoved { sig, term } => {
                    self.sig_table.insert(sig, term);
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
        let mut queue = vec![(t1, t2)];
        // A proof edge is identified by its source node (edges are always crossed upwards),
        // so every edge, and hence every reason literal, is emitted at most once.
        let mut done: HashSet<usize> = HashSet::new();

        while let Some((a, b)) = queue.pop() {
            if a == b {
                continue;
            }
            debug_assert_eq!(self.find(a), self.find(b), "Cannot explain nodes that are not equal");
            let lca = self.lca(a, b);

            for start in [a, b] {
                let mut curr = start;
                while curr != lca {
                    let edge = self.proof_tree[curr].expect("path to LCA must exist");
                    if done.insert(curr) {
                        match edge.reason {
                            Some(lit) => explanation.push(lit),
                            None => match (&self.terms[curr], &self.terms[edge.target]) {
                                (Term::App(_, xs), Term::App(_, ys)) => {
                                    queue.extend(xs.iter().copied().zip(ys.iter().copied()));
                                }
                                _ => unreachable!("edge without a reason must be a congruence edge"),
                            },
                        }
                    }
                    curr = edge.target;
                }
            }
        }
    }

    fn lca(&self, a: usize, b: usize) -> usize {
        let mut ancestors = HashSet::new();
        let mut curr = a;
        ancestors.insert(curr);
        while let Some(edge) = &self.proof_tree[curr] {
            curr = edge.target;
            ancestors.insert(curr);
        }
        let mut lca = b;
        while !ancestors.contains(&lca) {
            lca = self.proof_tree[lca].expect("nodes of the same class share a proof tree").target;
        }
        lca
    }

    fn signature(&self, term_id: usize) -> Option<Signature> {
        if let Term::App(f, ref args) = self.terms[term_id] { Some(Signature { f, args: args.iter().map(|&a| self.find(a)).collect() }) } else { None }
    }
}

#[cfg(test)]
mod regression_tests {
    use super::*;

    /// Terms created after a merge must register on the class root, not on the raw argument.
    #[test]
    fn term_created_after_merge_is_congruent() {
        let mut e = EufTheory::new();
        let f = e.new_func_id();
        let x = e.new_var();
        let y = e.new_var();
        let (w1, w2, w3) = (e.new_var(), e.new_var(), e.new_var());
        let fw = e.new_app(f, vec![w1]);
        e.merge(w1, w2, Some(Lit::new(1, false)));
        e.merge(w1, w3, Some(Lit::new(2, false)));
        e.merge(x, y, Some(Lit::new(3, false)));
        let fy = e.new_app(f, vec![y]); // y is a non-root here
        e.merge(x, w1, Some(Lit::new(4, false))); // x's class becomes the child
        e.propagate_congruences();
        assert_eq!(e.find(fy), e.find(fw));
    }

    /// Congruences queued by term creation must survive a push/cancel_until(0) round trip.
    #[test]
    fn creation_time_congruence_survives_backtracking() {
        let mut e = EufTheory::new();
        let x = e.new_var();
        let h1 = e.new_app(7, vec![x]);
        let h2 = e.new_app(7, vec![x]);
        e.push();
        e.cancel_until(0);
        e.propagate_congruences();
        assert_eq!(e.find(h1), e.find(h2));
    }

    /// `reason: None` is reserved for congruence steps; on variables it would yield an empty explanation.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "reserved for congruence")]
    fn none_reason_on_variables_is_rejected() {
        let mut e = EufTheory::new();
        let (a, b) = (e.new_var(), e.new_var());
        e.merge(a, b, None);
    }

    /// Shared sub-proofs must be explained once (was exponential in the nesting depth).
    #[test]
    fn explanation_is_linear_on_shared_subproofs() {
        let mut e = EufTheory::new();
        let f = e.new_func_id();
        let (mut a, mut b, mut c, mut d) = (e.new_var(), e.new_var(), e.new_var(), e.new_var());
        let (a0, b0, c0, d0) = (a, b, c, d);
        for _ in 0..200 {
            let (na, nb) = (e.new_app(f, vec![a, c]), e.new_app(f, vec![b, d]));
            let (nc, nd) = (e.new_app(f, vec![c, a]), e.new_app(f, vec![d, b]));
            (a, b, c, d) = (na, nb, nc, nd);
        }
        e.propagate_congruences();
        e.merge(a0, b0, Some(Lit::new(1, false)));
        e.merge(c0, d0, Some(Lit::new(2, false)));
        e.propagate_congruences();
        let mut lemma = Vec::new();
        e.explain(a, b, &mut lemma);
        assert_eq!(lemma.len(), 2);
    }

    // ---- differential fuzz against a naive congruence closure, with push/cancel_until ----

    struct Rng(u64);
    impl Rng {
        fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    fn naive_classes(terms: &[Option<(usize, Vec<usize>)>], eqs: &[(usize, usize)]) -> Vec<usize> {
        fn find(p: &mut [usize], mut x: usize) -> usize {
            while p[x] != x {
                p[x] = p[p[x]];
                x = p[x];
            }
            x
        }
        let mut p: Vec<usize> = (0..terms.len()).collect();
        for &(a, b) in eqs {
            let (ra, rb) = (find(&mut p, a), find(&mut p, b));
            p[ra] = rb;
        }
        loop {
            let mut changed = false;
            for i in 0..terms.len() {
                for j in i + 1..terms.len() {
                    if let (Some((f, xs)), Some((g, ys))) = (&terms[i], &terms[j]) {
                        if f == g && xs.len() == ys.len() && find(&mut p, i) != find(&mut p, j) && xs.iter().zip(ys).all(|(&x, &y)| find(&mut p, x) == find(&mut p, y)) {
                            let (ri, rj) = (find(&mut p, i), find(&mut p, j));
                            p[ri] = rj;
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        (0..terms.len()).map(|i| find(&mut p, i)).collect()
    }

    #[test]
    fn fuzz_against_naive_closure() {
        for seed in 1..3000u64 {
            let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
            let mut e = EufTheory::new();
            let mut terms: Vec<Option<(usize, Vec<usize>)>> = Vec::new();
            for _ in 0..3 + rng.below(4) {
                e.new_var();
                terms.push(None);
            }
            for _ in 0..4 + rng.below(8) {
                let (f, arity) = (rng.below(3), 1 + rng.below(2));
                let args: Vec<usize> = (0..arity).map(|_| rng.below(terms.len())).collect();
                e.new_app(f, args.clone());
                terms.push(Some((f, args)));
            }
            e.propagate_congruences();

            let mut levels: Vec<Vec<(usize, usize)>> = vec![vec![]];
            let mut lit = 1;
            for step in 0..30 {
                match rng.below(10) {
                    0..=5 => {
                        let (a, b) = (rng.below(terms.len()), rng.below(terms.len()));
                        e.merge(a, b, Some(Lit::new(lit, false)));
                        lit += 1;
                        e.propagate_congruences();
                        levels.last_mut().unwrap().push((a, b));
                    }
                    6..=7 if levels.len() < 5 => {
                        e.push();
                        levels.push(vec![]);
                    }
                    _ if levels.len() > 1 => {
                        let l = rng.below(levels.len() - 1);
                        e.cancel_until(l);
                        levels.truncate(l + 1);
                    }
                    _ => continue,
                }
                let eqs: Vec<_> = levels.iter().flatten().copied().collect();
                let oracle = naive_classes(&terms, &eqs);
                for i in 0..terms.len() {
                    for j in 0..terms.len() {
                        assert_eq!(e.find(i) == e.find(j), oracle[i] == oracle[j], "seed {seed} step {step}: pair ({i},{j})");
                    }
                }
            }
        }
    }
}
