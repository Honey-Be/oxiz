//! A minimal in-crate host (`TermLang` impl) for developing and
//! z3-cross-checking the engine without OxiZ. A term arena with hash-consing;
//! bound variables are identified by name (as in OxiZ), so substitution is a
//! plain recursive replace — capture-free because the substitution range is
//! always ground (no variables to capture).

use crate::term::{Binding, TermLang, TermView};
use rustc_hash::FxHashMap;

pub type Tid = u32;
pub type Name = u32;
pub type Sym = u32;
pub type Sort = u32;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Node {
    Var(Name),
    App(Sym, Vec<Tid>),
    Implies(Tid, Tid),
    Quant {
        forall: bool,
        vars: Vec<(Name, Sort)>,
        patterns: Vec<Vec<Tid>>,
        body: Tid,
    },
    Opaque(u64),
}

#[derive(Default)]
pub struct Toy {
    nodes: Vec<Node>,
    intern: FxHashMap<Node, Tid>,
    sort: Vec<Sort>,
    // side table so `view` can hand out the bound-vars slice by reference
    quant_vars: Vec<Vec<(Name, Sort)>>,
    quant_pats: Vec<Vec<Vec<Tid>>>,
}

impl Toy {
    pub fn new() -> Self {
        Toy::default()
    }

    fn mk(&mut self, node: Node, sort: Sort) -> Tid {
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = self.nodes.len() as Tid;
        self.quant_vars.push(Vec::new());
        self.quant_pats.push(Vec::new());
        if let Node::Quant { vars, patterns, .. } = &node {
            self.quant_vars[id as usize] = vars.clone();
            self.quant_pats[id as usize] = patterns.clone();
        }
        self.intern.insert(node.clone(), id);
        self.nodes.push(node);
        self.sort.push(sort);
        id
    }

    pub fn var(&mut self, name: Name, sort: Sort) -> Tid {
        self.mk(Node::Var(name), sort)
    }
    pub fn app(&mut self, sym: Sym, args: &[Tid], sort: Sort) -> Tid {
        self.mk(Node::App(sym, args.to_vec()), sort)
    }
    pub fn konst(&mut self, sym: Sym, sort: Sort) -> Tid {
        self.app(sym, &[], sort)
    }
    pub fn opaque(&mut self, tag: u64, sort: Sort) -> Tid {
        self.mk(Node::Opaque(tag), sort)
    }
    pub fn implies(&mut self, a: Tid, b: Tid, bool_sort: Sort) -> Tid {
        self.mk(Node::Implies(a, b), bool_sort)
    }
    pub fn forall(
        &mut self,
        vars: &[(Name, Sort)],
        patterns: &[&[Tid]],
        body: Tid,
        bool_sort: Sort,
    ) -> Tid {
        self.mk(
            Node::Quant {
                forall: true,
                vars: vars.to_vec(),
                patterns: patterns.iter().map(|p| p.to_vec()).collect(),
                body,
            },
            bool_sort,
        )
    }
}

impl TermLang for Toy {
    type Term = Tid;
    type Sort = Sort;
    type VarName = Name;
    type Sym = Sym;

    fn view(&self, t: Tid) -> TermView<'_, Self> {
        match &self.nodes[t as usize] {
            Node::Var(n) => TermView::Var { name: *n },
            Node::App(s, _) => TermView::App { sym: *s },
            // Treat `⇒` as an app under a reserved pseudo-symbol.
            Node::Implies(_, _) => TermView::App { sym: u32::MAX },
            Node::Quant { forall, body, .. } => TermView::Quant {
                forall: *forall,
                vars: &self.quant_vars[t as usize],
                body: *body,
            },
            Node::Opaque(_) => TermView::Opaque,
        }
    }

    fn children(&self, t: Tid) -> Vec<Tid> {
        match &self.nodes[t as usize] {
            Node::App(_, args) => args.clone(),
            Node::Implies(a, b) => vec![*a, *b],
            _ => Vec::new(),
        }
    }

    fn patterns(&self, t: Tid) -> Vec<Vec<Tid>> {
        match &self.nodes[t as usize] {
            Node::Quant { .. } => self.quant_pats[t as usize].clone(),
            _ => Vec::new(),
        }
    }

    fn sort_of(&self, t: Tid) -> Sort {
        self.sort[t as usize]
    }

    fn substitute(&mut self, body: Tid, binding: &Binding<Self>) -> Tid {
        self.subst_rec(body, binding)
    }

    fn mk_implies(&mut self, a: Tid, b: Tid) -> Tid {
        // bool sort is conventionally 0 in tests
        let bs = self.sort_of(a);
        self.mk(Node::Implies(a, b), bs)
    }
}

impl Toy {
    fn subst_rec(&mut self, t: Tid, binding: &Binding<Toy>) -> Tid {
        match self.nodes[t as usize].clone() {
            Node::Var(n) => binding.get(n).unwrap_or(t),
            Node::App(s, args) => {
                let new: Vec<Tid> = args.iter().map(|&a| self.subst_rec(a, binding)).collect();
                let srt = self.sort[t as usize];
                if new == args { t } else { self.app(s, &new, srt) }
            }
            Node::Implies(a, b) => {
                let na = self.subst_rec(a, binding);
                let nb = self.subst_rec(b, binding);
                let bs = self.sort[t as usize];
                self.mk(Node::Implies(na, nb), bs)
            }
            // Do not substitute under a nested quantifier's own binders in the
            // toy (the corpus does not need nested capture); a real host
            // handles α-renaming. Leave as-is.
            Node::Quant { .. } | Node::Opaque(_) => t,
        }
    }
}
