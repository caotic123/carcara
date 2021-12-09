use super::{Identifier, Rc, Sort, Term, Terminal};
use ahash::{AHashMap, AHashSet};

pub struct TermPool {
    pub(crate) terms: AHashMap<Term, Rc<Term>>,
    free_vars_cache: AHashMap<Rc<Term>, AHashSet<String>>,
    bool_true: Rc<Term>,
    bool_false: Rc<Term>,
}

impl Default for TermPool {
    fn default() -> Self {
        Self::new()
    }
}

impl TermPool {
    pub fn new() -> Self {
        let mut terms = AHashMap::new();
        let bool_sort = Self::add_term_to_map(&mut terms, Term::Sort(Sort::Bool));
        let bool_true = Self::add_term_to_map(
            &mut terms,
            Term::Terminal(Terminal::Var(
                Identifier::Simple("true".into()),
                bool_sort.clone(),
            )),
        );
        let bool_false = Self::add_term_to_map(
            &mut terms,
            Term::Terminal(Terminal::Var(Identifier::Simple("false".into()), bool_sort)),
        );
        Self {
            terms,
            free_vars_cache: AHashMap::new(),
            bool_true,
            bool_false,
        }
    }

    pub fn bool_true(&self) -> Rc<Term> {
        self.bool_true.clone()
    }

    pub fn bool_false(&self) -> Rc<Term> {
        self.bool_false.clone()
    }

    pub fn bool_constant(&self, value: bool) -> Rc<Term> {
        match value {
            true => self.bool_true(),
            false => self.bool_false(),
        }
    }

    fn add_term_to_map(terms_map: &mut AHashMap<Term, Rc<Term>>, term: Term) -> Rc<Term> {
        use std::collections::hash_map::Entry;

        match terms_map.entry(term) {
            Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            Entry::Vacant(vacant_entry) => {
                let term = vacant_entry.key().clone();
                vacant_entry.insert(Rc::new(term)).clone()
            }
        }
    }

    /// Takes a term and returns an `Rc` referencing it. If the term was not originally in the
    /// terms hash map, it is added to it.
    pub fn add_term(&mut self, term: Term) -> Rc<Term> {
        Self::add_term_to_map(&mut self.terms, term)
    }

    /// Takes a vector of terms and calls `add_term` on each.
    pub fn add_all(&mut self, terms: Vec<Term>) -> Vec<Rc<Term>> {
        terms.into_iter().map(|t| self.add_term(t)).collect()
    }

    /// Returns an `AHashSet` containing all the free variables in this term.
    pub fn free_vars<'t>(&mut self, term: &'t Rc<Term>) -> &AHashSet<String> {
        // Here, I would like to do
        // ```
        // if let Some(vars) = self.free_vars_cache.get(term) {
        //     return vars;
        // }
        // ```
        // However, because of a limitation in the borrow checker, the compiler thinks that
        // this immutable borrow of `cache` has to live until the end of the function, even
        // though the code immediately returns. This would stop me from mutating `cache` in the
        // rest of the function. Because of that, I have to check if the hash map contains
        // `term` as a key, and then get the value associated with it, meaning I have to access
        // the hash map twice, which is a bit slower. This is an example of problem case #3
        // from the non-lexical lifetimes RFC:
        // https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md
        if self.free_vars_cache.contains_key(term) {
            return self.free_vars_cache.get(term).unwrap();
        }
        let set = match term.as_ref() {
            Term::App(f, args) => {
                let mut set = self.free_vars(f).clone();
                for a in args {
                    set.extend(self.free_vars(a).iter().cloned())
                }
                set
            }
            Term::Op(_, args) => {
                let mut set = AHashSet::new();
                for a in args {
                    set.extend(self.free_vars(a).iter().cloned())
                }
                set
            }
            Term::Quant(_, bindings, inner) | Term::Let(bindings, inner) => {
                let mut vars = self.free_vars(inner).clone();
                for (s, _) in bindings {
                    vars.remove(s.as_str());
                }
                vars
            }
            Term::Choice((bound_var, _), inner) => {
                let mut vars = self.free_vars(inner).clone();
                vars.remove(bound_var.as_str());
                vars
            }
            Term::Terminal(Terminal::Var(Identifier::Simple(var), _)) => {
                let mut set = AHashSet::with_capacity(1);
                set.insert(var.clone());
                set
            }
            Term::Terminal(_) | Term::Sort(_) => AHashSet::new(),
        };
        self.free_vars_cache.insert(term.clone(), set);
        self.free_vars_cache.get(term).unwrap()
    }
}