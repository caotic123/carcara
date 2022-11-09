use crate::ast::{BindingList, Quantifier, Rc, Term};
use ahash::{AHashMap, AHashSet, AHasher};
use std::{
    borrow::Borrow,
    fmt,
    hash::{Hash, Hasher},
    ops,
};

/// Returns `true` if the character is a valid symbol character in the SMT-LIB and Alethe languages.
pub fn is_symbol_character(ch: char) -> bool {
    match ch {
        ch if ch.is_ascii_alphanumeric() => true,
        '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<'
        | '>' | '@' => true,
        _ => false,
    }
}

/// An iterator that removes duplicate elements from `iter`. This will yield the elements in
/// `iter` in order, skipping elements that have already been seen before.
pub struct Dedup<T, I> {
    seen: AHashSet<T>,
    iter: I,
}

impl<T, I> Iterator for Dedup<T, I>
where
    T: Clone + Hash + Eq,
    I: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let got = self.iter.next()?;
            let is_new = self.seen.insert(got.clone());
            if is_new {
                return Some(got);
            }
        }
    }
}

pub trait DedupIterator<T> {
    /// Creates an iterator that skips duplicate elements.
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized;
}

impl<T, I: Iterator<Item = T>> DedupIterator<T> for I {
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized,
    {
        Dedup { seen: AHashSet::new(), iter: self }
    }
}

pub struct HashCache<T> {
    hash: u64,
    value: T,
}

impl<T: PartialEq> PartialEq for HashCache<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for HashCache<T> {}

impl<T: Hash> Hash for HashCache<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<T: Eq + Hash> HashCache<T> {
    pub fn new(value: T) -> Self {
        let mut hasher = AHasher::default();
        value.hash(&mut hasher);
        Self { hash: hasher.finish(), value }
    }

    pub fn unwrap(self) -> T {
        self.value
    }
}

impl<T> AsRef<T> for HashCache<T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

#[derive(Debug)]
pub struct SymbolTable<K, V> {
    scopes: Vec<AHashMap<K, V>>,
}

impl<K, V> SymbolTable<K, V> {
    pub fn new() -> Self {
        Self { scopes: vec![AHashMap::new()] }
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(AHashMap::new());
    }

    pub fn pop_scope(&mut self) {
        match self.scopes.len() {
            0 => unreachable!(),
            1 => {
                log::error!("cannot pop last scope in symbol table");
                panic!();
            }
            _ => {
                self.scopes.pop().unwrap();
            }
        }
    }
}

impl<K: Eq + Hash, V> SymbolTable<K, V> {
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        // Note: If there are a lot of scopes in the symbol table, this can be a big performance
        // bottleneck. As currently implemented, this function needs to hash the key once for every
        // scope. The ideal way of solving this would be to hash the key once, and reuse that hash
        // to access the entry in each scope. To do that, we could use the `HashMap::raw_entry`
        // method, but it is currently nightly-only. Another way to mitigate this issue is to use
        // the `HashCache<T>` struct to wrap the key values in the symbol table. This allows the key
        // to only be hashed once, and that value is stored and reused in the struct.
        self.scopes.iter().rev().find_map(|scope| scope.get(key))
    }

    pub fn get_with_depth<Q>(&self, key: &Q) -> Option<(usize, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(depth, scope)| scope.get(key).map(|v| (depth, v)))
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.scopes.last_mut().unwrap().insert(key, value);
    }
}

impl<K, V> Default for SymbolTable<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

// TODO: Document this struct
#[derive(Debug)]
pub struct Range(Option<usize>, Option<usize>);

impl Range {
    pub fn contains(&self, n: usize) -> bool {
        self.0.map_or(true, |bound| n >= bound) && self.1.map_or(true, |bound| n <= bound)
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Range(Some(a), Some(b)) if a == b => write!(f, "{}", a),
            Range(Some(a), Some(b)) => write!(f, "between {} and {}", a, b),
            Range(Some(a), None) => write!(f, "at least {}", a),
            Range(None, Some(b)) => write!(f, "up to {}", b),
            Range(None, None) => write!(f, "any number of"),
        }
    }
}

impl From<usize> for Range {
    fn from(n: usize) -> Self {
        Self(Some(n), Some(n))
    }
}

impl From<ops::Range<usize>> for Range {
    fn from(r: ops::Range<usize>) -> Self {
        Self(Some(r.start), Some(r.end - 1))
    }
}

impl From<ops::RangeFrom<usize>> for Range {
    fn from(r: ops::RangeFrom<usize>) -> Self {
        Self(Some(r.start), None)
    }
}

impl From<ops::RangeFull> for Range {
    fn from(_: ops::RangeFull) -> Self {
        Self(None, None)
    }
}

impl From<ops::RangeTo<usize>> for Range {
    fn from(r: ops::RangeTo<usize>) -> Self {
        Self(None, Some(r.end - 1))
    }
}

/// Provides a pretty displayable name for a type. For example, the type name for `Rc<Term>` is
/// "term".
pub trait TypeName {
    const NAME: &'static str;
}

impl TypeName for Rc<Term> {
    const NAME: &'static str = "term";
}

impl TypeName for Quantifier {
    const NAME: &'static str = "quantifier";
}

impl TypeName for BindingList {
    const NAME: &'static str = "binding list";
}