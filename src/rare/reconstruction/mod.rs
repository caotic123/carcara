//! Post-hoc certificate reconstruction from a provenance-free saturated
//! e-graph: the checker-side pipeline that turns an egglog run into an
//! independently verifiable equality certificate.
pub mod certificate;
pub mod computation;
pub mod program;
pub mod search;
pub mod snapshot;
pub mod term;

#[cfg(test)]
mod tests;

pub use certificate::*;
pub use computation::*;
pub use program::*;
pub use search::*;
pub use snapshot::*;
pub use term::*;
