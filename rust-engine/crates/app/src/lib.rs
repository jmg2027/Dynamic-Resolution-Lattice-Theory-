//! DRLT 213 App — concrete physics observables.
//!
//! Phase 4: ships simplex, basel, alpha_em, certificate emitter for
//! the bracket_137 chain.  Entry binary: `alpha-em-bracket`.

pub mod simplex;
pub mod basel;
pub mod alpha_em;
pub mod alpha_em_with_tail;
pub mod alpha_em_so10_gram;
pub mod certificate;
pub mod gap_explorer;
pub mod wallis;

pub const LEAN_NAMESPACE: &str = "E213.App";
