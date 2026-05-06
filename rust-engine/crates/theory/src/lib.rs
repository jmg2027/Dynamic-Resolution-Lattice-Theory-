//! DRLT 213 Theory — Raw axiom + Atomicity (forced uniqueness).
//!
//! Mirrors Lean `E213.Theory.{Raw, Atomicity}` (post-M14 rename).
//!
//! - `raw`        : Raw opaque + canonical-form Tree (formerly
//!                  in firmware/)
//! - `lens`       : Lens type def (legacy locality — historically
//!                  hosted here for co-locality with raw; the
//!                  Lens algebra lives in the `lens/` crate)
//! - `atomicity`  : forced d=5 / (NS, NT) = (3, 2) proofs
//!                  (formerly in os/; absorbed in M14 Phase K2)

pub mod raw;
pub mod lens;
pub mod atomicity;

pub use raw::{Raw, NotEq, check_not_eq};
pub use lens::Lens;

pub use atomicity::canonical_part::{canonical_split, canonical_split_consistent, D, N_S, N_T};
pub use atomicity::atomicity::{
    atomic_decomps, canonical_partition_holds, closure_size_nondecomposable,
    decomp, is_alive, is_atomic, is_decomposable, is_non_decomposable,
    pair_size_nondecomposable, CLOSURE_SIZE, PAIR_SIZE,
};
pub use atomicity::arity::{
    find_collision, pigeonhole_holds_universal_sample, reachable3,
    reachable_base_only, Raw3Tag,
};

pub const LEAN_NAMESPACE: &str = "E213.Theory";
