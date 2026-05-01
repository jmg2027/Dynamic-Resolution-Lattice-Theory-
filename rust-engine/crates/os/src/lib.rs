//! DRLT 213 OS — Atomicity, Pigeonhole, Analysis213 algorithms.
//!
//! Phase 3: ships atomicity, arity (pigeonhole), canonical_part.
//! Phase 5+ grows `analysis213/` lazily as `app/` requires.

pub mod atomicity;
pub mod arity;
pub mod canonical_part;

pub use canonical_part::{canonical_split, canonical_split_consistent, D, N_S, N_T};
pub use atomicity::{
    atomic_decomps, canonical_partition_holds, closure_size_nondecomposable,
    decomp, is_alive, is_atomic, is_decomposable, is_non_decomposable,
    pair_size_nondecomposable, CLOSURE_SIZE, PAIR_SIZE,
};
pub use arity::{
    find_collision, pigeonhole_holds_universal_sample, reachable3,
    reachable_base_only, Raw3Tag,
};

pub const LEAN_NAMESPACE: &str = "E213.OS";
