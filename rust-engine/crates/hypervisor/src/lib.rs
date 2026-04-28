//! DRLT 213 Hypervisor — Lens instances + cohomology operators.
//!
//! Phase 0: ships canonical `lens_leaves` and `lens_depth` only.
//! Phase 1: adds `lens_chiral_k32` (paper 1 capstone).
//! Phase 2+: cohomology fold targets as Lens compositions.

pub mod canonical;
pub mod chiral_k32;
pub mod k32_graph;

pub use canonical::{lens_leaves, lens_depth};
pub use chiral_k32::{b1_bipartite, binom, chiral_dim, lens_st_count,
                     paper1_capstone_check};

pub const LEAN_NAMESPACE: &str = "E213.Hypervisor";
