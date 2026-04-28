//! DRLT 213 Hypervisor — Lens instances + cohomology operators.
//!
//! Phase 0: ships canonical `lens_leaves` and `lens_depth` only.
//! Phase 1: adds `lens_chiral_k32` (paper 1 capstone).
//! Phase 2+: cohomology fold targets as Lens compositions.

pub mod canonical;

pub use canonical::{lens_leaves, lens_depth};

pub const LEAN_NAMESPACE: &str = "E213.Hypervisor";
