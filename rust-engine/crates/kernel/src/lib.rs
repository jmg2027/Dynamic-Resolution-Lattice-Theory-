//! DRLT 213 Kernel — deep-embedded ℕ encoding, decidability primitives.
//!
//! Mirrors `lean/E213/Kernel/`.  Single allowed numeric carrier:
//! `num_bigint::BigUint`.  No `f32`/`f64`, no `unsafe`, no Q-algebra
//! type class — Lean has none.  Each public item declares
//! `LEAN_THM` (or its module declares the cited Lean namespace).

pub mod term;
pub mod compare;
pub mod rat;
pub mod normal_form;

pub use term::Term;

/// Citation marker — read by `verify-citations`.
pub const LEAN_NAMESPACE: &str = "E213.Kernel";
