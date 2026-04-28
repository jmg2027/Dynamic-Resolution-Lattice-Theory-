//! DRLT 213 Firmware — `Raw` opaque + `Lens` sealed.
//!
//! Mirrors `lean/E213/Firmware/` (`Raw`) and
//! `lean/E213/Hypervisor/Lens.lean` (`Lens`).
//!
//! `Raw` wraps a canonical-form `Tree`; the internal representation
//! is `pub(crate)` and never escapes.  `slash` is a smart constructor
//! that auto-canonicalizes child order, mirroring `Raw.slash_comm`.
//!
//! `Lens<A>` is sealed: only `Lens::__new__` (crate-internal) can
//! construct one, ensuring every `Lens` instance carries a Lean
//! theorem citation.

pub mod raw;
pub mod lens;

pub use raw::{Raw, NotEq, check_not_eq};
pub use lens::Lens;

pub const LEAN_NAMESPACE: &str = "E213.Firmware";
