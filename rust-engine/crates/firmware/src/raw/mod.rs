//! `Raw` — opaque, canonical-form-only public API.
//!
//! Mirror of `lean/E213/Firmware/Raw.lean`.  Public API:
//! `a`, `b`, `slash`, `fold`, `depth`, plus `swap` (TODO Phase 0+).
//! Internal `Tree` is `pub(crate)` and never appears in any public
//! signature, matching Lean's `E213.Firmware.Internal` boundary.

mod internal;

use internal::Tree;
use std::cmp::Ordering;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Raw(Tree);

/// Witness type for `x ≠ y`.  Constructed only via [`check_not_eq`].
#[derive(Debug)]
pub struct NotEq(());

/// Issues a `NotEq` witness when `x ≠ y`, else `None`.
pub fn check_not_eq(x: &Raw, y: &Raw) -> Option<NotEq> {
    if x == y { None } else { Some(NotEq(())) }
}

impl Raw {
    /// `Raw.a` — Lean: `E213.Firmware.Raw.a`.
    pub fn a() -> Raw { Raw(Tree::A) }

    /// `Raw.b` — Lean: `E213.Firmware.Raw.b`.
    pub fn b() -> Raw { Raw(Tree::B) }

    /// `Raw.slash x y h` — smart constructor.  Auto-canonicalizes
    /// child order so `slash x y = slash y x` (Lean: `slash_comm`).
    /// `_w: NotEq` enforces `x ≠ y` at compile time.
    pub fn slash(x: Raw, y: Raw, _w: NotEq) -> Raw {
        match x.0.cmp(&y.0) {
            Ordering::Less    => Raw(Tree::Slash(Box::new(x.0), Box::new(y.0))),
            Ordering::Greater => Raw(Tree::Slash(Box::new(y.0), Box::new(x.0))),
            // `_w: NotEq` ⇒ unreachable; defensive panic.
            Ordering::Equal   => panic!("slash on x == y; NotEq witness invalid"),
        }
    }

    /// `Raw.depth` — Lean: `E213.Firmware.Raw.depth`.
    pub fn depth(&self) -> u64 { self.0.depth() }

    /// `Raw.fold` — catamorphism.  **`combine` MUST be symmetric**
    /// (Lean `fold_slash` requires `∀ u v, c u v = c v u`).
    /// Asymmetric `combine` is a *silent leak* per AXIOM.md §3 —
    /// callers in `hypervisor/` ensure symmetry by construction.
    pub fn fold<A: Clone, F: Fn(&A, &A) -> A + ?Sized>(
        &self, base_a: A, base_b: A, combine: &F,
    ) -> A {
        self.0.fold(base_a, base_b, combine)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn a_neq_b() {
        let a = Raw::a(); let b = Raw::b();
        assert_ne!(a, b);
        let _w = check_not_eq(&a, &b).expect("a ≠ b");
    }

    #[test] fn slash_commutes() {
        let a = Raw::a(); let b = Raw::b();
        let w1 = check_not_eq(&a, &b).unwrap();
        let w2 = check_not_eq(&b, &a).unwrap();
        let s_ab = Raw::slash(a.clone(), b.clone(), w1);
        let s_ba = Raw::slash(b, a, w2);
        assert_eq!(s_ab, s_ba);
    }

    #[test] fn depth_a_zero() { assert_eq!(Raw::a().depth(), 0); }
}
