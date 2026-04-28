//! `Lens` — sealed catamorphism wrapper.
//!
//! Mirror of `lean/E213/Hypervisor/Lens.lean`:
//!
//! ```lean
//! structure Lens (α : Type) where
//!   base_a  : α
//!   base_b  : α
//!   combine : α → α → α
//! def Lens.view  (L) (r : Raw) : α := r.fold L.base_a L.base_b L.combine
//! def Lens.equiv (L) (x y : Raw) : Prop := L.view x = L.view y
//! ```
//!
//! Sealed: only `Lens::__new__` (crate-internal) constructs.  Every
//! caller (in `hypervisor/`) supplies a `lean_thm` citation string
//! and a *symmetric* `combine` (axiom requirement, §3).

use crate::raw::Raw;
use std::sync::Arc;

mod sealed { pub trait LensSeal {} }

#[derive(Clone)]
pub struct Lens<A: Clone> {
    base_a: A,
    base_b: A,
    combine: Arc<dyn Fn(&A, &A) -> A + Send + Sync>,
    lean_thm: &'static str,
    _seal: std::marker::PhantomData<dyn sealed::LensSeal + Send + Sync>,
}

impl<A: Clone> Lens<A> {
    /// Crate-internal constructor.  Public factories live in the
    /// `hypervisor` crate and pass through here.  Do NOT relax to
    /// `pub` — that breaks the citation guarantee.
    #[doc(hidden)]
    pub fn __new__<F>(lean_thm: &'static str, base_a: A, base_b: A, combine: F) -> Self
    where F: Fn(&A, &A) -> A + Send + Sync + 'static,
    {
        Lens {
            base_a, base_b, combine: Arc::new(combine), lean_thm,
            _seal: std::marker::PhantomData,
        }
    }

    /// `Lens.view` — apply catamorphism.  Lean:
    /// `E213.Hypervisor.Lens.view`.
    pub fn view(&self, r: &Raw) -> A {
        r.fold(self.base_a.clone(), self.base_b.clone(), &*self.combine)
    }

    /// `Lens.equiv` — Bool form (Lean is Prop).  Lean:
    /// `E213.Hypervisor.Lens.equiv`.
    pub fn equiv(&self, x: &Raw, y: &Raw) -> bool
    where A: PartialEq {
        self.view(x) == self.view(y)
    }

    /// Lean theorem citation for this lens instance.
    pub fn lean_thm(&self) -> &'static str { self.lean_thm }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Mirror of canonical `Lens.leaves` smoke test:
    /// `Lens.leaves.view Raw.a = 1`.
    #[test] fn leaves_a_is_one() {
        let lens: Lens<u64> = Lens::__new__(
            "E213.Hypervisor.Lens.leaves", 1u64, 1u64, |a, b| a + b,
        );
        assert_eq!(lens.view(&Raw::a()), 1);
        assert_eq!(lens.view(&Raw::b()), 1);
    }
}
