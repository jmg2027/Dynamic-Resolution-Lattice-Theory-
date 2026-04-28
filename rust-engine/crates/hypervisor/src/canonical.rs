//! Canonical lenses: `leaves`, `depth`.
//!
//! Mirror of `lean/E213/Hypervisor/Lens.lean`:
//!
//! ```lean
//! def Lens.leaves : Lens Nat := ⟨1, 1, (· + ·)⟩
//! def Lens.depth  : Lens Nat := ⟨0, 0, fun a b => 1 + max a b⟩
//! ```
//!
//! Both `combine` ops are symmetric (`+` and `1 + max`), satisfying
//! the axiom-compliance requirement of `Raw.fold_slash`.

use drlt_firmware::Lens;

/// `Lens.leaves : Lens Nat` — counts base-object occurrences.
pub fn lens_leaves() -> Lens<u64> {
    Lens::__new__(
        "E213.Hypervisor.Lens.leaves", 1u64, 1u64, |a, b| a + b,
        &[(1u64, 2), (3, 7), (0, 5)],
    )
}

/// `Lens.depth : Lens Nat` — tree height.
pub fn lens_depth() -> Lens<u64> {
    Lens::__new__(
        "E213.Hypervisor.Lens.depth", 0u64, 0u64,
        |a, b| 1 + std::cmp::max(*a, *b),
        &[(0u64, 1), (3, 7), (5, 5)],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use drlt_firmware::Raw;

    /// Mirror of `Lens.leaves.view Raw.a = 1`.
    #[test] fn leaves_a()  { assert_eq!(lens_leaves().view(&Raw::a()), 1); }
    #[test] fn leaves_b()  { assert_eq!(lens_leaves().view(&Raw::b()), 1); }
    #[test] fn depth_a()   { assert_eq!(lens_depth().view(&Raw::a()),  0); }
    #[test] fn depth_b()   { assert_eq!(lens_depth().view(&Raw::b()),  0); }
}
