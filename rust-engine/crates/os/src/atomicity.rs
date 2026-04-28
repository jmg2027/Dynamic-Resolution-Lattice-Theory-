//! Atomicity — n = 5 is the unique atomic ℕ given atoms {2, 3}.
//!
//! Mirrors `lean/E213/OS/{Atomicity, Alive, NonDecomposable,
//! PrimitiveSizes}.lean`.  All ℕ-valued, finite-search-decidable.

/// Lean: `Atomicity.Decomp n a b := n = 2·a + 3·b`.
pub fn decomp(n: u64, a: u64, b: u64) -> bool { n == 2 * a + 3 * b }

/// Lean: `Atomicity.IsAlive a b := a%2=1 ∧ b%2=1` (both odd).
/// Equivalent to `Alive.alive_iff_odd_pair`.
pub fn is_alive(a: u64, b: u64) -> bool { a % 2 == 1 && b % 2 == 1 }

/// All (a, b) with `decomp n a b`.
pub fn atomic_decomps(n: u64) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let max_a = n / 2;
    for a in 0..=max_a {
        let rem = n - 2 * a;
        if rem % 3 == 0 { out.push((a, rem / 3)); }
    }
    out
}

/// Lean: `Atomicity.Atomic n` ⟺ unique decomp + that decomp alive.
/// `atomic_iff_five : Atomic n ↔ n = 5`.
pub fn is_atomic(n: u64) -> bool {
    let ds = atomic_decomps(n);
    ds.len() == 1 && is_alive(ds[0].0, ds[0].1)
}

/// Lean: `canonical_partition` — every alive decomp of 5 is (1, 1).
pub fn canonical_partition_holds() -> bool {
    for a in 0..=5 {
        for b in 0..=5 {
            if decomp(5, a, b) && is_alive(a, b) && (a, b) != (1, 1) {
                return false;
            }
        }
    }
    true
}

// ── PrimitiveSizes mirror ─────────────────────────────────────────

/// Lean: `PrimitiveSizes.pairSize := 2`.
pub const PAIR_SIZE: u64 = 2;

/// Lean: `PrimitiveSizes.closureSize := 3`.
pub const CLOSURE_SIZE: u64 = 3;

// ── NonDecomposable mirror ────────────────────────────────────────

/// Lean: `NonDecomposable.Decomposable n := ∃ a b ≥ 2, a + b = n`.
pub fn is_decomposable(n: u64) -> bool {
    if n < 4 { return false; }
    // a ≥ 2 ∧ b ≥ 2 ∧ a + b = n  ⇔  n ≥ 4.
    // Witness: a = 2, b = n - 2 (b ≥ 2 since n ≥ 4).
    true
}

/// Lean: `NonDecomposable.NonDecomposable n := n ≥ 2 ∧ ¬ Decomposable n`.
pub fn is_non_decomposable(n: u64) -> bool { n >= 2 && !is_decomposable(n) }

/// Lean: `primitive_sizes_eq_nondecomposable` — n is non-decomposable
/// iff n ∈ {2, 3, 1, 0}.  We mirror the affirmative half: pairSize
/// and closureSize are non-decomposable.
pub fn pair_size_nondecomposable()    -> bool { is_non_decomposable(PAIR_SIZE) }
pub fn closure_size_nondecomposable() -> bool { is_non_decomposable(CLOSURE_SIZE) }
