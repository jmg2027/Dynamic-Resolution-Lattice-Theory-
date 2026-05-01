//! Integration tests — Atomicity, NonDecomposable, PrimitiveSizes.
//!
//! Maps to `lean/E213/OS/{Atomicity, Alive, NonDecomposable,
//! PrimitiveSizes}.lean`.

use drlt_os::{
    atomic_decomps, canonical_partition_holds, closure_size_nondecomposable,
    decomp, is_alive, is_atomic, is_decomposable, is_non_decomposable,
    pair_size_nondecomposable, CLOSURE_SIZE, PAIR_SIZE,
};

// ── decomp + is_alive smoke ───────────────────────────────────────

#[test] fn decomp_5_eq_2_plus_3() {
    assert!(decomp(5, 1, 1));        // 5 = 2·1 + 3·1
    assert!(decomp(5, 1, 1) && !decomp(5, 1, 2));
}

#[test] fn alive_iff_both_odd() {
    assert!(is_alive(1, 1)); assert!(is_alive(3, 5));
    assert!(!is_alive(2, 1)); assert!(!is_alive(1, 2));
    assert!(!is_alive(0, 0)); assert!(!is_alive(2, 2));
}

// ── atomic_iff_five (Lean main theorem) ───────────────────────────

/// Lean: `atomic_five : Atomic 5`.
#[test] fn atomic_five() { assert!(is_atomic(5)); }

/// Lean: `atomic_iff_five` ∀ n. `Atomic n ↔ n = 5`.
#[test] fn atomic_iff_five_for_n_lt_20() {
    for n in 0..20 {
        assert_eq!(is_atomic(n), n == 5,
            "is_atomic({n}) ≠ (n == 5)");
    }
}

/// Lean: `canonical_partition` — alive decomp of 5 ⟹ (1, 1).
#[test] fn canonical_partition() { assert!(canonical_partition_holds()); }

#[test] fn decomps_of_5_is_singleton_one_one() {
    assert_eq!(atomic_decomps(5), vec![(1, 1)]);
}

#[test] fn decomps_of_6_is_two_one_three_zero() {
    assert_eq!(atomic_decomps(6), vec![(0, 2), (3, 0)]);
}

// ── PrimitiveSizes mirror ─────────────────────────────────────────

#[test] fn pair_size_is_two()        { assert_eq!(PAIR_SIZE, 2); }
#[test] fn closure_size_is_three()   { assert_eq!(CLOSURE_SIZE, 3); }

/// Lean: `pairSize_nondecomposable : NonDecomposable 2`.
#[test] fn pair_size_nondec()        { assert!(pair_size_nondecomposable()); }

/// Lean: `closureSize_nondecomposable : NonDecomposable 3`.
#[test] fn closure_size_nondec()     { assert!(closure_size_nondecomposable()); }

// ── NonDecomposable detail ────────────────────────────────────────

#[test] fn five_is_decomposable()    { assert!(is_decomposable(5)); }     // 2+3
#[test] fn six_is_decomposable()     { assert!(is_decomposable(6)); }     // not really alive but decomp
#[test] fn two_is_nondecomposable()  { assert!(is_non_decomposable(2)); }
#[test] fn three_is_nondecomposable(){ assert!(is_non_decomposable(3)); }

// ── Negative axiom-violation guards ───────────────────────────────

#[test] fn atomic_zero_is_false()    { assert!(!is_atomic(0)); }
#[test] fn atomic_six_is_false()     { assert!(!is_atomic(6)); }   // 2 decomps
#[test] fn atomic_seven_is_false()   { assert!(!is_atomic(7)); }   // (2,1) not alive
