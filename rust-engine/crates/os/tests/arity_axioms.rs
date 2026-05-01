//! Integration tests — Pigeonhole + ArityForcing.
//!
//! Maps to `lean/E213/OS/{Pigeonhole, ArityForcing,
//! ArityForcingGeneral}.lean`.

use drlt_os::{
    find_collision, pigeonhole_holds_universal_sample, reachable3,
    reachable_base_only, Raw3Tag,
};

// ── Pigeonhole: when N < k, some i ≠ j collide ────────────────────

#[test] fn collision_found_when_n_lt_k() {
    let g = |i: u64| i % 2;          // Fin 5 → Fin 2
    let c = find_collision(2, 5, &g);
    assert!(c.is_some());
}

#[test] fn no_collision_when_g_injective() {
    // Fin 3 → Fin 3, identity — injective.
    let g = |i: u64| i;
    assert!(find_collision(3, 3, &g).is_none());
}

#[test] fn pigeonhole_sample_holds_for_2_lt_5() {
    assert!(pigeonhole_holds_universal_sample(2, 5));
}

#[test] fn pigeonhole_sample_holds_for_1_lt_3() {
    assert!(pigeonhole_holds_universal_sample(1, 3));
}

#[test] fn pigeonhole_trivial_when_n_geq_k() {
    assert!(pigeonhole_holds_universal_sample(5, 3));
}

// ── ArityForcing: only obj is reachable ───────────────────────────

/// Lean: `ArityForcing.reachable3_only_object` —
/// `Reachable3 (rel3 _ _ _) → False`.
#[test] fn rel3_not_reachable() { assert!(!reachable3(Raw3Tag::Rel3)); }

/// Lean: implicit `obj_reachable` base case.
#[test] fn obj_reachable() { assert!(reachable3(Raw3Tag::Obj)); }

// ── ArityForcingGeneral: N < k forces base only ───────────────────

/// Lean: `ArityForcingGeneral.reachable_base_only` ∀ N k. N < k →
/// no rel_k reachable.
#[test] fn arity_forcing_general() {
    assert!(reachable_base_only(2, 3));
    assert!(reachable_base_only(0, 5));
    assert!(!reachable_base_only(3, 2));
    assert!(!reachable_base_only(5, 5));      // N = k: not strict
}

// ── Concrete 213 fact: 5 atoms cannot host arity-6+ relations ─────

/// In 213 with d = 5 atoms, any arity-6 relation forces a collision.
#[test] fn arity_six_blocked_for_d_five() {
    assert!(reachable_base_only(5, 6));
}
