//! Integration tests — `Raw` axioms + 213 axiom violation guards.
//!
//! Maps to `lean/E213/Firmware/Raw/*.lean` public API.

use drlt_firmware::{check_not_eq, Raw};

fn slash(x: Raw, y: Raw) -> Raw {
    let w = check_not_eq(&x, &y).expect("x ≠ y");
    Raw::slash(x, y, w)
}

// ── Axiom: two distinct base entities exist ───────────────────────

#[test] fn axiom_two_distinct_bases() { assert_ne!(Raw::a(), Raw::b()); }

#[test] fn axiom_a_neq_a_witness_unavailable() {
    assert!(check_not_eq(&Raw::a(), &Raw::a()).is_none());
}
#[test] fn axiom_b_neq_b_witness_unavailable() {
    assert!(check_not_eq(&Raw::b(), &Raw::b()).is_none());
}

// ── slash_comm: distinction is directionless (axiom §3) ───────────

#[test] fn slash_comm_a_b() {
    assert_eq!(slash(Raw::a(), Raw::b()), slash(Raw::b(), Raw::a()));
}

#[test] fn slash_comm_nested() {
    let l = slash(slash(Raw::a(), Raw::b()), Raw::a());
    let r = slash(Raw::a(), slash(Raw::a(), Raw::b()));
    assert_eq!(l, r);
}

// ── depth observable ──────────────────────────────────────────────

#[test] fn depth_a_zero()        { assert_eq!(Raw::a().depth(), 0); }
#[test] fn depth_b_zero()        { assert_eq!(Raw::b().depth(), 0); }
#[test] fn depth_slash_a_b_one() {
    assert_eq!(slash(Raw::a(), Raw::b()).depth(), 1);
}
#[test] fn depth_slash_slash_two() {
    let ab = slash(Raw::a(), Raw::b());
    assert_eq!(slash(ab, Raw::a()).depth(), 2);
}

// ── fold smoke (Lean fold_a, fold_b) ──────────────────────────────

#[test] fn fold_a_returns_base_a() {
    assert_eq!(Raw::a().fold(7u64, 99u64, &|a, _| *a), 7);
}
#[test] fn fold_b_returns_base_b() {
    assert_eq!(Raw::b().fold(7u64, 99u64, &|_, b| *b), 99);
}

#[test] fn fold_slash_symmetric_combine_invariant() {
    let combine = |a: &u64, b: &u64| a + b;        // symmetric
    let lab = slash(Raw::a(), Raw::b()).fold(1u64, 1u64, &combine);
    let lba = slash(Raw::b(), Raw::a()).fold(1u64, 1u64, &combine);
    assert_eq!(lab, 2);
    assert_eq!(lab, lba);
}

// ── Axiom violation guard: slash(x, x) cannot be constructed ──────

/// 213 axiom requires `x ≠ y` for `slash`.  No `NotEq` witness can be
/// obtained for identical Raws — type-level enforcement.
#[test] fn axiom_violation_self_slash_is_blocked() {
    let r = slash(Raw::a(), Raw::b());
    assert!(check_not_eq(&r, &r.clone()).is_none(),
        "x ≠ x must never produce a NotEq witness");
}
