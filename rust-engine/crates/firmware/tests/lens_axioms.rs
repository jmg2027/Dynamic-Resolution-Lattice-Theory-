//! Integration tests — `Lens` axioms + asymmetric-combine guard.
//!
//! Lean: `lean/E213/Hypervisor/Lens.lean`.  Lens with asymmetric
//! `combine` is a *silent leak* per `Raw.fold_slash` (axiom §3).
//! These tests fence that guarantee.

use drlt_firmware::{check_not_eq, Lens, Raw};

fn slash(x: Raw, y: Raw) -> Raw {
    let w = check_not_eq(&x, &y).expect("x ≠ y");
    Raw::slash(x, y, w)
}

// ── Lens.equiv axioms ─────────────────────────────────────────────

#[test] fn lens_equiv_reflexive() {
    let l: Lens<u64> = Lens::__new__("test.leaves", 1u64, 1u64, |a, b| a + b);
    let r = slash(Raw::a(), Raw::b());
    assert!(l.equiv(&r, &r));
}

#[test] fn lens_equiv_symmetric() {
    let l: Lens<u64> = Lens::__new__("test.leaves", 1u64, 1u64, |a, b| a + b);
    let x = slash(Raw::a(), Raw::b());
    let y = slash(Raw::b(), Raw::a());        // canonicalises to same
    assert!(l.equiv(&x, &y) && l.equiv(&y, &x));
}

#[test] fn lens_view_distinguishes_a_and_b_when_intended() {
    // First-projection lens: base_a = 0, base_b = 1.
    let l: Lens<u64> = Lens::__new__("test.first", 0u64, 1u64, |a, _| *a);
    assert_eq!(l.view(&Raw::a()), 0);
    assert_eq!(l.view(&Raw::b()), 1);
}

// ── Lean theorem citation present ─────────────────────────────────

#[test] fn lens_carries_citation() {
    let l: Lens<u64> = Lens::__new__(
        "E213.Hypervisor.Lens.leaves", 1u64, 1u64, |a, b| a + b,
    );
    assert_eq!(l.lean_thm(), "E213.Hypervisor.Lens.leaves");
}

// ── Axiom violation guard: asymmetric combine is detectable ───────

/// `combine` symmetry audit — to be promoted to a construction-time
/// check in Phase 1.  213 axiom requires `combine u v = combine v u`.
fn audit_symmetric<A: Clone + PartialEq>(
    combine: impl Fn(&A, &A) -> A, samples: &[(A, A)],
) -> bool {
    samples.iter().all(|(u, v)| combine(u, v) == combine(v, u))
}

#[test] fn audit_passes_for_addition() {
    let combine = |a: &u64, b: &u64| a + b;
    assert!(audit_symmetric(combine, &[(1u64, 2), (3, 7), (0, 5)]));
}

#[test] fn audit_passes_for_one_plus_max() {
    let combine = |a: &u64, b: &u64| 1 + std::cmp::max(*a, *b);
    assert!(audit_symmetric(combine, &[(1u64, 2), (3, 7), (5, 5)]));
}

#[test] fn axiom_violation_first_projection_flagged() {
    // Asymmetric: result depends on argument order → axiom §3 leak.
    let combine = |a: &u64, _: &u64| *a;
    assert!(!audit_symmetric(combine, &[(1u64, 2), (3, 7)]),
        "asymmetric combine must be flagged");
}

#[test] fn axiom_violation_subtraction_flagged() {
    let combine = |a: &u64, b: &u64| a.saturating_sub(*b);
    assert!(!audit_symmetric(combine, &[(7u64, 3), (2, 5)]));
}
