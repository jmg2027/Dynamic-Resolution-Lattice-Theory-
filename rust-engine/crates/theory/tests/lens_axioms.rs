//! Integration tests — `Lens` axioms + asymmetric-combine guard.
//!
//! Lean: `lean/E213/Hypervisor/Lens.lean`.  Phase 1 promotes the
//! symmetry audit to `__new__` construction time.

use drlt_theory::{check_not_eq, Lens, Raw};

fn slash(x: Raw, y: Raw) -> Raw {
    let w = check_not_eq(&x, &y).expect("x ≠ y");
    Raw::slash(x, y, w)
}

fn add_lens() -> Lens<u64> {
    Lens::__new__("test.leaves", 1u64, 1u64, |a, b| a + b,
                  &[(1u64, 2), (3, 7)])
}

// ── Lens.equiv axioms ─────────────────────────────────────────────

#[test] fn lens_equiv_reflexive() {
    let r = slash(Raw::a(), Raw::b());
    assert!(add_lens().equiv(&r, &r));
}

#[test] fn lens_equiv_symmetric() {
    let l = add_lens();
    let x = slash(Raw::a(), Raw::b());
    let y = slash(Raw::b(), Raw::a());        // canonicalises to same
    assert!(l.equiv(&x, &y) && l.equiv(&y, &x));
}

#[test] fn lens_view_distinguishes_a_and_b() {
    let l: Lens<u64> = Lens::__new__("test.max", 0u64, 1u64,
        |a, b| std::cmp::max(*a, *b), &[(0u64, 1), (3, 7)]);
    assert_eq!(l.view(&Raw::a()), 0);
    assert_eq!(l.view(&Raw::b()), 1);
}

#[test] fn lens_carries_citation() {
    assert_eq!(add_lens().lean_thm(), "test.leaves");
}

// ── Construction-time symmetric audit (Phase 1 hardening) ─────────

#[test] #[should_panic(expected = "axiom violation")]
fn ctor_panics_on_first_projection() {
    let _: Lens<u64> = Lens::__new__("bad.first", 0u64, 1u64,
        |a, _| *a, &[(1u64, 2), (3, 7)]);
}

#[test] #[should_panic(expected = "axiom violation")]
fn ctor_panics_on_subtraction() {
    let _: Lens<u64> = Lens::__new__("bad.sub", 0u64, 0u64,
        |a, b| a.saturating_sub(*b), &[(7u64, 3), (2, 5)]);
}

#[test] #[should_panic(expected = "sym_samples must be non-empty")]
fn ctor_panics_on_empty_samples() {
    let _: Lens<u64> = Lens::__new__("bad.empty", 0u64, 0u64,
        |a, b| a + b, &[]);
}

#[test] fn ctor_accepts_addition() { let _ = add_lens(); }

#[test] fn ctor_accepts_one_plus_max() {
    let _: Lens<u64> = Lens::__new__("test.depth", 0u64, 0u64,
        |a, b| 1 + std::cmp::max(*a, *b),
        &[(0u64, 1), (3, 7), (5, 5)]);
}
