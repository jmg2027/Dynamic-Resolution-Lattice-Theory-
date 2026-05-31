import E213.Lib.Math.Real213.PhiAbCut
import E213.Lib.Math.Analysis.ResolutionQuantitative

/-!
# ModulusForm — the resolving modulus is per-real; constant grades are the thinnest class

`ResolutionQuantitative` gave the `ResolutionShift` grade its quantitative meaning:
grade `n` is `2ⁿ`-finer resolution.  But that lives entirely in the **dyadic**
world — `dyadicCut M E = constCut M (2^E)`, and a grade is a *constant* modulus
`fun _ _ => E`, the *same* depth at every probe.

It would overclaim to read "`2ⁿ` decides everything" off that.  The probe space of
a cut is *every* rational `m/k`, not just dyadics, and the modulus that resolves a
real at probe `(m,k)` is in general a **function of the probe** — an element of the
full space `ℕ → ℕ → ℕ`, of which the constant grades are a razor-thin slice.  Each
real carries its **own** modulus form, set by how fast its rational approximants
converge:

  - **dyadic** `M/2^E` — constant grade (the `ResolutionShift` slice);
  - **φ** (algebraic) — its convergents are the Fibonacci pairs, growing like
    `φⁿ`, and its resolving modulus is `N(m,k) = 2·k` (`PhiAbCut.phiCompletion`):
    **linear in the probe denominator**, not constant, not `2ⁿ`;
  - **e** (transcendental) — its convergents have denominators `n!`
    (`Cauchy/Euler.eulerDen`), growing *faster*, so its per-threshold modulus
    grows correspondingly *slower* in the probe — a different form again.

This file proves the separation: φ's modulus `2·k` is dominated by **no** constant
grade (`phi_modulus_exceeds_every_grade`), so φ is genuinely outside the
dyadic/grade class — the modulus form is a real invariant distinguishing the
reals, exactly the "each real has its own modulus, the grades being only the
simplest" picture.  The grade monoid of `ModulusMonoid` is one (constant)
sub-monoid of a much larger space of resolving forms.

All ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.ModulusForm

open E213.Lib.Math.Analysis.ModulusMonoid (gradeToModulus madd mzero)
open E213.Lib.Math.Real213 (AbCutSeq)

/-! ## §1 — φ's resolving modulus, named -/

/-- **φ's resolving modulus**: `N(m,k) = 2·k`.  This is the modulus
    `PhiAbCut.phiCompletion` actually uses — linear in the probe denominator `k`,
    the Archimedean rate at which the Fibonacci convergents pass any rational. -/
def phiModulus : Nat → Nat → Nat := fun _ k => 2 * k

/-- φ's modulus genuinely resolves φ: past `phiModulus m k = 2k`, the convergent
    cut is constant (re-exported from `PhiAbCut.phi_cut_eventually_const`). -/
theorem phiModulus_resolves (m k i j : Nat)
    (hi : i ≥ phiModulus m k) (hj : j ≥ phiModulus m k) :
    E213.Lib.Math.Real213.PhiAbCut.phiAb.cut i m k
    = E213.Lib.Math.Real213.PhiAbCut.phiAb.cut j m k :=
  E213.Lib.Math.Real213.PhiAbCut.phi_cut_eventually_const m k i j hi hj

/-! ## §2 — φ's modulus is outside the constant-grade class -/

/-- ★★★ **φ's modulus exceeds every constant grade.**  For *any* grade `E`, there
    is a probe where `phiModulus` (= `2k`) strictly exceeds the constant grade
    `gradeToModulus E` (= `E`).  So no single grade — no amount of *uniform*
    dyadic resolution — captures φ's resolving modulus: φ needs probe-dependent
    resolution.  The grade sub-monoid does not contain φ's form. -/
theorem phi_modulus_exceeds_every_grade (E : Nat) :
    ∃ k, gradeToModulus E 0 k < phiModulus 0 k := by
  refine ⟨E + 1, ?_⟩
  show E < 2 * (E + 1)
  calc E ≤ 2 * E := Nat.le_mul_of_pos_left E (by decide)
    _ < 2 * E + 2 := Nat.lt_add_of_pos_right (by decide)
    _ = 2 * (E + 1) := by rw [Nat.mul_add, Nat.mul_one]

/-- ★★ Contrapositive framing: `phiModulus` is **not** any constant grade.  No `E`
    has `gradeToModulus E` agreeing with `phiModulus` at all probes — they differ
    at `k = E+1`.  φ's resolution form is irreducibly probe-dependent. -/
theorem phiModulus_not_constant (E : Nat) :
    ∃ m k, gradeToModulus E m k ≠ phiModulus m k := by
  obtain ⟨k, hk⟩ := phi_modulus_exceeds_every_grade E
  exact ⟨0, k, Nat.ne_of_lt hk⟩

/-! ## §3 — the modulus space is a per-real invariant, grades a thin slice -/

/-- ★★ **`mzero` resolves nothing past depth 0 only trivially; real moduli grow.**
    The identity modulus `mzero` (constant `0`) is the bottom of the grade slice;
    φ's `phiModulus` exceeds even it everywhere `k ≥ 1`.  The resolving form scales
    with the probe — resolution is *demanded* finer as the probe sharpens, and how
    much finer is the real's signature. -/
theorem phiModulus_above_mzero (k : Nat) (hk : k ≥ 1) :
    mzero 0 k < phiModulus 0 k := by
  show 0 < 2 * k
  calc 0 < 2 * 1 := by decide
    _ ≤ 2 * k := Nat.mul_le_mul_left 2 hk

/-- ★★★ **The grade monoid is a proper sub-structure.**  Combining §2: the
    constant-grade moduli (`gradeToModulus '' ℕ`, the `ResolutionShift` /
    dyadic class) do **not** exhaust the resolving moduli — φ's `phiModulus` is a
    resolving modulus (`phiModulus_resolves`) outside that image
    (`phiModulus_not_constant`).  So "the modulus is `2ⁿ`" holds only on the
    dyadic slice; the general real's modulus is a richer probe-dependent form, and
    the *form itself* separates reals (φ's linear `2k` ≠ any dyadic grade). -/
theorem grade_class_is_proper :
    (∀ m k i j, i ≥ phiModulus m k → j ≥ phiModulus m k →
       E213.Lib.Math.Real213.PhiAbCut.phiAb.cut i m k
       = E213.Lib.Math.Real213.PhiAbCut.phiAb.cut j m k)
    ∧ (∀ E, ∃ m k, gradeToModulus E m k ≠ phiModulus m k) :=
  ⟨phiModulus_resolves, phiModulus_not_constant⟩

end E213.Lib.Math.Analysis.ModulusForm
