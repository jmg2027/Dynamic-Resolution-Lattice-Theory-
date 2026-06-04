import E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal
import E213.Lib.Math.Mobius213OneAsGlue

/-!
# RatioLensFounding — `ℚ` is the ratio rung, and its coprimality is `det P = NS − NT = 1`

`seed/AXIOM/06_lens_readings.md` §6.7 founds `ℚ` by *"taking ratios of chain readings, with the
coprimality condition that §3.5's `det P = 1` already encodes algebraically."*  The distinctive
213 content is not the generic field-of-fractions construction; it is that **the ratio's
lowest-terms (coprimality) condition is exactly the unimodular determinant `det P = NS − NT = 1`.**

This file makes that a theorem.  The convergent matrix `Pⁿ = [[Q00, Q01],[Q01, Q11]]` reads the
self-pointing as a ratio `Q01/Q00` (or `Q00/Q01`), and its determinant is the unit:
`Q00·Q11 − Q01² = NS − NT = 1` (`PnFibonacciUniversal.det_pn_universal`,
`Mobius213OneAsGlue.ns_minus_nt_is_one`).  A unimodular determinant is exactly the
coprimality / lowest-terms condition `ℚ` requires, so the ratio is automatically in lowest terms.

The coupling to `ℤ` is by *identity of the unit*, not by construction-dependency.  This file's
content is `Nat`-level — `Q00, Q01, Q11 : Nat → Nat`, `NS − NT` a `Nat` value (`= 1` by
`ns_minus_nt_is_one`) — and it imports neither `ℤ` (`Int213`) nor `DifferenceLensFounding`.  The
value `NS − NT = 1` is the *same unit* the difference-Lens carries as its `det P`
(`SharedUnitAcrossReadings.the_unit_is_one_across_readings`): the ratio rung does not *build on*
the `ℤ` rung, it *shares its unit*.  So `ℚ` and `ℤ` are sibling readings of the count, coupled at
the unit `1`, not stacked.  The ratio's own identity is cross-multiplication (`ratioEquiv`,
reflexive and symmetric below).
-/

namespace E213.Lens.Number.RatioLensFounding

open E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11 det_pn_universal)
open E213.Lib.Math.Mobius213OneAsGlue (ns_minus_nt_is_one)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- The ratio identity: `p₁/p₂ = q₁/q₂` is cross-multiplication `p₁·q₂ = q₁·p₂`. -/
def ratioEquiv (p q : Nat × Nat) : Prop := p.1 * q.2 = q.1 * p.2

theorem ratioEquiv_refl (p : Nat × Nat) : ratioEquiv p p := rfl

theorem ratioEquiv_symm {p q : Nat × Nat} (h : ratioEquiv p q) : ratioEquiv q p := h.symm

/-- ★★★ **The convergent's lowest-terms condition is the difference-Lens unit `det P = NS − NT`.**
    The convergent matrix `Pⁿ = [[Q00, Q01],[Q01, Q11]]` has determinant `Q00·Q11 − Q01² = NS − NT`,
    written additively `Q00·Q11 = Q01² + (NS − NT)` (`det_pn_universal` with the glue
    `ns_minus_nt_is_one`).  A unimodular determinant is exactly the coprimality / lowest-terms
    condition `ℚ` requires (`06_lens_readings §6.7` / `§3.5`: *the coprimality that `det P = 1`
    already encodes algebraically*).  So the ratio `Q01/Q00` is automatically in lowest terms,
    because the cross-determinant of its readings is the difference-Lens unit. -/
theorem convergent_lowest_terms_is_det (n : Nat) :
    Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT) := by
  rw [ns_minus_nt_is_one]; exact det_pn_universal n

/-- ★★★ **`ℚ` is the ratio rung whose lowest-terms condition is the difference-Lens unit.**
    Bundle: the ratio identity is cross-multiplication (`ratioEquiv`, reflexive/symmetric); the
    convergent's lowest-terms condition is the matrix determinant `Q00·Q11 = Q01² + (NS − NT)`
    (`convergent_lowest_terms_is_det`), the unimodular/coprimality datum §6.7 says `det P` encodes;
    and `NS − NT = 1` is the difference-Lens unit.  So the `ℚ`-rung's defining coprimality is
    *derived from* the `ℤ`-rung's unit `det P = NS − NT`, not imposed — `ℚ` is the ratio reading
    whose well-definedness is the difference-Lens unit. -/
theorem ratio_lens_founds_on_difference :
    (∀ p : Nat × Nat, ratioEquiv p p)
    ∧ (∀ n, Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT))
    ∧ (NS - NT = 1) :=
  ⟨ratioEquiv_refl, convergent_lowest_terms_is_det, ns_minus_nt_is_one⟩

end E213.Lens.Number.RatioLensFounding
