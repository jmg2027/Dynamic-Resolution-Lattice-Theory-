import E213.Lib.Math.Analysis.ResolutionShift
import E213.Lib.Math.Analysis.ModulusMonoid
import E213.Meta.Tactic.NatHelper

/-!
# ResolutionQuantitative — the grade monoid measures resolution, exactly

`ModulusMonoid` showed the completion tower's bookkeeping is one commutative
monoid `(ℕ, +)` (carried pointwise), with `ResolutionShift`'s scalar grades
embedded as the constant sub-monoid.  That settled *that* grades compose
additively — but additively *over what*?  A grade was so far an abstract tag.

This file gives the tag its **quantitative meaning**: grade `n` is exactly "divide
the represented value by `2ⁿ`", i.e. multiply the cut's denominator by `2ⁿ`.

A `dyadicCut M E = constCut M (2^E)` represents the dyadic rational `M / 2^E`
(`Core/Dyadic`).  The grade-`n` shifter `cutHalfIter n` (n-fold `cutHalf`) sends it
to `dyadicCut M (E + n) = constCut M (2^(E+n))` — denominator `2^E ↦ 2^(E+n)`,
value `M/2^E ↦ M/2^(E+n) = (M/2^E)/2ⁿ`.  So:

  - `grade_scales_denominator` — grade `n` multiplies the denominator by `2ⁿ`;
  - `grade_add_multiplies` — composing grades `a, b` multiplies the scalings:
    `2^(a+b) = 2^a · 2^b`.  The grade monoid `(ℕ, +)` maps to the **denominator
    monoid (powers of 2, ×)** by a homomorphism (`a + b ↦ 2^a · 2^b`).  Additive
    grade ↔ multiplicative resolution.
  - grade is **measurable and unique** — `IsResolutionShift_grade_unique` already
    shows distinct grades produce distinct cuts at a test probe, so the
    quantitative reading is faithful: the resolution a shifter applies is a
    well-defined number, read off at a single query.

This closes the loop on the originator's thesis: the modulus is not abstract
bookkeeping — each grade *is* a measurable amount of resolution (`2ⁿ` finer), the
monoid law `a + b` *is* the composition of resolutions `2^a · 2^b`, and the whole
thing is tangible because the amount is read at one probe.

All ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.ResolutionQuantitative

open E213.Lib.Math.Analysis.ResolutionShift
open E213.Lib.Math.Analysis.ModulusMonoid (gradeToModulus madd)
open E213.Lib.Math.Real213.Core.Dyadic (dyadicCut)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — `2^(a+b) = 2^a · 2^b`, PURE (additive grade ↔ multiplicative scaling) -/

/-- `2^(a+b) = 2^a · 2^b` — the homomorphism `(ℕ,+) → (powers of 2, ×)`.  PURE
    (Lean-core `Nat.pow_add` pulls `propext`; this is induction with
    `NatHelper.mul_assoc`). -/
theorem two_pow_add (a b : Nat) : 2^(a+b) = 2^a * 2^b := by
  induction b with
  | zero => show 2^(a+0) = 2^a * 2^0; rw [Nat.add_zero, Nat.mul_one]
  | succ k ih =>
    show 2^(a+(k+1)) = 2^a * 2^(k+1)
    rw [show a+(k+1) = (a+k)+1 from rfl, Nat.pow_succ, ih, Nat.pow_succ]
    exact E213.Tactic.NatHelper.mul_assoc (2^a) (2^k) 2

/-! ## §2 — grade n = denominator scaled by 2^n -/

/-- ★★★ **Grade `n` scales the denominator by `2ⁿ`.**  Applying the grade-`n`
    shifter `cutHalfIter n` to `dyadicCut M E` (value `M/2^E`) yields the cut
    `constCut M (2^(E+n))` (value `M/2^(E+n)` = the value divided by `2ⁿ`).  The
    grade's abstract tag is exactly this much finer resolution. -/
theorem grade_scales_denominator (M E n m k : Nat) :
    cutHalfIter n (dyadicCut M E) m k = constCut M (2^(E + n)) m k := by
  rw [IsResolutionShift_cutHalfIter n M E m k]; rfl

/-- ★★★ **Grade addition multiplies the resolutions.**  Composing a grade-`a`
    then grade-`b` shift scales the denominator by `2^(a+b) = 2^a · 2^b` — the
    additive grade monoid maps onto the multiplicative resolution monoid.  Stated
    on the denominators reached: grade `a+b` from base `E` lands at `2^(E+(a+b))`,
    and `2^(a+b) = 2^a · 2^b`. -/
theorem grade_add_multiplies (a b : Nat) :
    (2:Nat)^(a + b) = 2^a * 2^b := two_pow_add a b

/-- ★★ The grade→modulus embedding (`ModulusMonoid.gradeToModulus`) composed with
    the denominator reading: grade `a + b` embeds as the constant modulus `a+b`,
    whose resolution is `2^(a+b) = 2^a·2^b`.  Ties the monoid hom of
    `ModulusMonoid` to the quantitative scaling here. -/
theorem gradeModulus_resolution (a b m k : Nat) :
    gradeToModulus (a + b) m k = madd (gradeToModulus a) (gradeToModulus b) m k
    ∧ (2:Nat)^(a + b) = 2^a * 2^b :=
  ⟨rfl, two_pow_add a b⟩

/-! ## §3 — the resolution is a faithful, measurable number -/

/-- ★★★ **Resolution is measurable and unique.**  A cut transformer carries *at
    most one* grade (`IsResolutionShift_grade_unique`): distinct grades are
    distinguished at a single test probe.  So "the amount of resolution `g`
    applies" is a well-defined number — the quantitative reading of §2 is
    faithful, not a choice. -/
theorem resolution_is_measurable
    {g : (Nat → Nat → Bool) → (Nat → Nat → Bool)} {E E' : Nat}
    (h : IsResolutionShift g E) (h' : IsResolutionShift g E') : E = E' :=
  IsResolutionShift_grade_unique h h'

/-- ★★ **Every resolution is realised.**  For each `n`, the grade-`n` shifter
    `cutHalfIter n` applies exactly `2ⁿ`-fold resolution (existence witness, via
    `IsResolutionShift_exists_at_grade`). -/
theorem resolution_realised (n : Nat) :
    IsResolutionShift (cutHalfIter n) n := IsResolutionShift_cutHalfIter n

end E213.Lib.Math.Analysis.ResolutionQuantitative
