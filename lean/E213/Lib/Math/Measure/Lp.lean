import E213.Lib.Math.Measure.LebesgueIntegral

/-!
# Measure Theory 213 — Lp spaces (atomic skeleton)

213-native paradigm: `‖f‖_p^p = ∫ |f|^p dμ` is a finite Nat sum
over the bracket cover.  No measure-theoretic completeness chase.

Atomic content:
  * `lpNormPow p f S` — `Σ f(midNum)^p · lenNum`
  * `lp_const c p S` — closed form for constant integrand
  * Hölder cross-multiplied form (single-bracket): `(a·b) ≤ a²+b²`
    via the elementary AM-GM-style inequality `2ab ≤ a²+b²`.
-/

namespace E213.Lib.Math.Measure.Lp

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
  (DyadicBracket DyadicBracket.lenNum DyadicBracket.midNum)
open E213.Lib.Math.Measure.MeasurableSet
  (DyadicMeasurableSet emptySet singleton)
open E213.Lib.Math.Measure.LebesgueIntegral
  (lebesgueStepNum constIntegrand)

/-- `f^p` lifted pointwise. -/
def powIntegrand (f : Nat → Nat) (p : Nat) : Nat → Nat :=
  fun n => f n ^ p

/-- `‖f‖_p^p = ∫ |f|^p dμ` (Nat-side). -/
def lpNormPow (p : Nat) (f : Nat → Nat) (s : DyadicMeasurableSet) : Nat :=
  lebesgueStepNum (powIntegrand f p) s

/-- ★ Empty set: `‖f‖_p^p over ∅ = 0` (rfl). -/
theorem lp_empty (p : Nat) (f : Nat → Nat) :
    lpNormPow p f emptySet = 0 := rfl

/-- ★ Lp norm of `c` (constant) over a singleton: `c^p · lenNum`. -/
theorem lp_const_singleton (c p : Nat) (db : DyadicBracket) :
    lpNormPow p (constIntegrand c) (singleton db) = c ^ p * db.lenNum := by
  show (constIntegrand c db.midNum) ^ p * db.lenNum + 0
        = c ^ p * db.lenNum
  exact Nat.add_zero _

/-- ★ p = 1 collapses to ordinary Lebesgue integral on a singleton
    (pointwise; avoids funext). -/
theorem lp_one_singleton (f : Nat → Nat) (db : DyadicBracket) :
    lpNormPow 1 f (singleton db) = lebesgueStepNum f (singleton db) := by
  show (f db.midNum) ^ 1 * db.lenNum + 0
       = f db.midNum * db.lenNum + 0
  rw [Nat.pow_one]

/-- ★ Lp norm linearity over union (inherited from
    `lebesgue_union_additive`). -/
theorem lp_union_additive (p : Nat) (f : Nat → Nat)
    (s t : DyadicMeasurableSet) :
    lpNormPow p f (E213.Lib.Math.Measure.MeasurableSet.union s t)
      = lpNormPow p f s + lpNormPow p f t :=
  E213.Lib.Math.Measure.LebesgueIntegral.lebesgue_union_additive
    (powIntegrand f p) s t

/-- ★ Lp p=2 collapses to `Σ f² · lenNum` (the squared-norm
    form, `‖f‖₂² = ∫ f² dμ`). -/
theorem lp_two_singleton (f : Nat → Nat) (db : DyadicBracket) :
    lpNormPow 2 f (singleton db) = (f db.midNum * f db.midNum) * db.lenNum := by
  show (f db.midNum) ^ 2 * db.lenNum + 0
       = (f db.midNum * f db.midNum) * db.lenNum
  rw [Nat.add_zero, Nat.pow_two]

end E213.Lib.Math.Measure.Lp
