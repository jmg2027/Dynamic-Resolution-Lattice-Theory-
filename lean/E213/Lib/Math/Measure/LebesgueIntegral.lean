import E213.Lib.Math.Measure.MeasurableSet
import E213.Lib.Math.Measure.DyadicMeasure

/-!
# Measure Theory 213 — Lebesgue-style integral

213-native paradigm: a "Lebesgue integral over a measurable set" is
a finite sum over the bracket cover.  Each bracket contributes
`f-value × bracket-length` (numerator).  No σ-algebra, no Choice,
no monotone-class theorem chase.

Atomic content:
  * `lebesgueStepNum` — sum of `f(midNum) × bracketLen` over a list
  * Constant function: `∫ c dμ = c · μ(S)`
  * Empty set: `∫ f d∅ = 0` (rfl)
  * Linearity over union: `∫ f d(S∪T) = ∫ f dS + ∫ f dT`

213-native: integral *is* a finite sum.
-/

namespace E213.Lib.Math.Measure.LebesgueIntegral

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
  (DyadicBracket DyadicBracket.lenNum DyadicBracket.midNum)
open E213.Lib.Math.Measure.MeasurableSet
  (DyadicMeasurableSet emptySet singleton union)
open E213.Lib.Math.Measure.DyadicMeasure
  (bracketMeasureNum measureNum measureNum_append)

/-- Step-function Lebesgue integral: per-bracket contribution
    `f(midNum) × lenNum`. -/
def lebesgueStepNum (f : Nat → Nat) : List DyadicBracket → Nat
  | [] => 0
  | db :: rest =>
      f db.midNum * db.lenNum + lebesgueStepNum f rest

/-- Constant integrand `f := fun _ => c`. -/
def constIntegrand (c : Nat) : Nat → Nat := fun _ => c

/-- ★ Empty integral = 0 (rfl). -/
theorem lebesgue_empty (f : Nat → Nat) :
    lebesgueStepNum f emptySet = 0 := rfl

/-- ★ Singleton integral = f(midNum) × bracketLen. -/
theorem lebesgue_singleton (f : Nat → Nat) (db : DyadicBracket) :
    lebesgueStepNum f (singleton db) = f db.midNum * db.lenNum := by
  show f db.midNum * db.lenNum + 0 = f db.midNum * db.lenNum
  exact Nat.add_zero _

/-- Helper: additivity over `++`. -/
theorem lebesgueStepNum_append (f : Nat → Nat) :
    ∀ (s t : List DyadicBracket),
      lebesgueStepNum f (s ++ t)
        = lebesgueStepNum f s + lebesgueStepNum f t
  | [], t => by
      show lebesgueStepNum f t = 0 + lebesgueStepNum f t
      exact (Nat.zero_add _).symm
  | a :: s, t => by
      show f a.midNum * a.lenNum + lebesgueStepNum f (s ++ t)
        = (f a.midNum * a.lenNum + lebesgueStepNum f s)
          + lebesgueStepNum f t
      rw [lebesgueStepNum_append f s t]
      exact (Nat.add_assoc _ _ _).symm

/-- ★ Linearity over union. -/
theorem lebesgue_union_additive (f : Nat → Nat)
    (s t : DyadicMeasurableSet) :
    lebesgueStepNum f (union s t)
      = lebesgueStepNum f s + lebesgueStepNum f t :=
  lebesgueStepNum_append f s t

/-- Helper: constant integrand on a list = c · measureNum. -/
theorem lebesgue_const_eq_measure :
    ∀ (c : Nat) (s : List DyadicBracket),
      lebesgueStepNum (constIntegrand c) s = c * measureNum s
  | _, [] => rfl
  | c, db :: rest => by
      show c * db.lenNum + lebesgueStepNum (constIntegrand c) rest
        = c * (db.lenNum + measureNum rest)
      rw [lebesgue_const_eq_measure c rest]
      exact (Nat.mul_add c db.lenNum (measureNum rest)).symm

/-- ★ Constant integrand: `∫ c dμ = c · μ(S)`. -/
theorem lebesgue_const (c : Nat) (s : DyadicMeasurableSet) :
    lebesgueStepNum (constIntegrand c) s = c * measureNum s :=
  lebesgue_const_eq_measure c s

/-- ★ `∫ 1 dμ = lenNum` for a singleton. -/
theorem lebesgue_one_singleton (db : DyadicBracket) :
    lebesgueStepNum (constIntegrand 1) (singleton db) = db.lenNum := by
  rw [lebesgue_const 1 (singleton db)]
  show 1 * (db.lenNum + 0) = db.lenNum
  rw [Nat.add_zero]
  exact Nat.one_mul _

end E213.Lib.Math.Measure.LebesgueIntegral
