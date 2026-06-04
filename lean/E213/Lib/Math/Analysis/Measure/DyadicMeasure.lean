import E213.Lib.Math.Analysis.Measure.MeasurableSet

/-!
# Measure Theory 213 — Dyadic measure (cohomological)

Measure on `DyadicMeasurableSet` = sum of bracket lengths over a
common denominator `2^E`.  No σ-algebra; no Choice.  This is the
*ZFC-rejected* alternative paradigm: measure is finite by
construction.

## Atomic content

  * `bracketMeasureNum / bracketMeasureDen` — `Nat × Nat` ratio
  * `measureNum` on a list — sum of numerators
  * `measure_empty = 0` (rfl)
  * `measure_singleton db = db.lenNum` (rfl)
  * `measure_union_additive` — additivity (term-mode induction)

## 213-native paradigm

A *measure* is a `Nat`-valued sum.  Probability is the case
denominator = `2^E`.
-/

namespace E213.Lib.Math.Analysis.Measure.DyadicMeasure

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
  (DyadicBracket DyadicBracket.lenNum)
open E213.Lib.Math.Analysis.Measure.MeasurableSet
  (DyadicMeasurableSet emptySet singleton union)

/-- Numerator of the measure of a single bracket. -/
def bracketMeasureNum (db : DyadicBracket) : Nat := db.lenNum

/-- Denominator (the bracket's denom is `2^E`; we record `E`). -/
def bracketMeasureExp (db : DyadicBracket) : Nat := db.expE

/-- Numerator of the measure of a list, all reduced to the *first*
    bracket's exponent (atomic case: equal-`E` brackets).  For the
    general case, see `measureNumAt`. -/
def measureNum : List DyadicBracket → Nat
  | [] => 0
  | db :: rest => bracketMeasureNum db + measureNum rest

/-- ★ Empty measure = 0 (rfl). -/
theorem measure_empty : measureNum emptySet = 0 := rfl

/-- ★ Singleton measure = bracket length (rfl). -/
theorem measure_singleton (db : DyadicBracket) :
    measureNum (singleton db) = bracketMeasureNum db := by
  show bracketMeasureNum db + 0 = bracketMeasureNum db
  exact Nat.add_zero _

/-- Helper — additivity over `++` (no `union` wrapper). -/
theorem measureNum_append : ∀ (s t : List DyadicBracket),
    measureNum (s ++ t) = measureNum s + measureNum t
  | [], t => by
      show measureNum t = 0 + measureNum t
      exact (Nat.zero_add _).symm
  | a :: s, t => by
      show bracketMeasureNum a + measureNum (s ++ t)
        = (bracketMeasureNum a + measureNum s) + measureNum t
      rw [measureNum_append s t]
      exact (Nat.add_assoc _ _ _).symm

/-- ★ Additivity over union.  This is the 213-native version of
    "countable additivity"; `List` is finite, so the result is
    unconditional — no σ-algebra needed. -/
theorem measure_union_additive (s t : DyadicMeasurableSet) :
    measureNum (union s t) = measureNum s + measureNum t :=
  measureNum_append s t

/-- ★ Measure of a 2-bracket cover (closed-form). -/
theorem measure_pair (db1 db2 : DyadicBracket) :
    measureNum [db1, db2] = bracketMeasureNum db1 + bracketMeasureNum db2 := by
  show bracketMeasureNum db1 + (bracketMeasureNum db2 + 0)
    = bracketMeasureNum db1 + bracketMeasureNum db2
  exact congrArg (bracketMeasureNum db1 + ·) (Nat.add_zero _)

end E213.Lib.Math.Analysis.Measure.DyadicMeasure
