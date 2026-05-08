import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket

/-!
# Measure Theory 213 — Measurable sets (dyadic, Choice-free)

213-native rejection of σ-algebra: a *measurable set* is a finite
list of `DyadicBracket`s.  No countable-union closure — `List` is
already finite, no Choice.  Vitali / Banach-Tarski cannot arise.

## 213-native paradigm

  * `DyadicMeasurableSet := List DyadicBracket`
  * Union = `List.append`, empty set = `[]`
  * Measure = sum of bracket lengths over common denom

Everything in `Nat`; no `propext`, no Choice.
-/

namespace E213.Lib.Math.Measure.MeasurableSet

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
  (DyadicBracket DyadicBracket.lenNum)

/-- **DyadicMeasurableSet** — finite list of dyadic brackets.
    Replaces ZFC σ-algebra. -/
abbrev DyadicMeasurableSet := List DyadicBracket

/-- The empty measurable set. -/
def emptySet : DyadicMeasurableSet := []

/-- Singleton from a bracket. -/
def singleton (db : DyadicBracket) : DyadicMeasurableSet := [db]

/-- Union = list append (disjointness not required at this layer;
    the *measure* layer accounts for overlap). -/
def union (s t : DyadicMeasurableSet) : DyadicMeasurableSet := s ++ t

/-- ★ `union emptySet s = s` (rfl). -/
theorem union_empty_left (s : DyadicMeasurableSet) :
    union emptySet s = s := rfl

/-- ★ `singleton db ++ [] = [db]` (rfl). -/
theorem singleton_unfold (db : DyadicBracket) :
    singleton db = [db] := rfl

/-- Cardinality of the measurable cover (number of brackets). -/
def cardinality (s : DyadicMeasurableSet) : Nat := s.length

/-- ★ Empty has cardinality 0. -/
theorem cardinality_empty : cardinality emptySet = 0 := rfl

/-- ★ Singleton has cardinality 1. -/
theorem cardinality_singleton (db : DyadicBracket) :
    cardinality (singleton db) = 1 := rfl

/-- Term-mode `List.length_append` — propext-free induction on `s`. -/
theorem length_append_term : ∀ (s t : List DyadicBracket),
    (s ++ t).length = s.length + t.length
  | [], t => by
      show t.length = 0 + t.length
      exact (Nat.zero_add t.length).symm
  | a :: s, t => by
      show (a :: (s ++ t)).length = (a :: s).length + t.length
      show (s ++ t).length + 1 = (s.length + 1) + t.length
      rw [length_append_term s t]
      exact (Nat.succ_add s.length t.length).symm

/-- ★ Union cardinality = sum (term-mode). -/
theorem cardinality_union (s t : DyadicMeasurableSet) :
    cardinality (union s t) = s.length + t.length :=
  length_append_term s t

end E213.Lib.Math.Measure.MeasurableSet
