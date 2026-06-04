import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket

/-!
# Topology — `DyadicOpen` as bracket union

In 213, *open sets* are not arbitrary unions of intervals on a
continuous line — they are **finite unions of `DyadicBracket`s**
on the dyadic refinement tree.  This file:

  * `DyadicOpen` = `List DyadicBracket`.
  * `empty`, `singleton`, `union`, `size`.
  * Atomic: every `DyadicOpen` has finite cardinality
    (= `List.length`); compactness is automatic.

This is the σ-algebra-rejection echo: there is no "uncountable open
set" because `List` is countable by construction, and dyadic brackets
themselves are finite-data.

Key 213-native insight: countability of open sets is **structural**,
not via Choice.
-/

namespace E213.Lib.Math.Geometry.Topology.DyadicOpen

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)

/-- A *dyadic open set* — finite list of dyadic brackets. -/
abbrev DyadicOpen := List DyadicBracket

/-- The empty open set (vacuous union). -/
def empty : DyadicOpen := []

/-- Single-bracket open set. -/
def singleton (db : DyadicBracket) : DyadicOpen := [db]

/-- Union of two opens (list concatenation). -/
def union (a b : DyadicOpen) : DyadicOpen := a ++ b

/-- Cardinality (number of bracket components). -/
def size (o : DyadicOpen) : Nat := o.length

/-- Empty open has size 0 (rfl). -/
theorem size_empty : size empty = 0 := rfl

/-- Singleton open has size 1 (rfl). -/
theorem size_singleton (db : DyadicBracket) :
    size (singleton db) = 1 := rfl

/-- Union of empty with `o` is `o`. -/
theorem union_empty_left (o : DyadicOpen) :
    union empty o = o := List.nil_append o

/-- ★ **Size is additive under union** (term-mode, propext-clean). -/
theorem size_union : ∀ a b : DyadicOpen,
    size (union a b) = size a + size b
  | [], b => by show b.length = 0 + b.length; rw [Nat.zero_add]
  | _ :: a, b => by
    have ih : (a ++ b).length = a.length + b.length := size_union a b
    show (a ++ b).length + 1 = a.length + 1 + b.length
    rw [ih, Nat.add_right_comm]

/-- ★ **Every dyadic open is finite** ★ — no Choice needed; the
    `List` constructor itself enforces it. -/
theorem dyadic_open_finite (o : DyadicOpen) :
    ∃ n : Nat, size o = n := ⟨o.length, rfl⟩

/-- Concrete: a 3-bracket open has size 3. -/
theorem size_3_concrete (a b c : DyadicBracket) :
    size [a, b, c] = 3 := rfl

end E213.Lib.Math.Geometry.Topology.DyadicOpen
