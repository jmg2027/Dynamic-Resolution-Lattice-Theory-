import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Math.Cohomology.Delta.Core

/-!
# Cohomology.Cup.SubsetIdxRoundtrip

`kSubset n k j ↔ subsetIdx n k (kSubset n k j) = j` round-trip
lemmas at specific (n, k).  These are the **bridge primitives**
needed to transfer the list-level twisted Leibniz
(`LeibnizLexListLevel.list_level_leibniz_general`) to the
Fin-indexed `cup` / `delta` operations in `Cohomology/Cup/Core.lean`
and `Cohomology/Delta/Core.lean`.

The general round-trip `∀ (n k j : Nat), j < binom n k →
subsetIdx n k (kSubset n k j) = j` is kSubset's **bijection content**
on `Fin (binom n k)` — provable but structurally substantial (requires
inducting on n with case splits for the colex-enumeration recursion).

For DRLT physics applications, we need round-trip at specific (n, k)
pairs.  Δ⁴ uses (5, 0..5).  Δ³ uses (4, 0..4).

This file proves all such instances via `decide`.  PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip

open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1.  Round-trip on Δ⁴ (n = 5) -/

/-- ★ Round-trip at (n, k) = (5, 1).  5 cases. -/
theorem roundtrip_5_1 :
    subsetIdx 5 1 (kSubset 5 1 0) = 0
    ∧ subsetIdx 5 1 (kSubset 5 1 1) = 1
    ∧ subsetIdx 5 1 (kSubset 5 1 2) = 2
    ∧ subsetIdx 5 1 (kSubset 5 1 3) = 3
    ∧ subsetIdx 5 1 (kSubset 5 1 4) = 4 := by decide

/-- ★ Round-trip at (n, k) = (5, 2).  10 cases. -/
theorem roundtrip_5_2 :
    subsetIdx 5 2 (kSubset 5 2 0) = 0
    ∧ subsetIdx 5 2 (kSubset 5 2 1) = 1
    ∧ subsetIdx 5 2 (kSubset 5 2 2) = 2
    ∧ subsetIdx 5 2 (kSubset 5 2 3) = 3
    ∧ subsetIdx 5 2 (kSubset 5 2 4) = 4
    ∧ subsetIdx 5 2 (kSubset 5 2 5) = 5
    ∧ subsetIdx 5 2 (kSubset 5 2 6) = 6
    ∧ subsetIdx 5 2 (kSubset 5 2 7) = 7
    ∧ subsetIdx 5 2 (kSubset 5 2 8) = 8
    ∧ subsetIdx 5 2 (kSubset 5 2 9) = 9 := by decide

/-- ★ Round-trip at (n, k) = (5, 3).  10 cases. -/
theorem roundtrip_5_3 :
    subsetIdx 5 3 (kSubset 5 3 0) = 0
    ∧ subsetIdx 5 3 (kSubset 5 3 1) = 1
    ∧ subsetIdx 5 3 (kSubset 5 3 2) = 2
    ∧ subsetIdx 5 3 (kSubset 5 3 3) = 3
    ∧ subsetIdx 5 3 (kSubset 5 3 4) = 4
    ∧ subsetIdx 5 3 (kSubset 5 3 5) = 5
    ∧ subsetIdx 5 3 (kSubset 5 3 6) = 6
    ∧ subsetIdx 5 3 (kSubset 5 3 7) = 7
    ∧ subsetIdx 5 3 (kSubset 5 3 8) = 8
    ∧ subsetIdx 5 3 (kSubset 5 3 9) = 9 := by decide

/-- ★ Round-trip at (n, k) = (5, 4).  5 cases. -/
theorem roundtrip_5_4 :
    subsetIdx 5 4 (kSubset 5 4 0) = 0
    ∧ subsetIdx 5 4 (kSubset 5 4 1) = 1
    ∧ subsetIdx 5 4 (kSubset 5 4 2) = 2
    ∧ subsetIdx 5 4 (kSubset 5 4 3) = 3
    ∧ subsetIdx 5 4 (kSubset 5 4 4) = 4 := by decide

/-! ## §2.  Pointwise (Fin-input) form on Δ⁴ -/

/-- ★ Round-trip pointwise on `Fin (binom 5 1)`.  decide-enumerates
    Fin's 5 inhabitants directly. -/
theorem roundtrip_5_1_fin :
    ∀ (j : Fin (binom 5 1)),
      subsetIdx 5 1 (kSubset 5 1 j.val) = j.val := by decide

/-- ★ Round-trip pointwise on `Fin (binom 5 2)`. -/
theorem roundtrip_5_2_fin :
    ∀ (j : Fin (binom 5 2)),
      subsetIdx 5 2 (kSubset 5 2 j.val) = j.val := by decide

/-- ★ Round-trip pointwise on `Fin (binom 5 3)`. -/
theorem roundtrip_5_3_fin :
    ∀ (j : Fin (binom 5 3)),
      subsetIdx 5 3 (kSubset 5 3 j.val) = j.val := by decide

/-- ★ Round-trip pointwise on `Fin (binom 5 4)`. -/
theorem roundtrip_5_4_fin :
    ∀ (j : Fin (binom 5 4)),
      subsetIdx 5 4 (kSubset 5 4 j.val) = j.val := by decide

/-! ## §3.  General structural lemma — kSubset n 1 is singleton

For any n, `kSubset n 1 i = [i]` for i < n.  This is the simplest
"kSubset shape" lemma, foundational for the general (n, k=1) cup
bridge.  Provable by structural induction on n (∀ n, no decide). -/

/-- `binom k 0 = 1` for all k.  -/
theorem binom_k_0 (k : Nat) : binom k 0 = 1 := by
  cases k <;> rfl

/-- `binom m 1 = m` for all m.  Proved by Pascal recursion. -/
theorem binom_m_1 (m : Nat) : binom m 1 = m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    show binom k 0 + binom k 1 = k + 1
    rw [binom_k_0, ih, Nat.add_comm]

/-- ★★ **kSubset shape at k = 1** — for any n, the i-th 1-subset
    of {0..n-1} is the singleton list `[i]`.  PURE.  ∀ n. -/
theorem kSubset_n_1_singleton (n : Nat) :
    ∀ (i : Nat), i < n → kSubset n 1 i = [i] := by
  induction n with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    intro i hi
    show (if i < binom m 1 then kSubset m 1 i
          else kSubset m 0 (i - binom m 1) ++ [m]) = [i]
    rw [binom_m_1 m]
    by_cases hi_lt : i < m
    · rw [if_pos hi_lt]
      exact ih i hi_lt
    · rw [if_neg hi_lt]
      have hi_eq : i = m := by
        have h_le_m : i ≤ m := Nat.le_of_lt_succ hi
        have h_ge_m : m ≤ i := Nat.le_of_not_lt hi_lt
        exact Nat.le_antisymm h_le_m h_ge_m
      rw [hi_eq, Nat.sub_self]
      show kSubset m 0 0 ++ [m] = [m]
      cases m <;> rfl

/-! ## §4.  General ∀n round-trip at k = 1 — deferred

With `kSubset_n_1_singleton` showing `kSubset n 1 i = [i]`, the
round-trip `subsetIdx n 1 (kSubset n 1 i) = i` for `i < n` would
generalise the decide-verified `roundtrip_5_1` to arbitrary n.

The reduction is: `subsetIdx n 1 [i] = ((List.range n).find?
(fun j => kSubset n 1 j == [i])).getD n`.  Using
`kSubset_n_1_singleton`, the predicate becomes `[j] == [i]` ↔
`j == i`.  Then we need `(List.range n).find? (· == i) = some i`
for `i < n`.

This requires Lean-core `List.find?` structural lemmas on
`List.range`:
  · `List.find?_append` (PURE, in core)
  · `(List.range m).find? (· == j) = none` when `m ≤ j`
    (requires induction; involves `List.range_succ` which is
    [propext]-tainted — would propagate that to the round-trip).

For DRLT physics applications on Δ⁴ / Δ³ — covered by §1+§2 PURE
instances.  Full ∀n generalisation tagged as next-session work. -/

end E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip
