import E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip
import E213.Lib.Math.Cohomology.Cup.KSubsetStructural

/-!
# Cohomology.Cup.SubsetIdxRoundtripGeneral

General **∀n** round-trip at `k = 1`:

  `subsetIdx n 1 (kSubset n 1 i) = i`  for `i < n`.

Generalises the decide-verified `roundtrip_5_1` (in `SubsetIdxRoundtrip`)
to arbitrary `n`.

Strategy (PURE — avoids `List.range_succ`'s `propext`):
  1. Reduce `kSubset n 1 i` to `[i]` via `kSubset_n_1_singleton` (§3).
  2. Route `List.range n` through `List.range' 0 n` via the PURE bridge
     `List.range_eq_range'`.
  3. Prove a generic **witness lemma** for `find?` on `range'`: if
     a predicate `p` is `true` at a unique witness `i ∈ [s, s+n)` and
     `false` everywhere strictly below `i` in that range, then
     `(range' s n).find? p = some i`.
  4. Instantiate at `s = 0` with `p = (fun j => kSubset n 1 j == [i])`,
     using `kSubset_n_1_singleton` to verify the predicate-shape.

All theorems below are **PURE** (verified by `tools/scan_axioms.py`).
-/

namespace E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip

open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §5.  `find?` witness lemma on `List.range'` -/

/-- ★★★ **find? witness lemma on `range'`** — if `p i = true`, `p j = false`
    for `s ≤ j < i`, and `s ≤ i < s + n`, then `find? p (range' s n) = some i`.

    PURE.  Induction on `n` using `range' s (n+1) 1 = s :: range' (s+1) n 1`
    (rfl) and `find?` cons-unfolding (rfl via match).  -/
theorem find_range'_witness :
    ∀ (s n : Nat) (p : Nat → Bool) (i : Nat),
      s ≤ i → i < s + n → p i = true →
      (∀ j, s ≤ j → j < i → p j = false) →
      (List.range' s n).find? p = some i := by
  intro s n
  induction n generalizing s with
  | zero =>
    intro p i h_le h_lt _ _
    rw [Nat.add_zero] at h_lt
    exact absurd h_lt (Nat.not_lt_of_le h_le)
  | succ m ih =>
    intro p i h_le h_lt h_pi h_neg
    -- LHS = (s :: range' (s+1) m).find? p = (match p s with | true => some s | false => ...)
    show (s :: List.range' (s + 1) m).find? p = some i
    by_cases h_eq : s = i
    · -- s = i: p s = p i = true, so find? returns some s = some i
      subst h_eq
      show (match p s with
            | true => some s
            | false => (List.range' (s + 1) m).find? p) = some s
      rw [h_pi]
    · -- s < i: p s = false (by h_neg), recurse on range' (s+1) m
      have h_lt_si : s < i := Nat.lt_of_le_of_ne h_le h_eq
      have h_ps : p s = false := h_neg s (Nat.le_refl s) h_lt_si
      show (match p s with
            | true => some s
            | false => (List.range' (s + 1) m).find? p) = some i
      rw [h_ps]
      apply ih (s + 1) p i
      · exact Nat.succ_le_of_lt h_lt_si
      · -- i < s + (m + 1) ⇒ i < (s + 1) + m
        have hrw : s + (m + 1) = (s + 1) + m := by
          rw [Nat.add_assoc, Nat.add_comm m 1, ← Nat.add_assoc]
        rw [hrw] at h_lt
        exact h_lt
      · exact h_pi
      · intro j h_le_j h_lt_j
        exact h_neg j (Nat.le_of_succ_le h_le_j) h_lt_j

/-- ★★ **find? on `List.range n`** — specialised to `s = 0`, then
    routed through `List.range_eq_range'` to `range' 0 n`.  PURE. -/
theorem find_range_witness (n : Nat) (p : Nat → Bool) (i : Nat)
    (h_lt : i < n)
    (h_pi : p i = true)
    (h_neg : ∀ j, j < i → p j = false) :
    (List.range n).find? p = some i := by
  rw [List.range_eq_range']
  apply find_range'_witness 0 n p i
  · exact Nat.zero_le i
  · simpa using h_lt
  · exact h_pi
  · intro j _ h_lt_j
    exact h_neg j h_lt_j

/-! ## §6.  ∀n general round-trip at `k = 1` -/

/-- Auxiliary: `kSubset n 1 j == [i]` evaluates to `j == i` for `j < n`.
    Follows from `kSubset_n_1_singleton`.  PURE. -/
private theorem kSubset_n_1_eq_singleton_iff (n j i : Nat) (h : j < n) :
    (kSubset n 1 j == [i]) = (j == i) := by
  rw [kSubset_n_1_singleton n j h]
  -- LHS: ([j] == [i])
  -- We need to show this equals (j == i).
  -- By List.beq cons-unfolding: [j] == [i] = (j == i) && ([] == []) = (j == i) && true
  show ((j == i) && true) = (j == i)
  cases j == i <;> rfl

/-- Predicate `j == i` is `false` for `j < i`.  Uses `decide_eq_false` +
    `Nat.ne_of_lt`.  Routes through `(j == i) = decide (j = i)`
    (definitional via the `[DecidableEq Nat] → BEq Nat` instance).  PURE. -/
private theorem nat_beq_eq_false_of_lt (j i : Nat) (h : j < i) :
    (j == i) = false := by
  show decide (j = i) = false
  exact decide_eq_false (Nat.ne_of_lt h)

/-- `Nat.beq` self-reflexivity: `i == i = true`.  PURE. -/
private theorem nat_beq_self (i : Nat) : (i == i) = true := by
  show decide (i = i) = true
  exact decide_eq_true rfl

/-- ★★★ **General ∀n round-trip at k = 1** — for any `n` and `i < n`,
    `subsetIdx n 1 (kSubset n 1 i) = i`.  PURE.  -/
theorem roundtrip_n_1 (n i : Nat) (h : i < n) :
    subsetIdx n 1 (kSubset n 1 i) = i := by
  rw [kSubset_n_1_singleton n i h]
  -- Goal: subsetIdx n 1 [i] = i
  show ((List.range (binom n 1)).find?
        (fun j => kSubset n 1 j == [i])).getD (binom n 1) = i
  rw [binom_m_1 n]
  -- Goal: ((List.range n).find? (fun j => kSubset n 1 j == [i])).getD n = i
  -- Apply find_range_witness with witness i, predicate (kSubset n 1 · == [i]).
  have h_find :
      (List.range n).find? (fun j => kSubset n 1 j == [i]) = some i := by
    apply find_range_witness n _ i h
    · -- p i = true: kSubset n 1 i == [i] = true
      rw [kSubset_n_1_eq_singleton_iff n i i h, nat_beq_self]
    · -- ∀ j < i, p j = false
      intro j h_lt_j
      have h_j_lt_n : j < n := Nat.lt_trans h_lt_j h
      rw [kSubset_n_1_eq_singleton_iff n j i h_j_lt_n]
      exact nat_beq_eq_false_of_lt j i h_lt_j
  rw [h_find]
  rfl

/-- Pointwise (Fin-indexed) form on `Fin (binom n 1)`.  PURE.  -/
theorem roundtrip_n_1_fin (n : Nat) :
    ∀ (j : Fin (binom n 1)),
      subsetIdx n 1 (kSubset n 1 j.val) = j.val := by
  intro ⟨v, hv⟩
  -- hv : v < binom n 1 — destructure to avoid Fin-typed motive issue
  have h_lt : v < n := by
    rw [binom_m_1] at hv
    exact hv
  exact roundtrip_n_1 n v h_lt

/-! ## §7.  ∀(n, k) general round-trip — the kSubset bijection capstone -/

open E213.Lib.Math.Cohomology.Cup.KSubsetStructural
  (kSubset_injective)

/-- `List.beq` reflexivity for `List Nat`.  PURE. -/
private theorem list_nat_beq_self (l : List Nat) : (l == l) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show ((x == x) && (xs == xs)) = true
    rw [nat_beq_self]
    show (xs == xs) = true
    exact ih

/-- `List.beq` correctness one direction: `(l₁ == l₂) = true → l₁ = l₂`.  PURE. -/
private theorem list_nat_beq_eq_implies :
    ∀ (l₁ l₂ : List Nat), (l₁ == l₂) = true → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons y ys => exact Bool.noConfusion h
  | cons x xs ih =>
    intro l₂ h
    cases l₂ with
    | nil => exact Bool.noConfusion h
    | cons y ys =>
      have h_and : ((x == y) && (xs == ys)) = true := h
      have h_x_eq_y : (x == y) = true := by
        cases hxy : (x == y) with
        | true => rfl
        | false => rw [hxy] at h_and; exact Bool.noConfusion h_and
      have h_xs_eq_ys : (xs == ys) = true := by
        rw [h_x_eq_y] at h_and
        exact h_and
      have h_xy : x = y := of_decide_eq_true h_x_eq_y
      have h_xs_ys : xs = ys := ih ys h_xs_eq_ys
      rw [h_xy, h_xs_ys]

/-- `j ≠ i → (j == i) = false` for `Nat`.  PURE.  -/
private theorem nat_beq_eq_false_of_ne (j i : Nat) (h : j ≠ i) :
    (j == i) = false := by
  show decide (j = i) = false
  exact decide_eq_false h

/-- Auxiliary: `kSubset n k j == kSubset n k i` evaluates to `j == i`
    for `j < binom n k` and `i < binom n k`.  Routes through
    `kSubset_injective` (PURE in `KSubsetStructural`).  -/
private theorem kSubset_eq_kSubset_iff_idx (n k j i : Nat)
    (h_j : j < binom n k) (h_i : i < binom n k) :
    (kSubset n k j == kSubset n k i) = (j == i) := by
  by_cases h_eq : j = i
  · subst h_eq
    rw [list_nat_beq_self, nat_beq_self]
  · have h_neq_kSubset : kSubset n k j ≠ kSubset n k i := by
      intro h_eq_kSubset
      exact h_eq (kSubset_injective n k j i h_j h_i h_eq_kSubset)
    have h_beq_lhs : (kSubset n k j == kSubset n k i) = false := by
      cases h_beq : (kSubset n k j == kSubset n k i) with
      | true => exact absurd (list_nat_beq_eq_implies _ _ h_beq) h_neq_kSubset
      | false => rfl
    rw [h_beq_lhs, nat_beq_eq_false_of_ne j i h_eq]

/-- ★★★ **General ∀(n, k) round-trip** — for any `n`, `k`, and `j < binom n k`,
    `subsetIdx n k (kSubset n k j) = j`.  PURE.

    This is `kSubset`'s **bijection content** on `Fin (binom n k)`,
    proved via the `find?` witness lemma (§5) + `kSubset_injective`
    (in `KSubsetStructural`).  -/
theorem roundtrip_n_k (n k j : Nat) (h : j < binom n k) :
    subsetIdx n k (kSubset n k j) = j := by
  show ((List.range (binom n k)).find?
        (fun i => kSubset n k i == kSubset n k j)).getD (binom n k) = j
  have h_find :
      (List.range (binom n k)).find?
        (fun i => kSubset n k i == kSubset n k j) = some j := by
    apply find_range_witness (binom n k) _ j h
    · -- p j = true:  kSubset n k j == kSubset n k j = true
      rw [kSubset_eq_kSubset_iff_idx n k j j h h, nat_beq_self]
    · -- ∀ i < j, p i = false
      intro i h_lt_i
      have h_i_lt : i < binom n k := Nat.lt_trans h_lt_i h
      rw [kSubset_eq_kSubset_iff_idx n k i j h_i_lt h]
      exact nat_beq_eq_false_of_lt i j h_lt_i
  rw [h_find]
  rfl

/-- Pointwise (Fin-indexed) form on `Fin (binom n k)`.  PURE. -/
theorem roundtrip_n_k_fin (n k : Nat) :
    ∀ (j : Fin (binom n k)),
      subsetIdx n k (kSubset n k j.val) = j.val := by
  intro ⟨v, hv⟩
  exact roundtrip_n_k n k v hv

end E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip
