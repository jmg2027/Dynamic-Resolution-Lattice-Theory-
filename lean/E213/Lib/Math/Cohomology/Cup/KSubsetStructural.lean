import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Physics.Simplex.Counts
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.ListHelper

/-!
# Cohomology.Cup.KSubsetStructural

Structural properties of `kSubset` foundational for the ∀(n, k)
bijection between `Fin (binom n k)` and k-subsets of `{0..n-1}`:

  · `kSubset_length` — `(kSubset n k j).length = k`.
  · `kSubset_all_lt` — every element `< n`.
  · `kSubset_injective` — `i₁ ≠ i₂ → kSubset n k i₁ ≠ kSubset n k i₂`.

All PURE.  Core tactics: induction on `n` matching kSubset's colex
recursion + `binom`'s Pascal recursion (both `rfl`-direct).

Bypasses `List.length_append`, `Nat.add_sub_cancel`, `Nat.sub_lt_sub_right`
(all propext-tainted in Lean core) with PURE custom helpers.
-/

namespace E213.Lib.Math.Cohomology.Cup.KSubsetStructural

open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §0.  PURE Nat / List helpers (replacing propext-tainted Lean-core lemmas)

Nat helpers (`add_sub_cancel_right`, `sub_lt_sub_right`,
`sub_pos_of_lt`) are sourced from the central
`E213.Tactic.NatHelper` PURE-shield layer (G93 §C1).  We rename
them locally so existing call sites remain unaffected. -/

/-- Local alias for `NatHelper.add_sub_cancel_right`.
    Centralised in `Meta/Tactic/NatHelper.lean` (G93 §C1). -/
@[reducible] def nat_add_sub_cancel : ∀ (a c : Nat), (a + c) - c = a :=
  E213.Tactic.NatHelper.add_sub_cancel_right

/-- Local alias for `NatHelper.sub_lt_sub_right`.
    Centralised in `Meta/Tactic/NatHelper.lean` (G93 §C1). -/
@[reducible] def nat_sub_lt_sub_right :
    ∀ {a b : Nat} (c : Nat), c ≤ a → a < b → a - c < b - c :=
  E213.Tactic.NatHelper.sub_lt_sub_right

/-- Local alias for `ListHelper.length_append_singleton`.
    Centralised in `Meta/Tactic/ListHelper.lean` (G94 §1). -/
@[reducible] def list_length_append_singleton :
    ∀ (l : List Nat) (x : Nat), (l ++ [x]).length = l.length + 1 :=
  E213.Tactic.ListHelper.length_append_singleton

/-- Local alias for `ListHelper.mem_append_singleton`.
    Centralised in `Meta/Tactic/ListHelper.lean` (G94 §1). -/
@[reducible] private def list_mem_append_singleton :
    ∀ (l : List Nat) (m x : Nat), x ∈ l ++ [m] → x ∈ l ∨ x = m :=
  E213.Tactic.ListHelper.mem_append_singleton

/-! ## §1.  Length lemma -/

/-- ★★ **kSubset has length `k`** — for any valid `(n, k, j)` with
    `j < binom n k`, the list `kSubset n k j` has length exactly `k`.  PURE. -/
theorem kSubset_length :
    ∀ (n k j : Nat), j < binom n k → (kSubset n k j).length = k := by
  intro n
  induction n with
  | zero =>
    intro k j h
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ kj =>
        exact absurd h (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ kj)))
    | succ k' =>
      exact absurd h (Nat.not_lt_zero j)
  | succ m ih =>
    intro k j h
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ kj =>
        exact absurd h (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ kj)))
    | succ k' =>
      show (if j < binom m (k' + 1) then kSubset m (k' + 1) j
            else kSubset m k' (j - binom m (k' + 1)) ++ [m]).length = k' + 1
      by_cases h_lt : j < binom m (k' + 1)
      · rw [if_pos h_lt]
        exact ih (k' + 1) j h_lt
      · rw [if_neg h_lt]
        have h_ge : binom m (k' + 1) ≤ j := Nat.le_of_not_lt h_lt
        have h_split : j - binom m (k' + 1) < binom m k' := by
          have h_lt2 : j < binom m k' + binom m (k' + 1) := h
          have h_sub : j - binom m (k' + 1)
              < (binom m k' + binom m (k' + 1)) - binom m (k' + 1) :=
            nat_sub_lt_sub_right (binom m (k' + 1)) h_ge h_lt2
          rwa [nat_add_sub_cancel] at h_sub
        rw [list_length_append_singleton]
        rw [ih k' (j - binom m (k' + 1)) h_split]

/-! ## §2.  Element bound lemma -/

/-- ★★ **kSubset elements all `< n`** — every element of `kSubset n k j`
    is strictly less than `n`, for valid `j < binom n k`.  PURE.  -/
theorem kSubset_all_lt :
    ∀ (n k j : Nat), j < binom n k → ∀ x ∈ kSubset n k j, x < n := by
  intro n
  induction n with
  | zero =>
    intro k j h
    cases k with
    | zero =>
      cases j with
      | zero => intro x hmem; exact absurd hmem (List.not_mem_nil x)
      | succ kj =>
        exact absurd h (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ kj)))
    | succ k' =>
      exact absurd h (Nat.not_lt_zero j)
  | succ m ih =>
    intro k j h
    cases k with
    | zero =>
      cases j with
      | zero => intro x hmem; exact absurd hmem (List.not_mem_nil x)
      | succ kj =>
        exact absurd h (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ kj)))
    | succ k' =>
      intro x hmem
      show x < m + 1
      -- Unfold kSubset (m+1) (k'+1) j
      change x ∈ (if j < binom m (k' + 1) then kSubset m (k' + 1) j
            else kSubset m k' (j - binom m (k' + 1)) ++ [m]) at hmem
      by_cases h_lt : j < binom m (k' + 1)
      · rw [if_pos h_lt] at hmem
        have h_x_lt_m : x < m := ih (k' + 1) j h_lt x hmem
        exact Nat.lt_succ_of_lt h_x_lt_m
      · rw [if_neg h_lt] at hmem
        have h_ge : binom m (k' + 1) ≤ j := Nat.le_of_not_lt h_lt
        have h_split : j - binom m (k' + 1) < binom m k' := by
          have h_lt2 : j < binom m k' + binom m (k' + 1) := h
          have h_sub : j - binom m (k' + 1)
              < (binom m k' + binom m (k' + 1)) - binom m (k' + 1) :=
            nat_sub_lt_sub_right (binom m (k' + 1)) h_ge h_lt2
          rwa [nat_add_sub_cancel] at h_sub
        -- hmem : x ∈ kSubset m k' (j - split) ++ [m]
        -- Either x ∈ kSubset m k' (...) (so x < m) or x = m (so x < m+1)
        rcases list_mem_append_singleton _ m x hmem with h_in | h_x_eq
        · have h_x_lt_m : x < m := ih k' _ h_split x h_in
          exact Nat.lt_succ_of_lt h_x_lt_m
        · rw [h_x_eq]
          exact Nat.lt_succ_self _

/-! ## §3.  More PURE helpers for injectivity -/

/-- Local alias for `NatHelper.sub_pos_of_lt` with the b/a arg
    order convention used by downstream callers.  Centralised in
    `Meta/Tactic/NatHelper.lean` (G93 §C1). -/
@[reducible] def nat_sub_pos_of_lt :
    ∀ {a b : Nat}, b < a → 0 < a - b :=
  fun h => E213.Tactic.NatHelper.sub_pos_of_lt h

/-- `c ≤ a → c ≤ b → a - c = b - c → a = b` — PURE right-cancellation. -/
private theorem nat_sub_inj_right :
    ∀ {a b c : Nat}, c ≤ a → c ≤ b → a - c = b - c → a = b := by
  intro a b c
  induction c generalizing a b with
  | zero => intro _ _ h; rwa [Nat.sub_zero, Nat.sub_zero] at h
  | succ k ih =>
    intro h_le_a h_le_b h_eq
    cases a with
    | zero => exact absurd h_le_a (Nat.not_succ_le_zero k)
    | succ a' =>
      cases b with
      | zero => exact absurd h_le_b (Nat.not_succ_le_zero k)
      | succ b' =>
        have h_k_le_a' : k ≤ a' := Nat.le_of_succ_le_succ h_le_a
        have h_k_le_b' : k ≤ b' := Nat.le_of_succ_le_succ h_le_b
        have h_eq' : a' - k = b' - k := by
          rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub] at h_eq
          exact h_eq
        rw [ih h_k_le_a' h_k_le_b' h_eq']

/-- Local alias for `ListHelper.append_singleton_inj`.
    Centralised in `Meta/Tactic/ListHelper.lean` (G94 §1). -/
@[reducible] private def list_append_singleton_inj :
    ∀ (l₁ l₂ : List Nat) (x : Nat), l₁ ++ [x] = l₂ ++ [x] → l₁ = l₂ :=
  E213.Tactic.ListHelper.append_singleton_inj

/-- Local alias for `ListHelper.mem_append_singleton_right`.
    Centralised in `Meta/Tactic/ListHelper.lean` (G94 §1). -/
@[reducible] private def mem_append_singleton_right :
    ∀ (l : List Nat) (m : Nat), m ∈ l ++ [m] :=
  E213.Tactic.ListHelper.mem_append_singleton_right

/-! ## §4.  kSubset injectivity (∀ n k) -/

/-- ★★★ **kSubset is injective on `[0, binom n k)`** — if `i₁ < binom n k`,
    `i₂ < binom n k`, and `kSubset n k i₁ = kSubset n k i₂`, then `i₁ = i₂`.

    Substantial structural proof.  Inducts on `n`, case-splits on `k = 0` /
    `k = k'+1`, and within the latter splits both indices against the colex
    pivot `binom m (k'+1)`.  The cross-branch case (one index < pivot, one
    ≥ pivot) is impossible by `kSubset_all_lt` (would force `m ∈` a list of
    elements `< m`).  PURE. -/
theorem kSubset_injective :
    ∀ (n k i₁ i₂ : Nat), i₁ < binom n k → i₂ < binom n k →
      kSubset n k i₁ = kSubset n k i₂ → i₁ = i₂ := by
  intro n
  induction n with
  | zero =>
    intro k i₁ i₂ h₁ h₂ _
    cases k with
    | zero =>
      -- binom 0 0 = 1, both indices = 0
      cases i₁ with
      | zero =>
        cases i₂ with
        | zero => rfl
        | succ k₂ =>
          exact absurd h₂ (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ k₂)))
      | succ k₁ =>
        exact absurd h₁ (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ k₁)))
    | succ k' =>
      exact absurd h₁ (Nat.not_lt_zero i₁)
  | succ m ih =>
    intro k i₁ i₂ h₁ h₂ h_eq
    cases k with
    | zero =>
      cases i₁ with
      | zero =>
        cases i₂ with
        | zero => rfl
        | succ k₂ =>
          exact absurd h₂ (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ k₂)))
      | succ k₁ =>
        exact absurd h₁ (Nat.not_lt_of_le (Nat.succ_le_of_lt (Nat.zero_lt_succ k₁)))
    | succ k' =>
      -- Main case: split = binom m (k'+1)
      -- Unfold both sides via kSubset's defining if-then-else
      change (if i₁ < binom m (k' + 1) then kSubset m (k' + 1) i₁
              else kSubset m k' (i₁ - binom m (k' + 1)) ++ [m])
           = (if i₂ < binom m (k' + 1) then kSubset m (k' + 1) i₂
              else kSubset m k' (i₂ - binom m (k' + 1)) ++ [m])
        at h_eq
      by_cases h₁_lt : i₁ < binom m (k' + 1)
      · by_cases h₂_lt : i₂ < binom m (k' + 1)
        · rw [if_pos h₁_lt, if_pos h₂_lt] at h_eq
          exact ih (k' + 1) i₁ i₂ h₁_lt h₂_lt h_eq
        · rw [if_pos h₁_lt, if_neg h₂_lt] at h_eq
          have h_m_in_rhs : m ∈ kSubset m k' (i₂ - binom m (k' + 1)) ++ [m] :=
            mem_append_singleton_right _ m
          have h_m_in_lhs : m ∈ kSubset m (k' + 1) i₁ := h_eq ▸ h_m_in_rhs
          have h_m_lt_m : m < m := kSubset_all_lt m (k' + 1) i₁ h₁_lt m h_m_in_lhs
          exact absurd h_m_lt_m (Nat.lt_irrefl m)
      · by_cases h₂_lt : i₂ < binom m (k' + 1)
        · rw [if_neg h₁_lt, if_pos h₂_lt] at h_eq
          have h_m_in_lhs : m ∈ kSubset m k' (i₁ - binom m (k' + 1)) ++ [m] :=
            mem_append_singleton_right _ m
          have h_m_in_rhs : m ∈ kSubset m (k' + 1) i₂ := h_eq ▸ h_m_in_lhs
          have h_m_lt_m : m < m := kSubset_all_lt m (k' + 1) i₂ h₂_lt m h_m_in_rhs
          exact absurd h_m_lt_m (Nat.lt_irrefl m)
        · rw [if_neg h₁_lt, if_neg h₂_lt] at h_eq
          have h₁_ge : binom m (k' + 1) ≤ i₁ := Nat.le_of_not_lt h₁_lt
          have h₂_ge : binom m (k' + 1) ≤ i₂ := Nat.le_of_not_lt h₂_lt
          have h_split₁ : i₁ - binom m (k' + 1) < binom m k' := by
            have h_lt2 : i₁ < binom m k' + binom m (k' + 1) := h₁
            have h_sub : i₁ - binom m (k' + 1)
                < (binom m k' + binom m (k' + 1)) - binom m (k' + 1) :=
              nat_sub_lt_sub_right (binom m (k' + 1)) h₁_ge h_lt2
            rwa [nat_add_sub_cancel] at h_sub
          have h_split₂ : i₂ - binom m (k' + 1) < binom m k' := by
            have h_lt2 : i₂ < binom m k' + binom m (k' + 1) := h₂
            have h_sub : i₂ - binom m (k' + 1)
                < (binom m k' + binom m (k' + 1)) - binom m (k' + 1) :=
              nat_sub_lt_sub_right (binom m (k' + 1)) h₂_ge h_lt2
            rwa [nat_add_sub_cancel] at h_sub
          have h_inner_eq : kSubset m k' (i₁ - binom m (k' + 1))
                          = kSubset m k' (i₂ - binom m (k' + 1)) :=
            list_append_singleton_inj _ _ m h_eq
          have h_sub_eq : i₁ - binom m (k' + 1) = i₂ - binom m (k' + 1) :=
            ih k' _ _ h_split₁ h_split₂ h_inner_eq
          exact nat_sub_inj_right h₁_ge h₂_ge h_sub_eq

end E213.Lib.Math.Cohomology.Cup.KSubsetStructural
