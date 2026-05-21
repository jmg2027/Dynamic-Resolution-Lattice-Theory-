import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Physics.Simplex.Counts

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

/-! ## §0.  PURE Nat / List helpers (replacing propext-tainted Lean-core lemmas) -/

/-- `(a + c) - c = a` — PURE via `Nat.succ_sub_succ_eq_sub`. -/
private theorem nat_add_sub_cancel (a c : Nat) : (a + c) - c = a := by
  induction c with
  | zero => rfl
  | succ k ih =>
    show (a + (k + 1)) - (k + 1) = a
    rw [Nat.add_succ, Nat.succ_sub_succ_eq_sub]
    exact ih

/-- `c ≤ a → a < b → a - c < b - c` — PURE via `Nat.pred_lt_pred`. -/
private theorem nat_sub_lt_sub_right :
    ∀ {a b : Nat} (c : Nat), c ≤ a → a < b → a - c < b - c := by
  intro a b c
  induction c with
  | zero => intro _ h; exact h
  | succ k ih =>
    intro h_ge h_lt
    have h_k_le_a : k ≤ a := Nat.le_of_succ_le h_ge
    have h_sub_ih : a - k < b - k := ih h_k_le_a h_lt
    rw [Nat.sub_succ, Nat.sub_succ]
    apply Nat.pred_lt_pred _ h_sub_ih
    intro h_eq
    have h_a_le_k : a ≤ k := Nat.le_of_sub_eq_zero h_eq
    have h_eq_a : a = k := Nat.le_antisymm h_a_le_k h_k_le_a
    rw [h_eq_a] at h_ge
    exact Nat.not_succ_le_self k h_ge

/-- `(l ++ [x]).length = l.length + 1` — PURE via direct induction.
    Specialised to `Nat` (the only use site below). -/
private theorem list_length_append_singleton (l : List Nat) (x : Nat) :
    (l ++ [x]).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    show (ys ++ [x]).length + 1 = ys.length + 1 + 1
    rw [ih]

/-- `x ∈ l ++ [m] → x ∈ l ∨ x = m` — PURE via inductive `List.Mem`
    case-analysis (bypasses `List.mem_append`/`mem_singleton` propext-iff). -/
private theorem list_mem_append_singleton :
    ∀ (l : List Nat) (m x : Nat), x ∈ l ++ [m] → x ∈ l ∨ x = m := by
  intro l m x
  induction l with
  | nil =>
    intro h
    -- h : x ∈ [] ++ [m] = [m]
    cases h with
    | head _ => exact Or.inr rfl
    | tail _ h' => exact absurd h' (List.not_mem_nil x)
  | cons y ys ih =>
    intro h
    -- h : x ∈ y :: (ys ++ [m])
    cases h with
    | head _ => exact Or.inl (List.Mem.head ys)
    | tail _ h' =>
      rcases ih h' with h_in | h_eq
      · exact Or.inl (List.Mem.tail y h_in)
      · exact Or.inr h_eq

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

/-- `b < a → 0 < a - b` — PURE via `Nat.succ_sub_succ_eq_sub`. -/
private theorem nat_sub_pos_of_lt :
    ∀ {a b : Nat}, b < a → 0 < a - b := by
  intro a b
  induction b generalizing a with
  | zero => intro h; rwa [Nat.sub_zero]
  | succ k ih =>
    intro h_lt
    cases a with
    | zero => exact absurd h_lt (Nat.not_lt_zero _)
    | succ a' =>
      show 0 < a' + 1 - (k + 1)
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih (Nat.lt_of_succ_lt_succ h_lt)

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

/-- `l₁ ++ [x] = l₂ ++ [x] → l₁ = l₂` — PURE via cons-injection + length.
    Uses `Nat.noConfusion` (PURE) instead of `Nat.succ_ne_zero` (propext). -/
private theorem list_append_singleton_inj :
    ∀ (l₁ l₂ : List Nat) (x : Nat), l₁ ++ [x] = l₂ ++ [x] → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ x h
    cases l₂ with
    | nil => rfl
    | cons y ys =>
      injection h with _ h_tail
      have h_len : ([] : List Nat).length = (ys ++ [x]).length :=
        congrArg List.length h_tail
      rw [list_length_append_singleton] at h_len
      exact Nat.noConfusion h_len
  | cons a as ih =>
    intro l₂ x h
    cases l₂ with
    | nil =>
      injection h with _ h_tail
      have h_len : (as ++ [x]).length = ([] : List Nat).length :=
        congrArg List.length h_tail
      rw [list_length_append_singleton] at h_len
      exact Nat.noConfusion h_len
    | cons b bs =>
      injection h with h_head h_tail
      rw [h_head, ih bs x h_tail]

/-- `m ∈ l ++ [m]` — PURE constructive proof via `List.Mem`. -/
private theorem mem_append_singleton_right :
    ∀ (l : List Nat) (m : Nat), m ∈ l ++ [m] := by
  intro l m
  induction l with
  | nil => exact List.Mem.head []
  | cons y ys ih => exact List.Mem.tail y ih

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
