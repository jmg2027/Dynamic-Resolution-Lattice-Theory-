import E213.Lib.Math.Cohomology.Cup.Core
import E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtripGeneral
import E213.Meta.Tactic.ListHelper

/-!
# Cohomology.Cup.FinBridgeGeneral

**Automatic** List-level → Fin-indexed bridge for the lex-projection
`cup` operation, **∀(n, k, l)**.

Replaces the hardcoded vertex/face-index tables of
`Cohomology/Cup/FinBridge.lean` (Δ⁴-specific, decide-enumerated)
with a structural ∀(n, k, l) capstone built on:

  · `kSubset_take_eq` — `(kSubset n (k+l) j).take k = kSubset n k j_a`
    for some valid `j_a`.
  · `kSubset_drop_eq` — `(kSubset n (k+l) j).drop k = kSubset n l j_b`
    for some valid `j_b`.
  · `roundtrip_n_k` — `subsetIdx n k (kSubset n k j) = j`.

The capstone `cup_unfold_general` then states:

  `cup n k l α β τ_idx = α ⟨frontIdx, _⟩ && β ⟨backIdx, _⟩`

for any `(n, k, l)` and any `τ_idx : Fin (binom n (k+l))`, where
`frontIdx = subsetIdx n k (take k)` and `backIdx = subsetIdx n l (drop k)`.

All theorems below are **PURE**.

PURE infrastructure required custom helpers bypassing
`List.take_append_of_le_length`, `List.length_take`, etc. (all
propext-tainted in Lean core).
-/

namespace E213.Lib.Math.Cohomology.Cup.FinBridgeGeneral

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip
  (roundtrip_n_k)
open E213.Lib.Math.Cohomology.Cup.KSubsetStructural
  (kSubset_length kSubset_all_lt kSubset_injective)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §0.  PURE List take/drop helpers — aliases to ListHelper

All take/drop append helpers centralised in
`Meta/Tactic/ListHelper.lean` per  /   Local aliases
preserve existing call sites. -/

@[reducible] private def take_append_le :
    ∀ (l₁ l₂ : List Nat) (k : Nat),
      k ≤ l₁.length → (l₁ ++ l₂).take k = l₁.take k :=
  E213.Tactic.ListHelper.take_append_le

@[reducible] private def drop_append_le :
    ∀ (l₁ l₂ : List Nat) (k : Nat),
      k ≤ l₁.length → (l₁ ++ l₂).drop k = l₁.drop k ++ l₂ :=
  E213.Tactic.ListHelper.drop_append_le

@[reducible] private def take_length_self :
    ∀ (l : List Nat), l.take l.length = l :=
  E213.Tactic.ListHelper.take_length_self

@[reducible] private def drop_length_self :
    ∀ (l : List Nat), l.drop l.length = [] :=
  E213.Tactic.ListHelper.drop_length_self

@[reducible] private def take_of_length_le :
    ∀ (l : List Nat) (k : Nat), l.length ≤ k → l.take k = l :=
  E213.Tactic.ListHelper.take_of_length_le

@[reducible] private def drop_of_length_le :
    ∀ (l : List Nat) (k : Nat), l.length ≤ k → l.drop k = [] :=
  E213.Tactic.ListHelper.drop_of_length_le

open E213.Lib.Math.Cohomology.Cup.KSubsetStructural
  (nat_add_sub_cancel nat_sub_lt_sub_right list_length_append_singleton
   nat_sub_pos_of_lt)

/-- `binom n 0 = 1` for all `n`.  PURE (via `cases n`).
    Replicated locally to avoid a transitive import.  -/
private theorem binom_n_0 (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

/-- `binom p m ≤ binom (p+1) m` — Pascal monotonicity in first arg.  PURE. -/
private theorem binom_le_binom_succ (p m : Nat) :
    binom p m ≤ binom (p+1) m := by
  cases m with
  | zero =>
    rw [binom_n_0 p, binom_n_0 (p+1)]
    exact Nat.le_refl 1
  | succ k =>
    show binom p (k+1) ≤ binom p k + binom p (k+1)
    exact Nat.le_add_left _ _

/-! ## §1.  Structural take-equation for `kSubset` -/

/-- ★★★ **kSubset take-equation** — `take k` of `kSubset n m j` is itself
    a `kSubset n k j_a` for some valid `j_a < binom n k`.

    Tracks the colex recursion: when the appended `[n]` lies entirely
    in the dropped tail (k ≤ m-1 case), the take stays in the
    list-prefix and follows the IH; when `k = m` we take the whole
    list (the appended element included), giving `j_a = j` itself.
    PURE.  -/
theorem kSubset_take_eq :
    ∀ (n m k : Nat), k ≤ m → ∀ (j : Nat), j < binom n m →
      ∃ j_a, j_a < binom n k ∧
        (kSubset n m j).take k = kSubset n k j_a := by
  intro n
  induction n with
  | zero =>
    intro m k h_km j h_j
    cases m with
    | zero =>
      have hk : k = 0 := Nat.le_zero.mp h_km
      subst hk
      cases j with
      | zero => exact ⟨0, Nat.zero_lt_one, rfl⟩
      | succ kj =>
        exact absurd h_j (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.zero_le kj)))
    | succ m' =>
      exact absurd h_j (Nat.not_lt_zero j)
  | succ p ih =>
    intro m k h_km j h_j
    cases m with
    | zero =>
      have hk : k = 0 := Nat.le_zero.mp h_km
      subst hk
      cases j with
      | zero => exact ⟨0, Nat.zero_lt_one, rfl⟩
      | succ kj =>
        exact absurd h_j (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.zero_le kj)))
    | succ m' =>
      cases k with
      | zero =>
        -- take 0 of anything = []; kSubset (p+1) 0 0 = []
        exact ⟨0, Nat.zero_lt_one, rfl⟩
      | succ k' =>
        have h_k'_le_m' : k' ≤ m' := Nat.le_of_succ_le_succ h_km
        show ∃ j_a, j_a < binom (p+1) (k'+1) ∧
            ((if j < binom p (m'+1) then kSubset p (m'+1) j
              else kSubset p m' (j - binom p (m'+1)) ++ [p])).take (k'+1)
            = kSubset (p+1) (k'+1) j_a
        by_cases h_j_lt : j < binom p (m'+1)
        · -- j < split branch
          rw [if_pos h_j_lt]
          obtain ⟨j_a, h_ja_lt, h_eq⟩ := ih (m'+1) (k'+1) h_km j h_j_lt
          refine ⟨j_a, Nat.lt_of_lt_of_le h_ja_lt (Nat.le_add_left _ _), ?_⟩
          rw [h_eq]
          -- want: kSubset p (k'+1) j_a = kSubset (p+1) (k'+1) j_a
          show kSubset p (k'+1) j_a
            = (if j_a < binom p (k'+1) then kSubset p (k'+1) j_a
                else kSubset p k' (j_a - binom p (k'+1)) ++ [p])
          rw [if_pos h_ja_lt]
        · -- j ≥ split branch
          rw [if_neg h_j_lt]
          have h_j_ge : binom p (m'+1) ≤ j := Nat.le_of_not_lt h_j_lt
          have h_j_sub : j - binom p (m'+1) < binom p m' := by
            have h_lt : j < binom p m' + binom p (m'+1) := h_j
            have h_sub : j - binom p (m'+1)
                < (binom p m' + binom p (m'+1)) - binom p (m'+1) :=
              nat_sub_lt_sub_right (binom p (m'+1)) h_j_ge h_lt
            rwa [nat_add_sub_cancel] at h_sub
          have h_list_len : (kSubset p m' (j - binom p (m'+1))).length = m' :=
            kSubset_length p m' (j - binom p (m'+1)) h_j_sub
          by_cases h_k'_lt_m' : k' < m'
          · -- k' < m': take (k'+1) is within the list-prefix
            have h_kp1_le : k'+1 ≤ (kSubset p m' (j - binom p (m'+1))).length := by
              rw [h_list_len]; exact h_k'_lt_m'
            rw [take_append_le _ _ _ h_kp1_le]
            obtain ⟨j_a, h_ja_lt, h_eq⟩ :=
              ih m' (k'+1) h_k'_lt_m' (j - binom p (m'+1)) h_j_sub
            refine ⟨j_a, Nat.lt_of_lt_of_le h_ja_lt (Nat.le_add_left _ _), ?_⟩
            rw [h_eq]
            show kSubset p (k'+1) j_a
              = (if j_a < binom p (k'+1) then kSubset p (k'+1) j_a
                  else kSubset p k' (j_a - binom p (k'+1)) ++ [p])
            rw [if_pos h_ja_lt]
          · -- k' = m': take the whole thing (list ++ [p])
            have h_k'_eq_m' : k' = m' := Nat.le_antisymm h_k'_le_m'
              (Nat.le_of_not_lt h_k'_lt_m')
            subst h_k'_eq_m'
            -- Now k' takes the role of m' in subsequent goals
            have h_len_le :
                (kSubset p k' (j - binom p (k'+1)) ++ [p]).length ≤ k' + 1 := by
              rw [list_length_append_singleton, h_list_len]
              exact Nat.le_refl _
            rw [take_of_length_le _ _ h_len_le]
            refine ⟨j, h_j, ?_⟩
            show kSubset p k' (j - binom p (k'+1)) ++ [p]
              = (if j < binom p (k'+1) then kSubset p (k'+1) j
                  else kSubset p k' (j - binom p (k'+1)) ++ [p])
            rw [if_neg h_j_lt]


/-! ## §2.  Structural drop-equation for `kSubset` -/

/-- ★★★ **kSubset drop-equation** — `drop k` of `kSubset n m j` is
    `kSubset n (m - k) j_b` for some valid `j_b < binom n (m - k)`.

    Dual to `kSubset_take_eq`.  When the colex recursion appends `[n]`,
    drop carries the appended element forward (drop_append_le); the
    result lives in the higher half of the colex enumeration at level
    `m-k` of `n+1`, yielding `j_b = binom p (m-k) + (inner-IH index)`.
    PURE.  -/
theorem kSubset_drop_eq :
    ∀ (n m k : Nat), k ≤ m → ∀ (j : Nat), j < binom n m →
      ∃ j_b, j_b < binom n (m - k) ∧
        (kSubset n m j).drop k = kSubset n (m - k) j_b := by
  intro n
  induction n with
  | zero =>
    intro m k h_km j h_j
    cases m with
    | zero =>
      have hk : k = 0 := Nat.le_zero.mp h_km
      subst hk
      cases j with
      | zero => exact ⟨0, Nat.zero_lt_one, rfl⟩
      | succ kj =>
        exact absurd h_j (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.zero_le kj)))
    | succ m' =>
      exact absurd h_j (Nat.not_lt_zero j)
  | succ p ih =>
    intro m k h_km j h_j
    cases m with
    | zero =>
      have hk : k = 0 := Nat.le_zero.mp h_km
      subst hk
      cases j with
      | zero => exact ⟨0, Nat.zero_lt_one, rfl⟩
      | succ kj =>
        exact absurd h_j (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.zero_le kj)))
    | succ m' =>
      cases k with
      | zero =>
        -- drop 0 = entire list; m - 0 = m
        exact ⟨j, h_j, rfl⟩
      | succ k' =>
        have h_k'_le_m' : k' ≤ m' := Nat.le_of_succ_le_succ h_km
        show ∃ j_b, j_b < binom (p+1) ((m'+1) - (k'+1)) ∧
            ((if j < binom p (m'+1) then kSubset p (m'+1) j
              else kSubset p m' (j - binom p (m'+1)) ++ [p])).drop (k'+1)
            = kSubset (p+1) ((m'+1) - (k'+1)) j_b
        -- (m'+1) - (k'+1) = m' - k' by Nat.succ_sub_succ_eq_sub
        rw [Nat.succ_sub_succ_eq_sub]
        by_cases h_j_lt : j < binom p (m'+1)
        · -- j < split branch
          rw [if_pos h_j_lt]
          obtain ⟨j_b, h_jb_lt, h_eq⟩ := ih (m'+1) (k'+1) h_km j h_j_lt
          rw [Nat.succ_sub_succ_eq_sub] at h_jb_lt h_eq
          refine ⟨j_b, Nat.lt_of_lt_of_le h_jb_lt (binom_le_binom_succ p _), ?_⟩
          rw [h_eq]
          -- Want: kSubset p (m' - k') j_b = kSubset (p+1) (m' - k') j_b
          cases h_diff : m' - k' with
          | zero =>
            -- m' - k' = 0: both sides are []
            show kSubset p 0 j_b = kSubset (p+1) 0 j_b
            cases p <;> rfl
          | succ k'' =>
            -- m' - k' = k''+1
            rw [h_diff] at h_jb_lt
            show kSubset p (k''+1) j_b
              = (if j_b < binom p (k''+1) then kSubset p (k''+1) j_b
                  else kSubset p k'' (j_b - binom p (k''+1)) ++ [p])
            rw [if_pos h_jb_lt]
        · -- j ≥ split branch
          rw [if_neg h_j_lt]
          have h_j_ge : binom p (m'+1) ≤ j := Nat.le_of_not_lt h_j_lt
          have h_j_sub : j - binom p (m'+1) < binom p m' := by
            have h_lt : j < binom p m' + binom p (m'+1) := h_j
            have h_sub : j - binom p (m'+1)
                < (binom p m' + binom p (m'+1)) - binom p (m'+1) :=
              nat_sub_lt_sub_right (binom p (m'+1)) h_j_ge h_lt
            rwa [nat_add_sub_cancel] at h_sub
          have h_list_len : (kSubset p m' (j - binom p (m'+1))).length = m' :=
            kSubset_length p m' (j - binom p (m'+1)) h_j_sub
          by_cases h_k'_lt_m' : k' < m'
          · -- k' < m': drop (k'+1) splits into prefix-drop ++ [p]
            have h_kp1_le : k'+1 ≤ (kSubset p m' (j - binom p (m'+1))).length := by
              rw [h_list_len]; exact h_k'_lt_m'
            rw [drop_append_le _ _ _ h_kp1_le]
            obtain ⟨j_b', h_jb'_lt, h_eq⟩ :=
              ih m' (k'+1) h_k'_lt_m' (j - binom p (m'+1)) h_j_sub
            -- h_jb'_lt : j_b' < binom p (m' - (k'+1))
            -- h_eq : (kSubset p m' (j - split)).drop (k'+1) = kSubset p (m' - (k'+1)) j_b'
            -- Goal needs (m' - k') level.  Express m' - k' = (m' - (k'+1)) + 1 since k' < m'.
            have h_m_diff_succ : m' - k' = (m' - (k' + 1)) + 1 := by
              have h_le : k' + 1 ≤ m' := h_k'_lt_m'
              -- m' - k' = (m' - k') ; m' - (k'+1) = m' - k' - 1
              -- (m' - k' - 1) + 1 = m' - k' when m' - k' > 0
              show m' - k' = m' - (k' + 1) + 1
              rw [Nat.sub_succ]
              -- (m' - k').pred + 1 = m' - k'   when m' - k' > 0
              have h_pos : 0 < m' - k' := nat_sub_pos_of_lt h_k'_lt_m'
              exact (Nat.succ_pred_eq_of_pos h_pos).symm
            rw [h_eq, h_m_diff_succ]
            -- Goal: kSubset p (m' - (k'+1)) j_b' ++ [p] = kSubset (p+1) ((m' - (k'+1)) + 1) j_b
            refine ⟨binom p ((m' - (k'+1)) + 1) + j_b', ?_, ?_⟩
            · -- j_b < binom (p+1) ((m' - (k'+1)) + 1)
              show binom p (m' - (k'+1) + 1) + j_b' < binom p (m' - (k'+1)) + binom p (m' - (k'+1) + 1)
              rw [Nat.add_comm (binom p (m' - (k'+1))) (binom p (m' - (k'+1) + 1))]
              exact Nat.add_lt_add_left h_jb'_lt _
            · -- kSubset p (m' - (k'+1)) j_b' ++ [p] = kSubset (p+1) ((m' - (k'+1)) + 1) (...)
              show kSubset p (m' - (k'+1)) j_b' ++ [p]
                = (if binom p (m' - (k'+1) + 1) + j_b' < binom p (m' - (k'+1) + 1)
                   then kSubset p (m' - (k'+1) + 1) (binom p (m' - (k'+1) + 1) + j_b')
                   else kSubset p (m' - (k'+1))
                          ((binom p (m' - (k'+1) + 1) + j_b') - binom p (m' - (k'+1) + 1)) ++ [p])
              have h_not_lt :
                  ¬ (binom p (m' - (k'+1) + 1) + j_b' < binom p (m' - (k'+1) + 1)) :=
                Nat.not_lt_of_le (Nat.le_add_right _ _)
              rw [if_neg h_not_lt, Nat.add_comm (binom p _), nat_add_sub_cancel]
          · -- k' = m': drop (k'+1) = drop (m'+1) = empty
            have h_k'_eq_m' : k' = m' := Nat.le_antisymm h_k'_le_m'
              (Nat.le_of_not_lt h_k'_lt_m')
            subst h_k'_eq_m'
            -- Total length = k'+1, drop (k'+1) = []
            have h_full_len :
                (kSubset p k' (j - binom p (k'+1)) ++ [p]).length ≤ k' + 1 := by
              rw [list_length_append_singleton, h_list_len]
              exact Nat.le_refl _
            rw [drop_of_length_le _ _ h_full_len]
            -- Need kSubset (p+1) (k' - k') j_b = []
            rw [show k' - k' = 0 from Nat.sub_self k']
            exact ⟨0, Nat.zero_lt_one, rfl⟩


/-! ## §3.  General frontIdx / backIdx + cup unfold capstone -/

/-- General `frontIdx` — the colex index of the front `k`-vertex prefix
    of the `(k+l)`-subset `kSubset n (k+l) j`.  -/
def frontIdx (n k l j : Nat) : Nat :=
  subsetIdx n k ((kSubset n (k + l) j).take k)

/-- General `backIdx` — the colex index of the back `l`-vertex suffix
    of the `(k+l)`-subset `kSubset n (k+l) j`.  -/
def backIdx (n k l j : Nat) : Nat :=
  subsetIdx n l ((kSubset n (k + l) j).drop k)

/-- ★ `frontIdx n k l j < binom n k` when `j < binom n (k+l)`.  PURE
    via `kSubset_take_eq` + `roundtrip_n_k`.  -/
theorem frontIdx_lt (n k l j : Nat) (h : j < binom n (k + l)) :
    frontIdx n k l j < binom n k := by
  obtain ⟨j_a, h_ja_lt, h_eq⟩ :=
    kSubset_take_eq n (k+l) k (Nat.le_add_right k l) j h
  show subsetIdx n k ((kSubset n (k+l) j).take k) < binom n k
  rw [h_eq, roundtrip_n_k n k j_a h_ja_lt]
  exact h_ja_lt

/-- ★ `backIdx n k l j < binom n l` when `j < binom n (k+l)`.  PURE. -/
theorem backIdx_lt (n k l j : Nat) (h : j < binom n (k + l)) :
    backIdx n k l j < binom n l := by
  obtain ⟨j_b, h_jb_lt, h_eq⟩ :=
    kSubset_drop_eq n (k+l) k (Nat.le_add_right k l) j h
  -- (k+l) - k = l
  have h_kl_sub : (k + l) - k = l := by
    rw [Nat.add_comm k l, nat_add_sub_cancel]
  rw [h_kl_sub] at h_jb_lt h_eq
  show subsetIdx n l ((kSubset n (k+l) j).drop k) < binom n l
  rw [h_eq, roundtrip_n_k n l j_b h_jb_lt]
  exact h_jb_lt

/-- ★★★★★ **General cup unfold ∀(n, k, l)** — the merge-ready capstone.

    For any `(n, k, l)`, any cochains `α, β`, and any `τ_idx : Fin (binom n (k+l))`,
    the cup product unfolds to a single AND of cochain values at the
    `frontIdx` (k-prefix) and `backIdx` (l-suffix).

    Replaces the hardcoded `Cohomology/Cup/FinBridge.lean` unfold lemmas
    (Δ⁴-specific, 10240 decide cases per bidegree) with a structural ∀
    statement on top of `kSubset_take_eq` / `kSubset_drop_eq` / `roundtrip_n_k`.
    PURE.  -/
theorem cup_unfold_general (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (τ_idx : Fin (binom n (k + l))) :
    cup n k l α β τ_idx
      = (α ⟨frontIdx n k l τ_idx.val,
              frontIdx_lt n k l τ_idx.val τ_idx.isLt⟩
         && β ⟨backIdx n k l τ_idx.val,
                backIdx_lt n k l τ_idx.val τ_idx.isLt⟩) := by
  show (if hf : subsetIdx n k ((kSubset n (k+l) τ_idx.val).take k) < binom n k
        then (if hb : subsetIdx n l ((kSubset n (k+l) τ_idx.val).drop k) < binom n l
              then α ⟨_, hf⟩ && β ⟨_, hb⟩ else false)
        else false) = _
  have hf : subsetIdx n k ((kSubset n (k+l) τ_idx.val).take k) < binom n k :=
    frontIdx_lt n k l τ_idx.val τ_idx.isLt
  have hb : subsetIdx n l ((kSubset n (k+l) τ_idx.val).drop k) < binom n l :=
    backIdx_lt n k l τ_idx.val τ_idx.isLt
  rw [dif_pos hf, dif_pos hb]
  rfl

end E213.Lib.Math.Cohomology.Cup.FinBridgeGeneral
