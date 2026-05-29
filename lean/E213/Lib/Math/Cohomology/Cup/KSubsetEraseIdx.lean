import E213.Lib.Math.Cohomology.Cup.KSubsetStructural
import E213.Lib.Math.Combinatorics.Binomial
import E213.Meta.Tactic.ListHelper

/-!
# Cohomology.Cup.KSubsetEraseIdx

Structural sibling of `KSubsetStructural`/`FinBridgeGeneral`:

  `kSubset_eraseIdx_eq` — for any valid `(n, m, j)` and any `i < m`,
  the list `(kSubset n m j).eraseIdx i` is itself a kSubset:

    `(kSubset n m j).eraseIdx i = kSubset n (m - 1) j_e`

  for some `j_e < binom n (m - 1)`.

Combined with `roundtrip_n_k`, this enables a well-defined
**face index** map `Fin (binom n m) → Fin (binom n (m-1))` (per
remove-position-i), which is the workhorse for the Fin-level
∀(n, k, l) twisted Leibniz.

PURE.  Mirrors the structure of `kSubset_take_eq` / `kSubset_drop_eq`.
-/

namespace E213.Lib.Math.Cohomology.Cup.KSubsetEraseIdx

open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Cup.KSubsetStructural
  (kSubset_length kSubset_all_lt nat_add_sub_cancel nat_sub_lt_sub_right
   list_length_append_singleton)
open E213.Lib.Physics.Simplex.Counts (binom)

open E213.Lib.Math.Combinatorics.Binomial (binom_n_0 binom_le_binom_succ)

/-! ## §1.  Main structural lemma: `kSubset_eraseIdx_eq` -/

/-- ★★★ **kSubset eraseIdx-equation** — `eraseIdx i` of `kSubset n m j`
    is itself `kSubset n (m-1) j_e` for some valid `j_e < binom n (m-1)`,
    whenever `i < m` and `j < binom n m`.

    Induction on `n`, mirroring `kSubset_take_eq` / `kSubset_drop_eq`.
    The colex split (j < pivot vs j ≥ pivot) handles the two halves:
    inside the prefix (recurse on the inner list); inside the
    `_ ++ [p]` (cases on whether `i` is in the inner list or
    targets the appended element).  PURE. -/
theorem kSubset_eraseIdx_eq :
    ∀ (n m : Nat) (i : Nat), i < m → ∀ (j : Nat), j < binom n m →
      ∃ j_e, j_e < binom n (m - 1) ∧
        (kSubset n m j).eraseIdx i = kSubset n (m - 1) j_e := by
  intro n
  induction n with
  | zero =>
    intro m i h_im j h_j
    cases m with
    | zero => exact absurd h_im (Nat.not_lt_zero i)
    | succ m' => exact absurd h_j (Nat.not_lt_zero j)
  | succ p ih =>
    intro m i h_im j h_j
    cases m with
    | zero => exact absurd h_im (Nat.not_lt_zero i)
    | succ m' =>
      -- (m'+1) - 1 = m'
      show ∃ j_e, j_e < binom (p+1) m' ∧
          (kSubset (p+1) (m'+1) j).eraseIdx i = kSubset (p+1) m' j_e
      -- Unfold kSubset (p+1) (m'+1) j
      show ∃ j_e, j_e < binom (p+1) m' ∧
          ((if j < binom p (m'+1) then kSubset p (m'+1) j
            else kSubset p m' (j - binom p (m'+1)) ++ [p])).eraseIdx i
          = kSubset (p+1) m' j_e
      by_cases h_j_lt : j < binom p (m'+1)
      · -- j < split branch: stays inside p-prefix
        rw [if_pos h_j_lt]
        have h_i_succm' : i < m' + 1 := h_im
        obtain ⟨j_e, h_je_lt, h_eq⟩ := ih (m'+1) i h_i_succm' j h_j_lt
        -- h_je_lt : j_e < binom p ((m'+1) - 1) = binom p m'
        -- h_eq    : (kSubset p (m'+1) j).eraseIdx i = kSubset p m' j_e
        -- h_je_lt has type `j_e < binom p ((m'+1) - 1)`.  We
        -- normalize via a fresh hypothesis using Nat defeq.
        have h_je_lt' : j_e < binom p m' := h_je_lt
        refine ⟨j_e, ?_, ?_⟩
        · exact Nat.lt_of_lt_of_le h_je_lt' (binom_le_binom_succ p m')
        · rw [h_eq]
          cases h_m' : m' with
          | zero =>
            cases p <;> rfl
          | succ m'' =>
            rw [h_m'] at h_je_lt'
            show kSubset p (m''+1) j_e
              = (if j_e < binom p (m''+1) then kSubset p (m''+1) j_e
                  else kSubset p m'' (j_e - binom p (m''+1)) ++ [p])
            rw [if_pos h_je_lt']
      · -- j ≥ split branch: list is `inner ++ [p]`
        rw [if_neg h_j_lt]
        have h_j_ge : binom p (m'+1) ≤ j := Nat.le_of_not_lt h_j_lt
        have h_j_sub : j - binom p (m'+1) < binom p m' := by
          have h_lt : j < binom p m' + binom p (m'+1) := h_j
          have h_sub : j - binom p (m'+1)
              < (binom p m' + binom p (m'+1)) - binom p (m'+1) :=
            nat_sub_lt_sub_right (binom p (m'+1)) h_j_ge h_lt
          rwa [nat_add_sub_cancel] at h_sub
        have h_inner_len : (kSubset p m' (j - binom p (m'+1))).length = m' :=
          kSubset_length p m' (j - binom p (m'+1)) h_j_sub
        by_cases h_i_lt_m' : i < m'
        · -- i < m' = inner.length: erase stays in inner, [p] preserved
          have h_i_lt_innerlen :
              i < (kSubset p m' (j - binom p (m'+1))).length := by
            rw [h_inner_len]; exact h_i_lt_m'
          rw [E213.Tactic.ListHelper.eraseIdx_append_singleton_low
              _ p i h_i_lt_innerlen]
          -- Goal: (inner.eraseIdx i) ++ [p] = kSubset (p+1) m' j_e
          -- Recursive: inner.eraseIdx i = kSubset p (m'-1) j_inner
          obtain ⟨j_inner, h_jinner_lt, h_eq⟩ :=
            ih m' i h_i_lt_m' (j - binom p (m'+1)) h_j_sub
          -- h_jinner_lt : j_inner < binom p (m' - 1)
          -- We want j_e = binom p m' + j_inner so the result lives in
          -- the j ≥ split branch at level (p+1, m')
          cases h_m' : m' with
          | zero => exact absurd h_i_lt_m' (h_m' ▸ Nat.not_lt_zero i)
          | succ m'' =>
            -- m' = m''+1, so m' - 1 = m''
            rw [h_m'] at h_jinner_lt h_eq h_inner_len h_i_lt_innerlen h_i_lt_m'
            refine ⟨binom p (m''+1) + j_inner, ?_, ?_⟩
            · show binom p (m''+1) + j_inner
                  < binom p m'' + binom p (m''+1)
              rw [Nat.add_comm (binom p m'') (binom p (m''+1))]
              exact Nat.add_lt_add_left h_jinner_lt _
            · -- (inner.eraseIdx i) ++ [p] = kSubset (p+1) (m''+1)
              --   (binom p (m''+1) + j_inner)
              rw [h_eq]
              show kSubset p m'' j_inner ++ [p]
                = (if binom p (m''+1) + j_inner < binom p (m''+1)
                   then kSubset p (m''+1) (binom p (m''+1) + j_inner)
                   else kSubset p m''
                          ((binom p (m''+1) + j_inner) - binom p (m''+1))
                          ++ [p])
              have h_not_lt :
                  ¬ (binom p (m''+1) + j_inner < binom p (m''+1)) :=
                Nat.not_lt_of_le (Nat.le_add_right _ _)
              rw [if_neg h_not_lt, Nat.add_comm (binom p (m''+1)) j_inner,
                  nat_add_sub_cancel]
        · -- i ≥ m': i = m' (since i < m'+1)
          have h_i_eq_m' : i = m' := by
            have h_i_le_m' : i ≤ m' := Nat.le_of_lt_succ h_im
            have h_i_ge_m' : m' ≤ i := Nat.le_of_not_lt h_i_lt_m'
            exact Nat.le_antisymm h_i_le_m' h_i_ge_m'
          rw [h_i_eq_m']
          -- Localise the eraseIdx ↦ prefix rewrite to a single
          -- equation so `← h_inner_len` doesn't replace m' inside
          -- the kSubset arguments.
          have h_erase :
              (kSubset p m' (j - binom p (m'+1)) ++ [p]).eraseIdx m'
              = kSubset p m' (j - binom p (m'+1)) := by
            have key := E213.Tactic.ListHelper.eraseIdx_append_singleton_at_len
              (kSubset p m' (j - binom p (m'+1))) p
            rw [h_inner_len] at key
            exact key
          rw [h_erase]
          refine ⟨j - binom p (m'+1), ?_, ?_⟩
          · exact Nat.lt_of_lt_of_le h_j_sub (binom_le_binom_succ p m')
          · cases h_m' : m' with
            | zero =>
              cases p <;> rfl
            | succ m'' =>
              rw [h_m'] at h_j_sub
              show kSubset p (m''+1) (j - binom p (m''+2))
                = (if j - binom p (m''+2) < binom p (m''+1)
                   then kSubset p (m''+1) (j - binom p (m''+2))
                   else kSubset p m''
                          ((j - binom p (m''+2)) - binom p (m''+1)) ++ [p])
              rw [if_pos h_j_sub]

end E213.Lib.Math.Cohomology.Cup.KSubsetEraseIdx
