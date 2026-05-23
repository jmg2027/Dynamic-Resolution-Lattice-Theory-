import E213.Lib.Math.Padic.NegInvolutionFull
/-!
# Zp.neg involution — preservation invariant + full sequence theorem

Completes the State Accumulator Pattern (Gemini blocker-1 solution)
with the **preservation invariant**:

  `all_zero_below (Zp.neg x) k = all_zero_below x k`  for all k

The constant-branching induction:
  - Case `all_zero_below x j = true`: carry triggers
    `(Zp.neg x).digit_j = (p - x.digit_j) % p` which is 0 iff
    x.digit_j = 0.  AND with prior all-zero preserves the invariant.
  - Case `all_zero_below x j = false`: AND with false short-circuits;
    invariant holds trivially.

Then the full involution `((Zp.neg(Zp.neg x)).digits k).val = (x.digits k).val`
follows by case-split on `all_zero_below x k`.

All declarations PURE.
-/

namespace E213.Lib.Math.Padic.NegInvolutionPreserve

open E213.Meta.Nat.AddMod213 (double_neg_mod_at)
open E213.Tactic.NatHelper (add_right_cancel_pure div_self_pure)
open E213.Lib.Math.Padic.NegInvolutionFull
  (all_zero_below all_zero_below_zero all_zero_below_succ
   neg_carry_eq_state)

/-! ## §1 — Zp.neg digit-j formula via state accumulator -/

/-- ★ **Zp.neg digit-j formula**: parametric in `all_zero_below x j`. -/
theorem zp_neg_digit_succ_with_state (p : Nat) (hp : 1 < p) (x : ZpSeq p) (j : Nat) :
    ((Zp.neg p hp x).digits (j + 1)).val
    = (p - 1 - (x.digits (j + 1)).val
       + (if all_zero_below x (j + 1) = true then 1 else 0)) % p := by
  show ((Zp.add p (Nat.lt_of_succ_lt hp)
            (Zp.complement p (Nat.lt_of_succ_lt hp) x)
            (ZpSeq.one p hp)).digits (j + 1)).val
       = _
  rw [Zp.add_digit_val p (Nat.lt_of_succ_lt hp) _ _ (j + 1)]
  rw [neg_carry_eq_state p hp x j]
  rw [Zp.complement_digit_val p (Nat.lt_of_succ_lt hp) x (j + 1)]
  -- (one).digit_(j+1) = 0
  show (p - 1 - (x.digits (j+1)).val
          + ((ZpSeq.one p hp).digits (j+1)).val
          + (if all_zero_below x (j+1) = true then 1 else 0)) % p
       = _
  show (p - 1 - (x.digits (j+1)).val + 0
          + (if all_zero_below x (j+1) = true then 1 else 0)) % p
       = _
  rw [Nat.add_zero]

/-! ## §2 — Preservation invariant -/

/-- ★★★★ **Preservation invariant** (the State Accumulator Pattern
    payoff): `all_zero_below` is invariant under `Zp.neg`. -/
theorem neg_preserves_state (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ∀ k, all_zero_below (Zp.neg p hp x) k = all_zero_below x k
  | 0 => rfl
  | k + 1 => by
    rw [all_zero_below_succ (Zp.neg p hp x) k]
    rw [all_zero_below_succ x k]
    rw [neg_preserves_state p hp x k]
    -- Goal: (decide ((Zp.neg x).digit_k = 0) && all_zero_below x k)
    --     = (decide (x.digit_k = 0) && all_zero_below x k)
    -- Case-split on all_zero_below x k
    by_cases h_prior : all_zero_below x k = true
    · -- Prior all-zero: carry = 1, (Zp.neg x).digit_k = (p - x.digit_k) % p
      rw [h_prior, Bool.and_true, Bool.and_true]
      -- Need: decide ((Zp.neg x).digit_k = 0) = decide (x.digit_k = 0)
      -- (Zp.neg x).digit_k = 0 iff x.digit_k = 0
      cases k with
      | zero =>
        -- (Zp.neg x).digit_0 = (p - x.digit_0) % p
        rw [E213.Lib.Math.Padic.NegInvolution.zp_neg_digit_zero p hp x]
        -- decide ((p - x.digit_0) % p = 0) = decide (x.digit_0 = 0)
        by_cases h_x : (x.digits 0).val = 0
        · rw [h_x]
          show decide ((p - 0) % p = 0) = decide (0 = 0)
          rw [Nat.sub_zero, E213.Meta.Nat.AddMod213.mod_self p]
        · have h_pos : 0 < (x.digits 0).val := Nat.pos_of_ne_zero h_x
          have h_psub_lt : p - (x.digits 0).val < p :=
            Nat.sub_lt (Nat.lt_of_succ_lt hp) h_pos
          have h_psub_mod : (p - (x.digits 0).val) % p = p - (x.digits 0).val :=
            Nat.mod_eq_of_lt h_psub_lt
          rw [h_psub_mod]
          have h_psub_pos : 0 < p - (x.digits 0).val :=
            E213.Tactic.NatHelper.sub_pos_of_lt (x.digits 0).isLt
          have h_psub_ne : ¬ (p - (x.digits 0).val = 0) :=
            Nat.ne_of_gt h_psub_pos
          rw [decide_eq_false h_psub_ne, decide_eq_false h_x]
      | succ j =>
        rw [zp_neg_digit_succ_with_state p hp x j]
        rw [h_prior]
        rw [if_pos rfl]
        -- Goal: decide ((p - 1 - x.digit_(j+1) + 1) % p = 0) = decide (x.digit_(j+1) = 0)
        -- p - 1 - x + 1 = p - x; (p - x) % p = 0 iff x = 0
        have ha : (x.digits (j+1)).val ≤ p - 1 :=
          Nat.le_sub_one_of_lt (x.digits (j+1)).isLt
        have hfold : p - 1 - (x.digits (j+1)).val + 1
                   = p - (x.digits (j+1)).val := by
          have lhs_full :
              (p - 1 - (x.digits (j+1)).val + 1) + (x.digits (j+1)).val = p := by
            rw [Nat.add_assoc, Nat.add_comm 1 (x.digits (j+1)).val]
            rw [← Nat.add_assoc]
            rw [E213.Tactic.NatHelper.sub_add_cancel ha]
            exact E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hp)
          have rhs_full :
              (p - (x.digits (j+1)).val) + (x.digits (j+1)).val = p :=
            E213.Tactic.NatHelper.sub_add_cancel
              (Nat.le_of_lt (x.digits (j+1)).isLt)
          have h_eq :
              (p - 1 - (x.digits (j+1)).val + 1) + (x.digits (j+1)).val
              = (p - (x.digits (j+1)).val) + (x.digits (j+1)).val := by
            rw [lhs_full, rhs_full]
          exact add_right_cancel_pure h_eq
        rw [hfold]
        by_cases h_x : (x.digits (j+1)).val = 0
        · rw [h_x]
          show decide ((p - 0) % p = 0) = decide (0 = 0)
          rw [Nat.sub_zero, E213.Meta.Nat.AddMod213.mod_self p]
        · have h_pos : 0 < (x.digits (j+1)).val := Nat.pos_of_ne_zero h_x
          have h_psub_lt : p - (x.digits (j+1)).val < p :=
            Nat.sub_lt (Nat.lt_of_succ_lt hp) h_pos
          have h_psub_mod : (p - (x.digits (j+1)).val) % p
                          = p - (x.digits (j+1)).val :=
            Nat.mod_eq_of_lt h_psub_lt
          rw [h_psub_mod]
          have h_psub_pos : 0 < p - (x.digits (j+1)).val :=
            E213.Tactic.NatHelper.sub_pos_of_lt (x.digits (j+1)).isLt
          have h_psub_ne : ¬ (p - (x.digits (j+1)).val = 0) :=
            Nat.ne_of_gt h_psub_pos
          rw [decide_eq_false h_psub_ne, decide_eq_false h_x]
    · -- Prior not all-zero: AND short-circuits both sides to false
      have h_false : all_zero_below x k = false := by
        cases h : all_zero_below x k with
        | true => exact absurd h h_prior
        | false => rfl
      rw [h_false, Bool.and_false, Bool.and_false]

/-! ## §3 — Full digit-k involution -/

/-- ★★★★★ **Full Zp.neg involution at digit-k**: for arbitrary `k`,
    `((Zp.neg(Zp.neg x)).digits k).val = (x.digits k).val`.

    This is the **complete sequence-level involution as a
    pointwise identity**, no funext required.  Combines:
      · `neg_carry_eq_state` (carry-state correspondence)
      · `neg_preserves_state` (preservation invariant)
      · case-split on `all_zero_below x k`

    Gemini's State Accumulator Pattern realised end-to-end. -/
theorem zp_neg_neg_digit_at (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ∀ k, ((Zp.neg p hp (Zp.neg p hp x)).digits k).val = (x.digits k).val
  | 0 => E213.Lib.Math.Padic.NegInvolution.zp_neg_neg_digit_zero p hp x
  | k + 1 => by
    -- (Zp.neg(Zp.neg x)).digit_(k+1) via zp_neg_digit_succ_with_state
    rw [zp_neg_digit_succ_with_state p hp (Zp.neg p hp x) k]
    rw [neg_preserves_state p hp x (k+1)]
    -- Goal: (p - 1 - (Zp.neg x).digit_(k+1)
    --        + (if all_zero_below x (k+1) = true then 1 else 0)) % p
    --      = x.digit_(k+1)
    by_cases h_state : all_zero_below x (k+1) = true
    · -- Prior all-zero → carry = 1, (Zp.neg x).digit_(k+1) = (p - x.digit) % p
      rw [if_pos h_state]
      rw [zp_neg_digit_succ_with_state p hp x k]
      rw [h_state, if_pos rfl]
      -- LHS = (p - 1 - ((p - 1 - x + 1) % p) + 1) % p
      -- Step 1: p - 1 - x + 1 = p - x (via hfold)
      have ha : (x.digits (k+1)).val ≤ p - 1 :=
        Nat.le_sub_one_of_lt (x.digits (k+1)).isLt
      have hfold : p - 1 - (x.digits (k+1)).val + 1
                 = p - (x.digits (k+1)).val := by
        have lhs_full :
            (p - 1 - (x.digits (k+1)).val + 1) + (x.digits (k+1)).val = p := by
          rw [Nat.add_assoc, Nat.add_comm 1 (x.digits (k+1)).val]
          rw [← Nat.add_assoc]
          rw [E213.Tactic.NatHelper.sub_add_cancel ha]
          exact E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hp)
        have rhs_full :
            (p - (x.digits (k+1)).val) + (x.digits (k+1)).val = p :=
          E213.Tactic.NatHelper.sub_add_cancel
            (Nat.le_of_lt (x.digits (k+1)).isLt)
        have h_eq :
            (p - 1 - (x.digits (k+1)).val + 1) + (x.digits (k+1)).val
            = (p - (x.digits (k+1)).val) + (x.digits (k+1)).val := by
          rw [lhs_full, rhs_full]
        exact add_right_cancel_pure h_eq
      rw [hfold]
      -- LHS = (p - 1 - ((p - x) % p) + 1) % p
      -- Step 2: same hfold on p - 1 - ((p - x) % p) + 1 = p - ((p - x) % p)
      -- We need to know the inner ((p-x) % p) for hfold.  It's a value < p.
      have h_inner_lt : (p - (x.digits (k+1)).val) % p < p :=
        Nat.mod_lt _ (Nat.lt_of_succ_lt hp)
      have h_inner_le : (p - (x.digits (k+1)).val) % p ≤ p - 1 :=
        Nat.le_sub_one_of_lt h_inner_lt
      have hfold2 :
          p - 1 - ((p - (x.digits (k+1)).val) % p) + 1
          = p - ((p - (x.digits (k+1)).val) % p) := by
        have lhs_full :
            (p - 1 - ((p - (x.digits (k+1)).val) % p) + 1)
              + ((p - (x.digits (k+1)).val) % p) = p := by
          rw [Nat.add_assoc, Nat.add_comm 1 _]
          rw [← Nat.add_assoc]
          rw [E213.Tactic.NatHelper.sub_add_cancel h_inner_le]
          exact E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hp)
        have rhs_full :
            (p - ((p - (x.digits (k+1)).val) % p))
              + ((p - (x.digits (k+1)).val) % p) = p :=
          E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt h_inner_lt)
        have h_eq :
            (p - 1 - ((p - (x.digits (k+1)).val) % p) + 1)
              + ((p - (x.digits (k+1)).val) % p)
            = (p - ((p - (x.digits (k+1)).val) % p))
              + ((p - (x.digits (k+1)).val) % p) := by
          rw [lhs_full, rhs_full]
        exact add_right_cancel_pure h_eq
      rw [hfold2]
      -- LHS = (p - ((p - x) % p)) % p = x.digit_(k+1)
      exact double_neg_mod_at p (x.digits (k+1)).val
        (Nat.lt_of_succ_lt hp) (x.digits (k+1)).isLt
    · -- Prior not all-zero → carry = 0, (Zp.neg x).digit_(k+1) = (p-1-x) % p
      have h_state_false : all_zero_below x (k+1) = false := by
        cases h : all_zero_below x (k+1) with
        | true => exact absurd h h_state
        | false => rfl
      rw [if_neg h_state]
      rw [zp_neg_digit_succ_with_state p hp x k]
      rw [h_state_false]
      rw [if_neg (fun h => Bool.false_ne_true h)]
      -- LHS = (p - 1 - ((p - 1 - x + 0) % p) + 0) % p
      rw [Nat.add_zero]
      -- (p - 1 - x.digit_(k+1)) % p = p - 1 - x.digit_(k+1) (since < p)
      have ha : (x.digits (k+1)).val ≤ p - 1 :=
        Nat.le_sub_one_of_lt (x.digits (k+1)).isLt
      have h_sub_lt : p - 1 - (x.digits (k+1)).val < p := by
        apply Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) _)
        exact Nat.sub_lt (Nat.lt_of_succ_lt hp) Nat.one_pos
      have h_sub_mod : (p - 1 - (x.digits (k+1)).val) % p
                     = p - 1 - (x.digits (k+1)).val :=
        Nat.mod_eq_of_lt h_sub_lt
      rw [Nat.add_zero, h_sub_mod]
      -- LHS = (p - 1 - (p - 1 - x.digit_(k+1))) % p
      -- = x.digit_(k+1) % p = x.digit_(k+1)
      have h_inner : p - 1 - (p - 1 - (x.digits (k+1)).val)
                   = (x.digits (k+1)).val := by
        have h_sub_le : p - 1 - (x.digits (k+1)).val ≤ p - 1 :=
          Nat.sub_le _ _
        have lhs_full :
            (p - 1 - (p - 1 - (x.digits (k+1)).val))
              + (p - 1 - (x.digits (k+1)).val) = p - 1 :=
          E213.Tactic.NatHelper.sub_add_cancel h_sub_le
        have rhs_full :
            (x.digits (k+1)).val + (p - 1 - (x.digits (k+1)).val) = p - 1 := by
          rw [Nat.add_comm]
          exact E213.Tactic.NatHelper.sub_add_cancel ha
        have h_eq :
            (p - 1 - (p - 1 - (x.digits (k+1)).val))
              + (p - 1 - (x.digits (k+1)).val)
            = (x.digits (k+1)).val
              + (p - 1 - (x.digits (k+1)).val) := by
          rw [lhs_full, rhs_full]
        exact add_right_cancel_pure h_eq
      rw [h_inner]
      exact Nat.mod_eq_of_lt (x.digits (k+1)).isLt

/-! ## §4 — Capstone -/

/-- ★★★★★ **Full Zp.neg involution capstone**: the trajectory-pw
    realisation of `Zp.neg ∘ Zp.neg = id` at every digit.

    Bundles: (a) preservation invariant
    `all_zero_below (Zp.neg x) k = all_zero_below x k`,
    (b) digit-k formula via state accumulator,
    (c) full involution `((Zp.neg(Zp.neg x)).digits k).val = (x.digits k).val`
    for arbitrary k.

    The funext-blocked sequence-level identity is realised as a
    pointwise (∀ k) PURE theorem via Gemini's State Accumulator
    Pattern: polynomial blow-up of carry chain collapses to
    constant-branching induction. -/
theorem zp_neg_full_involution_capstone
    (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    -- (a) Preservation invariant
    (∀ k, all_zero_below (Zp.neg p hp x) k = all_zero_below x k)
    -- (b) Digit-k formula
    ∧ (∀ j, ((Zp.neg p hp x).digits (j + 1)).val
            = (p - 1 - (x.digits (j + 1)).val
               + (if all_zero_below x (j + 1) = true then 1 else 0)) % p)
    -- (c) Full involution at every digit
    ∧ (∀ k, ((Zp.neg p hp (Zp.neg p hp x)).digits k).val
            = (x.digits k).val) := by
  refine ⟨?_, ?_, ?_⟩
  · exact neg_preserves_state p hp x
  · exact zp_neg_digit_succ_with_state p hp x
  · exact zp_neg_neg_digit_at p hp x

end E213.Lib.Math.Padic.NegInvolutionPreserve
