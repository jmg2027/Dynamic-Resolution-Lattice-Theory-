import E213.Lib.Math.NumberSystems.Padic.NegInvolution
/-!
# Zp.neg involution at digit-1 (carry-step rigor)

Extends `NegInvolution.lean` (digit-0) by one digit, tracking the
carry chain across `Zp.neg = complement + one`.

The key insight: `Zp.neg x` has a carry to digit-1 iff
`(x.digits 0).val = 0`.  Applied twice, the carry patterns at
digit-0 and digit-1 cancel to give the identity at digit-1.

Case-split on `(x.digits 0).val = 0`:

  Case A (digit-0 = 0):
    · (Zp.neg x).digit_0 = 0  (with carry 1 to digit-1)
    · (Zp.neg x).digit_1 = (p - x.digit_1) % p
    · (Zp.neg(Zp.neg x)).digit_1 = (p - ((p - x.digit_1) % p)) % p
                                  = x.digit_1  (double_neg_mod_at)

  Case B (digit-0 > 0):
    · (Zp.neg x).digit_0 = p - x.digit_0  (no carry)
    · (Zp.neg x).digit_1 = p - 1 - x.digit_1
    · (Zp.neg(Zp.neg x)).digit_1 = (p - 1 - (p - 1 - x.digit_1)) % p
                                  = x.digit_1

The trajectory-pw argument cleanly cancels in both cases.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.NegInvolutionDigit1

open E213.Meta.Nat.AddMod213 (double_neg_mod_at)
open E213.Tactic.NatHelper (add_right_cancel_pure)

/-! ## §1 — Carry of `complement x + one` at digit-1 -/

/-- ★ Carry at digit-1 of `Zp.neg x` is `(p - x.digit_0) / p`.

    Concretely: `1` if `x.digits 0 = 0`, else `0`. -/
theorem neg_carry_at_1 (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    Zp.carry p (Zp.complement p (Nat.lt_of_succ_lt hp) x)
                (ZpSeq.one p hp) 1
      = (p - (x.digits 0).val) / p := by
  rw [Zp.carry_succ]
  rw [Zp.carry_zero, Nat.add_zero]
  -- = ((complement x).digit_0 + one.digit_0) / p
  rw [Zp.complement_digit_val p (Nat.lt_of_succ_lt hp) x 0]
  show (p - 1 - (x.digits 0).val + ((ZpSeq.one p hp).digits 0).val) / p
       = (p - (x.digits 0).val) / p
  show (p - 1 - (x.digits 0).val + 1) / p
       = (p - (x.digits 0).val) / p
  -- p - 1 - a + 1 = p - a  when a ≤ p - 1 (proved as in NegInvolution)
  have ha : (x.digits 0).val ≤ p - 1 :=
    Nat.le_sub_one_of_lt (x.digits 0).isLt
  have hfold : p - 1 - (x.digits 0).val + 1 = p - (x.digits 0).val := by
    have lhs_full : (p - 1 - (x.digits 0).val + 1) + (x.digits 0).val = p := by
      rw [Nat.add_assoc, Nat.add_comm 1 (x.digits 0).val]
      rw [← Nat.add_assoc]
      rw [E213.Tactic.NatHelper.sub_add_cancel ha]
      exact E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hp)
    have rhs_full : (p - (x.digits 0).val) + (x.digits 0).val = p :=
      E213.Tactic.NatHelper.sub_add_cancel
        (Nat.le_of_lt (x.digits 0).isLt)
    have h_eq : (p - 1 - (x.digits 0).val + 1) + (x.digits 0).val
              = (p - (x.digits 0).val) + (x.digits 0).val := by
      rw [lhs_full, rhs_full]
    exact add_right_cancel_pure h_eq
  rw [hfold]

/-! ## §2 — Carry case-analysis -/

/-- Re-export `div_self_pure` from the Meta layer. -/
theorem div_self_pure (p : Nat) (hp : 0 < p) : p / p = 1 :=
  E213.Tactic.NatHelper.div_self_pure p hp

/-- ★ When `x.digit_0 = 0`: `(p - 0) / p = 1`. -/
theorem neg_carry_at_1_when_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h : (x.digits 0).val = 0) :
    Zp.carry p (Zp.complement p (Nat.lt_of_succ_lt hp) x)
                (ZpSeq.one p hp) 1 = 1 := by
  rw [neg_carry_at_1 p hp x, h]
  show (p - 0) / p = 1
  rw [Nat.sub_zero]
  exact div_self_pure p (Nat.lt_of_succ_lt hp)

/-- ★ When `x.digit_0 > 0`: `(p - x.digit_0) / p = 0`. -/
theorem neg_carry_at_1_when_nonzero (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h : (x.digits 0).val ≠ 0) :
    Zp.carry p (Zp.complement p (Nat.lt_of_succ_lt hp) x)
                (ZpSeq.one p hp) 1 = 0 := by
  rw [neg_carry_at_1 p hp x]
  have h_pos : 0 < (x.digits 0).val := Nat.pos_of_ne_zero h
  have h_psub_lt : p - (x.digits 0).val < p :=
    Nat.sub_lt (Nat.lt_of_succ_lt hp) h_pos
  exact Nat.div_eq_of_lt h_psub_lt

/-! ## §3 — Zp.neg digit-1 formula (case-split) -/

/-- ★ `Zp.neg` at digit-1 (case x.digit_0 = 0): result is
    `(p - x.digit_1) % p`. -/
theorem zp_neg_digit_one_when_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h : (x.digits 0).val = 0) :
    ((Zp.neg p hp x).digits 1).val = (p - (x.digits 1).val) % p := by
  show ((Zp.add p (Nat.lt_of_succ_lt hp)
            (Zp.complement p (Nat.lt_of_succ_lt hp) x)
            (ZpSeq.one p hp)).digits 1).val
        = (p - (x.digits 1).val) % p
  rw [Zp.add_digit_val p (Nat.lt_of_succ_lt hp) _ _ 1]
  rw [neg_carry_at_1_when_zero p hp x h]
  rw [Zp.complement_digit_val p (Nat.lt_of_succ_lt hp) x 1]
  -- ((one).digits 1).val = 0
  show (p - 1 - (x.digits 1).val + ((ZpSeq.one p hp).digits 1).val + 1) % p
       = (p - (x.digits 1).val) % p
  show (p - 1 - (x.digits 1).val + 0 + 1) % p
       = (p - (x.digits 1).val) % p
  rw [Nat.add_zero]
  -- Same p-1-a+1 = p-a manipulation
  have ha : (x.digits 1).val ≤ p - 1 :=
    Nat.le_sub_one_of_lt (x.digits 1).isLt
  have hfold : p - 1 - (x.digits 1).val + 1 = p - (x.digits 1).val := by
    have lhs_full : (p - 1 - (x.digits 1).val + 1) + (x.digits 1).val = p := by
      rw [Nat.add_assoc, Nat.add_comm 1 (x.digits 1).val]
      rw [← Nat.add_assoc]
      rw [E213.Tactic.NatHelper.sub_add_cancel ha]
      exact E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hp)
    have rhs_full : (p - (x.digits 1).val) + (x.digits 1).val = p :=
      E213.Tactic.NatHelper.sub_add_cancel
        (Nat.le_of_lt (x.digits 1).isLt)
    have h_eq : (p - 1 - (x.digits 1).val + 1) + (x.digits 1).val
              = (p - (x.digits 1).val) + (x.digits 1).val := by
      rw [lhs_full, rhs_full]
    exact add_right_cancel_pure h_eq
  rw [hfold]

/-- ★ `Zp.neg` at digit-1 (case x.digit_0 > 0): result is
    `(p - 1 - x.digit_1) % p`. -/
theorem zp_neg_digit_one_when_nonzero
    (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h : (x.digits 0).val ≠ 0) :
    ((Zp.neg p hp x).digits 1).val = (p - 1 - (x.digits 1).val) % p := by
  show ((Zp.add p (Nat.lt_of_succ_lt hp)
            (Zp.complement p (Nat.lt_of_succ_lt hp) x)
            (ZpSeq.one p hp)).digits 1).val
        = (p - 1 - (x.digits 1).val) % p
  rw [Zp.add_digit_val p (Nat.lt_of_succ_lt hp) _ _ 1]
  rw [neg_carry_at_1_when_nonzero p hp x h]
  rw [Zp.complement_digit_val p (Nat.lt_of_succ_lt hp) x 1]
  show (p - 1 - (x.digits 1).val + ((ZpSeq.one p hp).digits 1).val + 0) % p
       = (p - 1 - (x.digits 1).val) % p
  show (p - 1 - (x.digits 1).val + 0 + 0) % p
       = (p - 1 - (x.digits 1).val) % p
  rw [Nat.add_zero]


/-! ## §3.5 — Zp.neg digit-0 zero/nonzero discrimination -/

/-- Helper: when `x.digit_0 = 0`, `(Zp.neg x).digit_0 = 0`. -/
theorem zp_neg_digit_zero_when_zero
    (p : Nat) (hp : 1 < p) (x : ZpSeq p) (h : (x.digits 0).val = 0) :
    ((Zp.neg p hp x).digits 0).val = 0 := by
  rw [NegInvolution.zp_neg_digit_zero p hp x]
  rw [h]
  show (p - 0) % p = 0
  rw [Nat.sub_zero]
  exact E213.Meta.Nat.AddMod213.mod_self p

/-- Helper: when `x.digit_0 ≠ 0`, `(Zp.neg x).digit_0 = p - x.digit_0 ≠ 0`. -/
theorem zp_neg_digit_zero_when_nonzero_eq
    (p : Nat) (hp : 1 < p) (x : ZpSeq p) (h : (x.digits 0).val ≠ 0) :
    ((Zp.neg p hp x).digits 0).val = p - (x.digits 0).val := by
  rw [NegInvolution.zp_neg_digit_zero p hp x]
  have h_pos : 0 < (x.digits 0).val := Nat.pos_of_ne_zero h
  have h_psub_lt : p - (x.digits 0).val < p :=
    Nat.sub_lt (Nat.lt_of_succ_lt hp) h_pos
  exact Nat.mod_eq_of_lt h_psub_lt

/-! ## §3.6 — Zp.neg involution at digit-1 -/

/-- ★★★ **Zp.neg involution at digit-1** (case x.digit_0 = 0). -/
theorem zp_neg_neg_digit_one_when_zero
    (p : Nat) (hp : 1 < p) (x : ZpSeq p) (h : (x.digits 0).val = 0) :
    ((Zp.neg p hp (Zp.neg p hp x)).digits 1).val = (x.digits 1).val := by
  -- (Zp.neg x).digit_0 = 0 (helper)
  have h_inner_d0 : ((Zp.neg p hp x).digits 0).val = 0 :=
    zp_neg_digit_zero_when_zero p hp x h
  -- (Zp.neg (Zp.neg x)).digit_1 (case zero applies again)
  rw [zp_neg_digit_one_when_zero p hp (Zp.neg p hp x) h_inner_d0]
  -- = (p - (Zp.neg x).digit_1) % p
  rw [zp_neg_digit_one_when_zero p hp x h]
  -- = (p - (p - x.digit_1) % p) % p
  exact double_neg_mod_at p (x.digits 1).val (Nat.lt_of_succ_lt hp)
    (x.digits 1).isLt

/-- ★★★ **Zp.neg involution at digit-1** (case x.digit_0 ≠ 0). -/
theorem zp_neg_neg_digit_one_when_nonzero
    (p : Nat) (hp : 1 < p) (x : ZpSeq p) (h : (x.digits 0).val ≠ 0) :
    ((Zp.neg p hp (Zp.neg p hp x)).digits 1).val = (x.digits 1).val := by
  -- (Zp.neg x).digit_0 = p - x.digit_0 (helper)
  have h_inner_d0_val : ((Zp.neg p hp x).digits 0).val = p - (x.digits 0).val :=
    zp_neg_digit_zero_when_nonzero_eq p hp x h
  have h_pos : 0 < (x.digits 0).val := Nat.pos_of_ne_zero h
  have h_inner_d0_nonzero : ((Zp.neg p hp x).digits 0).val ≠ 0 := by
    rw [h_inner_d0_val]
    intro hp_sub_zero
    -- p - x.digit_0 = 0 ↔ p ≤ x.digit_0, but x.digit_0 < p
    have hp_le : p ≤ (x.digits 0).val := Nat.le_of_sub_eq_zero hp_sub_zero
    exact Nat.lt_irrefl p
      (Nat.lt_of_le_of_lt hp_le (x.digits 0).isLt)
  -- (Zp.neg (Zp.neg x)).digit_1 (case nonzero)
  rw [zp_neg_digit_one_when_nonzero p hp (Zp.neg p hp x) h_inner_d0_nonzero]
  -- = (p - 1 - (Zp.neg x).digit_1) % p
  rw [zp_neg_digit_one_when_nonzero p hp x h]
  -- = (p - 1 - ((p - 1 - x.digit_1) % p)) % p
  -- For x.digit_1 < p, p - 1 - x.digit_1 < p, so % p doesn't change it.
  have hb : (x.digits 1).val ≤ p - 1 :=
    Nat.le_sub_one_of_lt (x.digits 1).isLt
  have hpm1_sub_lt : p - 1 - (x.digits 1).val < p := by
    apply Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) _)
    exact Nat.sub_lt (Nat.lt_of_succ_lt hp) Nat.one_pos
  rw [Nat.mod_eq_of_lt hpm1_sub_lt]
  -- Now: (p - 1 - (p - 1 - x.digit_1)) % p = x.digit_1
  -- p - 1 - (p - 1 - a) = a for a ≤ p - 1
  have key : p - 1 - (p - 1 - (x.digits 1).val) = (x.digits 1).val := by
    -- Use add_right_cancel: (p-1 - (p-1-a)) + (p-1-a) = p-1
    -- And a + (p-1-a) = p-1
    have lhs : (p - 1 - (p - 1 - (x.digits 1).val))
                + (p - 1 - (x.digits 1).val) = p - 1 := by
      have h_sub_le : p - 1 - (x.digits 1).val ≤ p - 1 := Nat.sub_le _ _
      exact E213.Tactic.NatHelper.sub_add_cancel h_sub_le
    have rhs : (x.digits 1).val + (p - 1 - (x.digits 1).val) = p - 1 := by
      rw [Nat.add_comm]
      exact E213.Tactic.NatHelper.sub_add_cancel hb
    have h_eq : (p - 1 - (p - 1 - (x.digits 1).val))
                  + (p - 1 - (x.digits 1).val)
              = (x.digits 1).val + (p - 1 - (x.digits 1).val) := by
      rw [lhs, rhs]
    exact add_right_cancel_pure h_eq
  rw [key]
  exact Nat.mod_eq_of_lt (x.digits 1).isLt

/-! ## §4 — Capstone -/

/-- ★★★★★ **Zp.neg digit-1 carry-tracking capstone**.

    Bundles: (a) general carry-at-1 formula, (b) carry case-split
    (zero / nonzero digit-0), (c) Zp.neg digit-1 formula in both
    cases.

    This establishes the **per-digit involution rigor** one step
    past digit-0, demonstrating the carry-chain argument can be
    extended uniformly.  The full involution at all digits follows
    the same pattern with deeper carry tracking. -/
theorem zp_neg_digit_one_capstone
    (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    -- (a) General carry formula
    Zp.carry p (Zp.complement p (Nat.lt_of_succ_lt hp) x)
                (ZpSeq.one p hp) 1
      = (p - (x.digits 0).val) / p
    -- (b) Carry case-split
    ∧ ((x.digits 0).val = 0 →
        Zp.carry p (Zp.complement p (Nat.lt_of_succ_lt hp) x)
                    (ZpSeq.one p hp) 1 = 1)
    ∧ ((x.digits 0).val ≠ 0 →
        Zp.carry p (Zp.complement p (Nat.lt_of_succ_lt hp) x)
                    (ZpSeq.one p hp) 1 = 0)
    -- (c) Zp.neg digit-1 formula (case x.digit_0 = 0)
    ∧ ((x.digits 0).val = 0 →
        ((Zp.neg p hp x).digits 1).val = (p - (x.digits 1).val) % p)
    ∧ ((x.digits 0).val ≠ 0 →
        ((Zp.neg p hp x).digits 1).val
        = (p - 1 - (x.digits 1).val) % p)
    -- ★★★ (d) Involution at digit-1 (full, both cases)
    ∧ ((x.digits 0).val = 0 →
        ((Zp.neg p hp (Zp.neg p hp x)).digits 1).val = (x.digits 1).val)
    ∧ ((x.digits 0).val ≠ 0 →
        ((Zp.neg p hp (Zp.neg p hp x)).digits 1).val
        = (x.digits 1).val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact neg_carry_at_1 p hp x
  · exact neg_carry_at_1_when_zero p hp x
  · exact neg_carry_at_1_when_nonzero p hp x
  · exact zp_neg_digit_one_when_zero p hp x
  · exact zp_neg_digit_one_when_nonzero p hp x
  · exact zp_neg_neg_digit_one_when_zero p hp x
  · exact zp_neg_neg_digit_one_when_nonzero p hp x

end E213.Lib.Math.NumberSystems.Padic.NegInvolutionDigit1
