import E213.Lib.Math.Padic.Arith
import E213.Meta.Nat.AddMod213
/-!
# Zp.neg involution at digit-0 (rigor)

Establishes that `Zp.neg ∘ Zp.neg = id` **at digit-0**, modulo the
canonical `Fin p` representation.

The user's observation: forward and backward trajectories under
`Zp.neg` form two paths from `x` to itself (via `-x`).  Showing
they coincide pointwise per digit closes involution; the digit-0
case is pure mod-arithmetic, no carry chain.

  `((Zp.neg p hp x).digits 0).val = (p - (x.digits 0).val) % p`

then applying `Zp.neg` again:

  `((Zp.neg p hp (Zp.neg p hp x)).digits 0).val
    = (p - ((p - (x.digits 0).val) % p)) % p`

which reduces to `(x.digits 0).val` by the **double-mod-negation
identity** `(p - (p - r) % p) % p = r` for `r < p`.

Higher-digit involution requires carry-chain analysis (the `+ 1`
in `Zp.neg = complement + 1` propagates when `x.digit_0 = 0`).
This file delivers the digit-0 rigor; the trajectory pattern at
higher digits is a follow-up.

All declarations PURE.
-/

namespace E213.Lib.Math.Padic.NegInvolution

open E213.Meta.Nat.AddMod213 (mod_self)

/-! ## §0 — PURE Nat helpers (re-proved locally)

`Nat.sub_add_cancel` and `Nat.add_right_cancel` from Lean core leak
`propext`; we re-prove the needed forms by direct induction. -/

/-- PURE additive right-cancellation: `a + c = b + c → a = b`. -/
theorem add_right_cancel_pure : ∀ {a b c : Nat},
    a + c = b + c → a = b
  | a, b, 0, h => by
    show a = b
    have h1 : a + 0 = a := Nat.add_zero a
    have h2 : b + 0 = b := Nat.add_zero b
    rw [h1, h2] at h
    exact h
  | a, b, c + 1, h => by
    have h_succ : a + c + 1 = b + c + 1 := by
      show a + (c + 1) = b + (c + 1)
      exact h
    have hc : a + c = b + c := Nat.succ.inj h_succ
    exact add_right_cancel_pure hc

/-! ## §1 — Double-mod-negation helper (re-proved locally) -/

/-- `(p - (p - r) % p) % p = r` when `r < p`.  PURE.  Local copy
    of FP2Sqrt5's `double_neg_mod` (which is private). -/
theorem double_neg_mod_at (p r : Nat) (hp : 0 < p) (hr : r < p) :
    (p - (p - r) % p) % p = r := by
  by_cases h0 : r = 0
  · subst h0
    show (p - (p - 0) % p) % p = 0
    rw [Nat.sub_zero, mod_self, Nat.sub_zero, mod_self]
  · have h0_pos : 0 < r := Nat.pos_of_ne_zero h0
    have hpsub_lt : p - r < p := Nat.sub_lt hp h0_pos
    have h_psub_le : r ≤ p := Nat.le_of_lt hr
    rw [Nat.mod_eq_of_lt hpsub_lt]
    rw [E213.Tactic.NatHelper.sub_sub_self h_psub_le]
    rw [Nat.mod_eq_of_lt hr]

/-! ## §2 — Zp.neg digit-0 formula -/

/-- ★ **Zp.neg digit-0 formula**: `((Zp.neg p hp x).digits 0).val
    = (p - (x.digits 0).val) % p`.

    Derivation:
      Zp.neg x = Zp.add (complement x) ZpSeq.one
      ((Zp.neg x).digits 0).val
        = ((complement x).digits 0).val + (ZpSeq.one.digits 0).val
          + carry₀ % p
        = (p - 1 - (x.digits 0).val) + 1 + 0 % p
        = (p - (x.digits 0).val) % p. -/
theorem zp_neg_digit_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ((Zp.neg p hp x).digits 0).val = (p - (x.digits 0).val) % p := by
  -- Unfold Zp.neg = Zp.add (complement x) one
  show ((Zp.add p (Nat.lt_of_succ_lt hp)
            (Zp.complement p (Nat.lt_of_succ_lt hp) x)
            (ZpSeq.one p hp)).digits 0).val
        = (p - (x.digits 0).val) % p
  rw [Zp.add_digit_val p (Nat.lt_of_succ_lt hp) _ _ 0]
  rw [Zp.carry_zero p _ _, Nat.add_zero]
  rw [Zp.complement_digit_val p (Nat.lt_of_succ_lt hp) x 0]
  -- (one.digits 0).val = 1 (since 1 < p, 1 % p = 1)
  show (p - 1 - (x.digits 0).val
          + ((ZpSeq.one p hp).digits 0).val) % p
        = (p - (x.digits 0).val) % p
  show (p - 1 - (x.digits 0).val + 1) % p
        = (p - (x.digits 0).val) % p
  -- p - 1 - a + 1 = p - a  when a ≤ p - 1
  have ha : (x.digits 0).val ≤ p - 1 :=
    Nat.le_sub_one_of_lt (x.digits 0).isLt
  -- p - 1 - a + 1 = p - a  when a ≤ p - 1
  -- Strategy: show ((p - 1 - a) + 1) + a = p (LHS), and (p - a) + a = p (RHS),
  -- then cancel +a on the right.
  have hfold : p - 1 - (x.digits 0).val + 1 = p - (x.digits 0).val := by
    have lhs_full : (p - 1 - (x.digits 0).val + 1) + (x.digits 0).val = p := by
      -- = (p-1-a) + 1 + a = (p-1-a) + (a+1) [add_assoc + comm]
      rw [Nat.add_assoc, Nat.add_comm 1 (x.digits 0).val]
      rw [← Nat.add_assoc]
      rw [E213.Tactic.NatHelper.sub_add_cancel ha]
      exact E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hp)
    have rhs_full : (p - (x.digits 0).val) + (x.digits 0).val = p :=
      E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt (x.digits 0).isLt)
    -- (a + c = p) ∧ (b + c = p) → a = b via subtraction
    have h_eq : (p - 1 - (x.digits 0).val + 1) + (x.digits 0).val
              = (p - (x.digits 0).val) + (x.digits 0).val := by
      rw [lhs_full, rhs_full]
    -- cancel + a
    exact add_right_cancel_pure h_eq
  rw [hfold]

/-! ## §3 — Zp.neg involution at digit-0 -/

/-- ★★★ **Zp.neg involution at digit-0**: `((Zp.neg (Zp.neg x)).digits 0).val
    = (x.digits 0).val`.

    The two-trajectory pointwise identity at digit-0: `-(-x).digit_0
    = x.digit_0`. -/
theorem zp_neg_neg_digit_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ((Zp.neg p hp (Zp.neg p hp x)).digits 0).val = (x.digits 0).val := by
  -- Inner: ((Zp.neg x).digits 0).val = (p - (x.digits 0).val) % p
  rw [zp_neg_digit_zero p hp (Zp.neg p hp x)]
  -- Apply zp_neg_digit_zero again for the outer
  -- but we need to instead show via double_neg_mod_at
  -- (Zp.neg p hp x).digits 0).val = (p - (x.digits 0).val) % p, so
  -- (p - ((p - (x.digits 0).val) % p)) % p = (x.digits 0).val
  rw [zp_neg_digit_zero p hp x]
  -- Goal: (p - (p - (x.digits 0).val) % p) % p = (x.digits 0).val
  exact double_neg_mod_at p (x.digits 0).val (Nat.lt_of_succ_lt hp)
    (x.digits 0).isLt

/-! ## §4 — Smoke tests -/

/-- Smoke at p = 5, x.digits 0 = 2: `((Zp.neg 5 (Zp.neg 5 x)).digits 0).val = 2`.
    Calc: `Zp.neg 2 mod 5 = 5 - 2 = 3`, then `Zp.neg 3 mod 5 = 5 - 3 = 2`. -/
theorem zp_neg_neg_smoke_5_2 (rest : Nat → ZpDigit 5) :
    let x : ZpSeq 5 := ⟨fun k => if k = 0 then ⟨2, by decide⟩ else rest k⟩
    ((Zp.neg 5 (by decide) (Zp.neg 5 (by decide) x)).digits 0).val = 2 :=
  zp_neg_neg_digit_zero 5 (by decide) _

/-- Smoke at p = 7, x.digits 0 = 0: edge case (Zp.neg 0 → 0 with carry). -/
theorem zp_neg_neg_smoke_7_0 (rest : Nat → ZpDigit 7) :
    let x : ZpSeq 7 := ⟨fun k => if k = 0 then ⟨0, by decide⟩ else rest k⟩
    ((Zp.neg 7 (by decide) (Zp.neg 7 (by decide) x)).digits 0).val = 0 :=
  zp_neg_neg_digit_zero 7 (by decide) _

/-! ## §5 — Capstone -/

/-- ★★★★★ **Zp.neg involution digit-0 capstone**.

    Bundles: (a) Zp.neg digit-0 formula `(p - x.digit_0) % p`,
    (b) involution at digit-0 (the two-trajectory pointwise
    identity), (c) double-mod-negation arithmetic helper,
    (d) smoke at concrete (p, x.digit_0).

    Reading: the user's observation realised — forward and
    backward Zp.neg trajectories coincide at digit-0 by pure
    Nat-mod arithmetic.  Higher-digit involution requires carry
    chain analysis (follow-up). -/
theorem zp_neg_involution_digit_zero_capstone
    (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    -- (a) Digit-0 formula
    ((Zp.neg p hp x).digits 0).val = (p - (x.digits 0).val) % p
    -- (b) Involution at digit-0
    ∧ ((Zp.neg p hp (Zp.neg p hp x)).digits 0).val = (x.digits 0).val
    -- (c) Helper: double-mod-negation
    ∧ (p - (p - (x.digits 0).val) % p) % p = (x.digits 0).val := by
  refine ⟨?_, ?_, ?_⟩
  · exact zp_neg_digit_zero p hp x
  · exact zp_neg_neg_digit_zero p hp x
  · exact double_neg_mod_at p (x.digits 0).val (Nat.lt_of_succ_lt hp)
      (x.digits 0).isLt

end E213.Lib.Math.Padic.NegInvolution
