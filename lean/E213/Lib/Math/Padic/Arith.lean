import E213.Lib.Math.Padic.Foundation
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
/-!
# Real213-p-adic Arithmetic

Digit-by-digit p-adic operations on `ZpSeq p`:
addition (with carry propagation), negation (via `neg_one + complement`),
and multiplication (digit-distributive).

All definitions PURE.  Reuses the PURE modular-arithmetic substrate
from `E213.Meta.Nat.AddMod213` / `MulMod213`.
-/

namespace E213.Lib.Math.Padic

/-! ## Addition with carry propagation

For p-adic addition `(x + y) : ZpSeq p`, the digit at position `k`
is `((x.digits k).val + (y.digits k).val + carry k) % p`,
where `carry k` is the carry into position `k`:

  carry 0 = 0
  carry (k+1) = ((x.digits k).val + (y.digits k).val + carry k) / p

Both `carry` and `add` are total functions on `ZpSeq p`,
giving a PURE p-adic addition.
-/

/-- The carry into digit position `k` when adding `x + y`. -/
def Zp.carry (p : Nat) (x y : ZpSeq p) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) / p

/-- p-adic addition `x + y` (digit-by-digit with carry). -/
def Zp.add (p : Nat) (hp : 0 < p) (x y : ZpSeq p) : ZpSeq p where
  digits := fun k =>
    ⟨((x.digits k).val + (y.digits k).val + Zp.carry p x y k) % p,
     Nat.mod_lt _ hp⟩

/-- Initial carry is 0 by definition. -/
theorem Zp.carry_zero (p : Nat) (x y : ZpSeq p) :
    Zp.carry p x y 0 = 0 := rfl

/-- Step rule for carry. -/
theorem Zp.carry_succ (p : Nat) (x y : ZpSeq p) (k : Nat) :
    Zp.carry p x y (k+1)
      = ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) / p := rfl

/-- Digit unfolding for `Zp.add`. -/
theorem Zp.add_digit_val (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (k : Nat) :
    ((Zp.add p hp x y).digits k).val
      = ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) % p := rfl

/-! ## Truncation correctness: addition reduces mod `p^n`

The structural identity:

  x.trunc n + y.trunc n = (Zp.add x y).trunc n + carry n · p^n

— sum-of-truncations equals truncation-of-sum plus the carry-out
in the position `p^n`.  Direct induction on `n`.

From this, `(Zp.add x y).trunc n = (x.trunc n + y.trunc n) % p^n`
follows by reducing both sides mod `p^n` (carry term is a multiple
of `p^n`, so it vanishes; both truncations sit in `[0, p^n)`).
-/

/-- Rearrangement helper: `(a + bp) + (c + dp) = (a + c) + (b + d) · pn`. -/
private theorem swap_distrib (a b c d pn : Nat) :
    (a + b * pn) + (c + d * pn) = (a + c) + (b + d) * pn :=
  calc (a + b * pn) + (c + d * pn)
      = a + (b * pn + (c + d * pn)) := Nat.add_assoc a (b * pn) (c + d * pn)
    _ = a + ((b * pn + c) + d * pn) := by rw [Nat.add_assoc]
    _ = a + ((c + b * pn) + d * pn) := by rw [Nat.add_comm (b * pn) c]
    _ = a + (c + (b * pn + d * pn)) := by
          rw [Nat.add_assoc c (b * pn) (d * pn)]
    _ = (a + c) + (b * pn + d * pn) := (Nat.add_assoc a c _).symm
    _ = (a + c) + (b + d) * pn := by
          rw [← E213.Tactic.NatHelper.add_mul]

/-- Split a sum `s · p^n` into `(s % p) · p^n + (s / p) · p^(n+1)`,
    using `div_add_mod`.  Pure arithmetic rearrangement. -/
private theorem split_mul_pow (s p pn : Nat) :
    s * pn = (s % p) * pn + (s / p) * (pn * p) := by
  have hdm := E213.Meta.Nat.AddMod213.div_add_mod s p
  rw [Nat.mul_comm p (s/p)] at hdm
  rw [Nat.add_comm ((s/p) * p) (s % p)] at hdm
  -- hdm : s % p + (s/p) * p = s
  calc s * pn
      = ((s % p) + (s / p) * p) * pn := by rw [hdm]
    _ = (s % p) * pn + (s / p) * p * pn :=
            E213.Tactic.NatHelper.add_mul (s % p) ((s/p) * p) pn
    _ = (s % p) * pn + (s / p) * (pn * p) := by
            rw [E213.Tactic.NatHelper.mul_assoc (s/p) p pn, Nat.mul_comm p pn,
                ← E213.Tactic.NatHelper.mul_assoc (s/p) pn p]

/-- Structural identity: sum-of-truncations = truncation-of-sum
    + carry · `p^n`. -/
theorem Zp.add_trunc_eq (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    ∀ n, x.trunc n + y.trunc n
          = (Zp.add p hp x y).trunc n + Zp.carry p x y n * p^n
  | 0 => by show (0 : Nat) + 0 = 0 + 0 * p^0; rfl
  | n + 1 => by
    have ih : x.trunc n + y.trunc n
              = (Zp.add p hp x y).trunc n + Zp.carry p x y n * p^n :=
      Zp.add_trunc_eq p hp x y n
    -- Let s = (x.digits n).val + (y.digits n).val + Zp.carry p x y n.
    -- Key facts (definitional):
    --   ((Zp.add).digits n).val = s % p
    --   Zp.carry x y (n+1)     = s / p
    -- Step 1: combine LHS into (x.trunc n + y.trunc n) + (dx + dy) * p^n.
    -- Step 2: apply IH and combine carry term to get
    --         (Zp.add).trunc n + (dx + dy + carry n) * p^n
    --       = (Zp.add).trunc n + s * p^n.
    -- Step 3: split s * p^n via `split_mul_pow` to match RHS.
    have hpow : p^(n+1) = p^n * p := Nat.pow_succ p n
    calc (x.trunc n + (x.digits n).val * p^n)
            + (y.trunc n + (y.digits n).val * p^n)
        = (x.trunc n + y.trunc n)
            + ((x.digits n).val + (y.digits n).val) * p^n :=
              swap_distrib (x.trunc n) (x.digits n).val
                (y.trunc n) (y.digits n).val (p^n)
      _ = ((Zp.add p hp x y).trunc n + Zp.carry p x y n * p^n)
            + ((x.digits n).val + (y.digits n).val) * p^n := by rw [ih]
      _ = (Zp.add p hp x y).trunc n
            + (Zp.carry p x y n
                + ((x.digits n).val + (y.digits n).val)) * p^n := by
              rw [Nat.add_assoc, ← E213.Tactic.NatHelper.add_mul]
      _ = (Zp.add p hp x y).trunc n
            + ((x.digits n).val + (y.digits n).val
                + Zp.carry p x y n) * p^n := by
              rw [Nat.add_comm (Zp.carry p x y n)
                    ((x.digits n).val + (y.digits n).val)]
      _ = (Zp.add p hp x y).trunc n
            + (((x.digits n).val + (y.digits n).val
                  + Zp.carry p x y n) % p * p^n
                + ((x.digits n).val + (y.digits n).val
                      + Zp.carry p x y n) / p * (p^n * p)) := by
              rw [split_mul_pow]
      _ = ((Zp.add p hp x y).trunc n
            + ((x.digits n).val + (y.digits n).val
                + Zp.carry p x y n) % p * p^n)
          + ((x.digits n).val + (y.digits n).val
                + Zp.carry p x y n) / p * (p^n * p) :=
            (Nat.add_assoc _ _ _).symm
      _ = ((Zp.add p hp x y).trunc n
            + ((x.digits n).val + (y.digits n).val
                + Zp.carry p x y n) % p * p^n)
          + ((x.digits n).val + (y.digits n).val
                + Zp.carry p x y n) / p * p^(n+1) := by rw [hpow]

/-- Reducing both sides mod `p^n` (the carry term vanishes; both
    truncations sit in `[0, p^n)`).  The natural ring-quotient
    statement: `(x + y) mod p^n = (x mod p^n) + (y mod p^n)` after
    reducing the sum mod `p^n`.

    Truncation is the canonical `ZpSeq p → ℤ/p^n` projection;
    this theorem says addition descends to that quotient. -/
theorem Zp.add_trunc (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (n : Nat) :
    (Zp.add p hp x y).trunc n = (x.trunc n + y.trunc n) % p^n := by
  have heq : x.trunc n + y.trunc n
              = (Zp.add p hp x y).trunc n + Zp.carry p x y n * p^n :=
    Zp.add_trunc_eq p hp x y n
  have hlt : (Zp.add p hp x y).trunc n < p^n :=
    ZpSeq.trunc_lt_p_pow hp (Zp.add p hp x y) n
  -- (x.trunc n + y.trunc n) % p^n
  --   = ((Zp.add x y).trunc n + carry n * p^n) % p^n   [by heq]
  --   = (Zp.add x y).trunc n % p^n                       [add_mul_mod_self_pure]
  --   = (Zp.add x y).trunc n                              [mod_eq_of_lt]
  calc (Zp.add p hp x y).trunc n
      = (Zp.add p hp x y).trunc n % p^n := (Nat.mod_eq_of_lt hlt).symm
    _ = ((Zp.add p hp x y).trunc n + Zp.carry p x y n * p^n) % p^n := by
          rw [E213.Tactic.NatHelper.add_mul_mod_self_pure]
    _ = (x.trunc n + y.trunc n) % p^n := by rw [← heq]

/-! ## Per-prime smokes for addition -/

-- 0 + 0 = 0 in ℤ_p, trunc level 3.
theorem Zp.smoke_add_zero_zero_2 :
    (Zp.add 2 (by decide)
      (ZpSeq.zero 2 (by decide)) (ZpSeq.zero 2 (by decide))).trunc 3 = 0 := by
  rw [Zp.add_trunc, ZpSeq.trunc_zero]

theorem Zp.smoke_add_zero_one_5 :
    (Zp.add 5 (by decide)
      (ZpSeq.zero 5 (by decide)) (ZpSeq.one 5 (by decide))).trunc 1 = 1 := by
  rw [Zp.add_trunc, ZpSeq.trunc_zero, ZpSeq.trunc_one_at_one]

/-! ## Digit-complement and negation

For each digit `d ∈ {0, …, p-1}`, the complement is `p-1-d`.  At
the sequence level, `complement x` has digit-k equal to `p-1 -
(x.digits k).val`.  Then `x + (complement x) = neg_one` (all-(p-1)
sequence, no carries), and `neg x := complement x + one` gives the
p-adic negation: `x + neg x = neg_one + one = 0` in ℤ_p (since
adding 1 to all-(p-1) cascades carry through all positions,
yielding all-zero).
-/

/-- Digit complement: `p - 1 - d`. -/
def Zp.complement (p : Nat) (hp : 0 < p) (x : ZpSeq p) : ZpSeq p where
  digits := fun k =>
    ⟨p - 1 - (x.digits k).val,
     Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hp Nat.one_pos)⟩

/-- p-adic negation `-x := complement x + 1`. -/
def Zp.neg (p : Nat) (hp : 1 < p) (x : ZpSeq p) : ZpSeq p :=
  Zp.add p (Nat.lt_of_succ_lt hp) (Zp.complement p (Nat.lt_of_succ_lt hp) x)
    (ZpSeq.one p hp)

/-- Digit value of `complement`: by `rfl`. -/
theorem Zp.complement_digit_val (p : Nat) (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.complement p hp x).digits k).val = p - 1 - (x.digits k).val := rfl

/-- The carry stays at `0` for the `x + complement x` sum, because
    each digit-pair sums to `p - 1 < p`. -/
theorem Zp.carry_x_complement (p : Nat) (hp : 0 < p) (x : ZpSeq p) :
    ∀ k, Zp.carry p x (Zp.complement p hp x) k = 0
  | 0 => rfl
  | k + 1 => by
    show ((x.digits k).val + ((Zp.complement p hp x).digits k).val
            + Zp.carry p x (Zp.complement p hp x) k) / p = 0
    rw [Zp.carry_x_complement p hp x k, Nat.add_zero]
    show ((x.digits k).val + (p - 1 - (x.digits k).val)) / p = 0
    have hle : (x.digits k).val ≤ p - 1 :=
      Nat.le_sub_one_of_lt (x.digits k).isLt
    -- a + (p-1 - a) = p-1 when a ≤ p-1.
    have hcancel : (x.digits k).val + (p - 1 - (x.digits k).val) = p - 1 := by
      rw [Nat.add_comm]; exact E213.Tactic.NatHelper.sub_add_cancel hle
    rw [hcancel]
    -- (p-1) / p = 0 when p > 0.
    exact Nat.div_eq_of_lt (Nat.sub_lt hp Nat.one_pos)

/-- `(x + complement x)` digit-k value is `p - 1`.  No carries
    propagate because each digit-pair sums to `p - 1 < p`. -/
theorem Zp.add_complement_digit (p : Nat) (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.add p hp x (Zp.complement p hp x)).digits k).val = p - 1 := by
  show ((x.digits k).val + ((Zp.complement p hp x).digits k).val
          + Zp.carry p x (Zp.complement p hp x) k) % p = p - 1
  rw [Zp.carry_x_complement p hp x k, Nat.add_zero]
  show ((x.digits k).val + (p - 1 - (x.digits k).val)) % p = p - 1
  have hle : (x.digits k).val ≤ p - 1 :=
    Nat.le_sub_one_of_lt (x.digits k).isLt
  have hcancel : (x.digits k).val + (p - 1 - (x.digits k).val) = p - 1 := by
    rw [Nat.add_comm]; exact E213.Tactic.NatHelper.sub_add_cancel hle
  rw [hcancel]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hp Nat.one_pos)

/-- Smoke: `Zp.neg 5 (one) = neg_one` at digit 0. -/
theorem Zp.smoke_neg_one_5_d0 :
    ((Zp.neg 5 (by decide) (ZpSeq.one 5 (by decide))).digits 0).val = 4 := rfl

/-! ## Multiplication (digit convolution + carry)

p-adic multiplication is a convolution-with-carry:
  · The "raw" sum at position `k` is `Σ_{i=0..k} (x.digits i) · (y.digits (k-i))`.
  · The carry into position `k+1` is `(rawSum k + carry k) / p`.
  · The digit at position `k` is `(rawSum k + carry k) % p`.

The truncation-correctness theorem (`(Zp.mul x y).trunc n
= (x.trunc n * y.trunc n) % p^n`) is structurally analogous to
`Zp.add_trunc` but requires more bookkeeping for the convolution.
We provide the PURE definitions here; the correctness theorem
is the natural next step.
-/

/-- Inner partial sum: `Σ_{i=0..upper-1} (x.digits i).val · (y.digits (k-i)).val`. -/
def Zp.mulRawSum (p : Nat) (x y : ZpSeq p) (k : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      Zp.mulRawSum p x y k i + (x.digits i).val * (y.digits (k - i)).val

/-- Raw convolution at position `k`: `Σ_{i=0..k} (x.digits i).val · (y.digits (k-i)).val`. -/
def Zp.mulRaw (p : Nat) (x y : ZpSeq p) (k : Nat) : Nat :=
  Zp.mulRawSum p x y k (k + 1)

/-- The carry into digit position `k` when multiplying `x * y`. -/
def Zp.mulCarry (p : Nat) (x y : ZpSeq p) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      (Zp.mulRaw p x y k + Zp.mulCarry p x y k) / p

/-- p-adic multiplication `x * y`. -/
def Zp.mul (p : Nat) (hp : 0 < p) (x y : ZpSeq p) : ZpSeq p where
  digits := fun k =>
    ⟨(Zp.mulRaw p x y k + Zp.mulCarry p x y k) % p, Nat.mod_lt _ hp⟩

/-- Initial carry of `mul` is 0 by definition. -/
theorem Zp.mulCarry_zero (p : Nat) (x y : ZpSeq p) :
    Zp.mulCarry p x y 0 = 0 := rfl

/-- Step rule for `mulCarry`. -/
theorem Zp.mulCarry_succ (p : Nat) (x y : ZpSeq p) (k : Nat) :
    Zp.mulCarry p x y (k+1)
      = (Zp.mulRaw p x y k + Zp.mulCarry p x y k) / p := rfl

/-- Digit unfolding for `Zp.mul`. -/
theorem Zp.mul_digit_val (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (k : Nat) :
    ((Zp.mul p hp x y).digits k).val
      = (Zp.mulRaw p x y k + Zp.mulCarry p x y k) % p := rfl

/-- Multiplying by zero on the right: every partial sum vanishes. -/
theorem Zp.mulRawSum_zero_right {p : Nat} (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ∀ upper, Zp.mulRawSum p x (ZpSeq.zero p hp) k upper = 0
  | 0 => rfl
  | i + 1 => by
    show Zp.mulRawSum p x (ZpSeq.zero p hp) k i
          + (x.digits i).val * ((ZpSeq.zero p hp).digits (k - i)).val = 0
    rw [Zp.mulRawSum_zero_right hp x k i]
    show (0 : Nat) + (x.digits i).val * 0 = 0
    rw [Nat.mul_zero, Nat.zero_add]

/-- Raw convolution with zero is zero. -/
theorem Zp.mulRaw_zero_right (p : Nat) (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    Zp.mulRaw p x (ZpSeq.zero p hp) k = 0 :=
  Zp.mulRawSum_zero_right hp x k (k+1)

/-- Carry from zero multiplication stays at zero. -/
theorem Zp.mulCarry_zero_right (p : Nat) (hp : 0 < p) (x : ZpSeq p) :
    ∀ k, Zp.mulCarry p x (ZpSeq.zero p hp) k = 0
  | 0 => rfl
  | k + 1 => by
    show (Zp.mulRaw p x (ZpSeq.zero p hp) k
            + Zp.mulCarry p x (ZpSeq.zero p hp) k) / p = 0
    rw [Zp.mulRaw_zero_right p hp x k, Zp.mulCarry_zero_right p hp x k]
    show (0 + 0) / p = 0
    rw [Nat.zero_add, Nat.zero_div]

/-- `x · 0 = 0` (digit level): every digit of the product is zero. -/
theorem Zp.mul_zero_right_digit (p : Nat) (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.mul p hp x (ZpSeq.zero p hp)).digits k).val = 0 := by
  show (Zp.mulRaw p x (ZpSeq.zero p hp) k
          + Zp.mulCarry p x (ZpSeq.zero p hp) k) % p = 0
  rw [Zp.mulRaw_zero_right p hp x k, Zp.mulCarry_zero_right p hp x k]
  show (0 + 0) % p = 0
  rw [Nat.zero_add]
  exact E213.Tactic.NatHelper.zero_mod p

/-! ## Multiplication by one (`x · 1 = x`)

For `y = ZpSeq.one`, the digit `y.digits j` is `1` at `j = 0`
and `0` elsewhere.  Hence the convolution `Σ x.digits i · y.digits (k-i)`
collapses to a single nonzero term at `i = k`: the sum is
`(x.digits k).val`.  The carry stays at zero because each
`mulRaw k = (x.digits k).val < p`.  So digit `k` of `x · one` is
`(x.digits k).val % p = (x.digits k).val`.
-/

/-- `(one).digits k` value: `1` if `k = 0`, else `0`. -/
theorem Zp.one_digit_val {p : Nat} (hp : 1 < p) (k : Nat) :
    ((ZpSeq.one p hp).digits k).val = if k = 0 then 1 else 0 := by
  show (if k = 0 then (⟨1, hp⟩ : Fin p) else ⟨0, _⟩).val
        = if k = 0 then 1 else 0
  cases hk : decide (k = 0) with
  | true =>
    have hk' : k = 0 := of_decide_eq_true hk
    rw [if_pos hk', if_pos hk']
  | false =>
    have hk' : ¬ (k = 0) := of_decide_eq_false hk
    rw [if_neg hk', if_neg hk']

/-- For `upper ≤ k`, the partial convolution with `one` vanishes
    because every term has `(one.digits (k - i)).val = 0` (since
    `k - i ≥ 1` when `i < upper ≤ k`). -/
theorem Zp.mulRawSum_one_right_le {p : Nat} (hp : 1 < p) (x : ZpSeq p)
    (k : Nat) :
    ∀ upper, upper ≤ k → Zp.mulRawSum p x (ZpSeq.one p hp) k upper = 0
  | 0, _ => rfl
  | i + 1, hi => by
    show Zp.mulRawSum p x (ZpSeq.one p hp) k i
          + (x.digits i).val * ((ZpSeq.one p hp).digits (k - i)).val = 0
    have hi' : i ≤ k := Nat.le_of_lt (Nat.lt_of_succ_le hi)
    rw [Zp.mulRawSum_one_right_le hp x k i hi']
    show (0 : Nat) + (x.digits i).val * ((ZpSeq.one p hp).digits (k - i)).val = 0
    have hpos : 0 < k - i :=
      E213.Tactic.NatHelper.sub_pos_of_lt (Nat.lt_of_succ_le hi)
    have hne : k - i ≠ 0 := Nat.ne_of_gt hpos
    rw [Zp.one_digit_val hp (k - i), if_neg hne]
    rw [Nat.mul_zero, Nat.add_zero]

/-- `mulRaw x one k = (x.digits k).val`.  The convolution collapses
    to its single nonzero term at `i = k`. -/
theorem Zp.mulRaw_one_right {p : Nat} (hp : 1 < p) (x : ZpSeq p) (k : Nat) :
    Zp.mulRaw p x (ZpSeq.one p hp) k = (x.digits k).val := by
  show Zp.mulRawSum p x (ZpSeq.one p hp) k (k + 1) = (x.digits k).val
  show Zp.mulRawSum p x (ZpSeq.one p hp) k k
          + (x.digits k).val * ((ZpSeq.one p hp).digits (k - k)).val
        = (x.digits k).val
  rw [Zp.mulRawSum_one_right_le hp x k k (Nat.le_refl k)]
  rw [Nat.sub_self, Zp.one_digit_val hp 0]
  show (0 : Nat) + (x.digits k).val * (if (0 : Nat) = 0 then 1 else 0)
        = (x.digits k).val
  rw [if_pos rfl, Nat.mul_one, Nat.zero_add]

/-- Carry stays at zero when multiplying by `one` because each
    `mulRaw k = (x.digits k).val < p`, so `mulRaw k / p = 0`. -/
theorem Zp.mulCarry_one_right {p : Nat} (hp : 1 < p) (x : ZpSeq p) :
    ∀ k, Zp.mulCarry p x (ZpSeq.one p hp) k = 0
  | 0 => rfl
  | k + 1 => by
    show (Zp.mulRaw p x (ZpSeq.one p hp) k
            + Zp.mulCarry p x (ZpSeq.one p hp) k) / p = 0
    rw [Zp.mulRaw_one_right hp x k, Zp.mulCarry_one_right hp x k,
        Nat.add_zero]
    exact Nat.div_eq_of_lt (x.digits k).isLt

/-- `x · 1 = x` (digit level): every digit of the product equals
    the corresponding digit of `x`. -/
theorem Zp.mul_one_right_digit {p : Nat} (hp : 1 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).digits k).val
      = (x.digits k).val := by
  show (Zp.mulRaw p x (ZpSeq.one p hp) k
          + Zp.mulCarry p x (ZpSeq.one p hp) k) % p
        = (x.digits k).val
  rw [Zp.mulRaw_one_right hp x k, Zp.mulCarry_one_right hp x k, Nat.add_zero]
  exact Nat.mod_eq_of_lt (x.digits k).isLt

end E213.Lib.Math.Padic
