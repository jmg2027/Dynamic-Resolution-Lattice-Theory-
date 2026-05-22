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

/-- Inner-swap rearrangement: `(a + b) + (c + d) = (a + c) + (b + d)`. -/
private theorem swap_inner (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d,
      Nat.add_comm b c, Nat.add_assoc c b d,
      ← Nat.add_assoc a c (b + d)]

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

/-- PURE replacement for `Nat.pow_add` (which leaks propext): by
    induction on the second exponent. -/
private theorem pow_add_pure (a : Nat) :
    ∀ m n, a^(m + n) = a^m * a^n
  | _, 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | m, n + 1 => by
    rw [← Nat.add_assoc, Nat.pow_succ, Nat.pow_succ, pow_add_pure a m n]
    exact E213.Tactic.NatHelper.mul_assoc (a^m) (a^n) a

/-- Split a sum `s · p^n` into `(s % p) · p^n + (s / p) · p^(n+1)`,
    using `div_add_mod`.  Pure arithmetic rearrangement. -/
theorem Zp.split_mul_pow (s p pn : Nat) :
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
              rw [Zp.split_mul_pow]
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

/-! ## Additive identity and commutativity (digit level) -/

/-- Carry from `x + 0` stays at zero (each digit sum `x + 0 + 0 < p`). -/
theorem Zp.carry_x_zero_right (p : Nat) (hp : 0 < p) (x : ZpSeq p) :
    ∀ k, Zp.carry p x (ZpSeq.zero p hp) k = 0
  | 0 => rfl
  | k + 1 => by
    show ((x.digits k).val + ((ZpSeq.zero p hp).digits k).val
            + Zp.carry p x (ZpSeq.zero p hp) k) / p = 0
    rw [Zp.carry_x_zero_right p hp x k]
    show (x.digits k).val / p = 0
    exact Nat.div_eq_of_lt (x.digits k).isLt

/-- `x + 0 = x` (digit level). -/
theorem Zp.add_zero_right_digit (p : Nat) (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.add p hp x (ZpSeq.zero p hp)).digits k).val = (x.digits k).val := by
  show ((x.digits k).val + ((ZpSeq.zero p hp).digits k).val
          + Zp.carry p x (ZpSeq.zero p hp) k) % p = (x.digits k).val
  rw [Zp.carry_x_zero_right p hp x k]
  show (x.digits k).val % p = (x.digits k).val
  exact Nat.mod_eq_of_lt (x.digits k).isLt

/-- Carry is symmetric in `x` and `y` (since digit-sums are commutative). -/
theorem Zp.carry_comm (p : Nat) (x y : ZpSeq p) :
    ∀ k, Zp.carry p x y k = Zp.carry p y x k
  | 0 => rfl
  | k + 1 => by
    show ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) / p
          = ((y.digits k).val + (x.digits k).val + Zp.carry p y x k) / p
    rw [Zp.carry_comm p x y k]
    rw [Nat.add_comm (x.digits k).val (y.digits k).val]

/-- Commutativity of `Zp.add` at the digit level: `(x + y).digits k =
    (y + x).digits k`. -/
theorem Zp.add_comm_digit (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (k : Nat) :
    ((Zp.add p hp x y).digits k).val = ((Zp.add p hp y x).digits k).val := by
  show ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) % p
        = ((y.digits k).val + (x.digits k).val + Zp.carry p y x k) % p
  rw [Zp.carry_comm p x y k]
  rw [Nat.add_comm (x.digits k).val (y.digits k).val]

/-- `0 + x = x` (digit level): follows from `add_zero_right_digit`
    via `add_comm_digit`. -/
theorem Zp.add_zero_left_digit (p : Nat) (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.add p hp (ZpSeq.zero p hp) x).digits k).val = (x.digits k).val := by
  rw [Zp.add_comm_digit p hp (ZpSeq.zero p hp) x k]
  exact Zp.add_zero_right_digit p hp x k

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

/-- `(neg_one + one).trunc (n+1) = 0` — additive cancellation at
    the truncation level for `n ≥ 1`.  Derivation:
        `((neg_one).trunc (n+1) + (one).trunc (n+1)) % p^(n+1)`
        `= ((p^(n+1) - 1) + 1) % p^(n+1)`
        `= p^(n+1) % p^(n+1) = 0`.
    Uses `add_trunc` + `trunc_neg_one_succ` + `trunc_one_succ`. -/
theorem Zp.add_neg_one_one_trunc_succ (p : Nat) (hp : 1 < p) (n : Nat) :
    (Zp.add p (Nat.lt_of_succ_lt hp)
      (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)) (ZpSeq.one p hp)).trunc (n+1)
        = 0 := by
  rw [Zp.add_trunc, ZpSeq.trunc_one_succ p hp n,
      ZpSeq.trunc_neg_one_succ p (Nat.lt_of_succ_lt hp) (n+1)]
  exact E213.Meta.Nat.AddMod213.mod_self _

/-! ## Digit shift on `ZpSeq` (multiplication by `p^k`)

`Zp.shiftLeft k x` pushes `x`'s digits `k` positions higher,
filling the low `k` positions with zero.  Value-wise this
multiplies by `p^k`: `(Zp.shiftLeft k x).digits j` is
`x.digits (j - k)` when `j ≥ k`, else `0`.

This enables ℚ_p addition with unequal shifts (align via shift).
-/

/-- Shift `x`'s digits left by `k` positions. -/
def Zp.shiftLeft (p : Nat) (hp : 0 < p) (k : Nat) (x : ZpSeq p) : ZpSeq p where
  digits := fun j =>
    if j < k then (⟨0, hp⟩ : Fin p) else x.digits (j - k)

/-- Shifting by 0 is the identity (digit-by-digit). -/
theorem Zp.shiftLeft_zero_digit (p : Nat) (hp : 0 < p) (x : ZpSeq p) (j : Nat) :
    ((Zp.shiftLeft p hp 0 x).digits j) = x.digits j := by
  show (if j < 0 then (⟨0, hp⟩ : Fin p) else x.digits (j - 0))
        = x.digits j
  rw [if_neg (Nat.not_lt_zero j), Nat.sub_zero]

/-- Shifting `zero` is still zero (digit-by-digit). -/
theorem Zp.shiftLeft_zero_seq_digit (p : Nat) (hp : 0 < p) (k j : Nat) :
    ((Zp.shiftLeft p hp k (ZpSeq.zero p hp)).digits j).val = 0 := by
  show (if j < k then (⟨0, hp⟩ : Fin p) else (ZpSeq.zero p hp).digits (j - k)).val
        = 0
  cases hjk : decide (j < k) with
  | true =>
    have hjk' : j < k := of_decide_eq_true hjk
    rw [if_pos hjk']
  | false =>
    have hjk' : ¬ (j < k) := of_decide_eq_false hjk
    rw [if_neg hjk']
    rfl

/-- Below the shift threshold, the digit is zero. -/
theorem Zp.shiftLeft_digit_low (p : Nat) (hp : 0 < p) (k : Nat) (x : ZpSeq p)
    (j : Nat) (h : j < k) :
    ((Zp.shiftLeft p hp k x).digits j).val = 0 := by
  show (if j < k then (⟨0, hp⟩ : Fin p) else x.digits (j - k)).val = 0
  rw [if_pos h]

/-- `(Zp.shiftLeft k x).trunc m = 0` for any `m ≤ k`.  The shifted
    sequence's low `k` digits are all zero, so any truncation below
    that threshold vanishes. -/
theorem Zp.shiftLeft_trunc_below (p : Nat) (hp : 0 < p) (k : Nat) (x : ZpSeq p) :
    ∀ m, m ≤ k → (Zp.shiftLeft p hp k x).trunc m = 0
  | 0, _ => rfl
  | m + 1, hm => by
    have hmk : m < k := Nat.lt_of_succ_le hm
    have hmle : m ≤ k := Nat.le_of_lt hmk
    show (Zp.shiftLeft p hp k x).trunc m
          + ((Zp.shiftLeft p hp k x).digits m).val * p^m = 0
    rw [Zp.shiftLeft_trunc_below p hp k x m hmle,
        Zp.shiftLeft_digit_low p hp k x m hmk,
        Nat.zero_mul, Nat.zero_add]

/-- Above the shift threshold, the digit matches the original
    (with the index shifted): `(shiftLeft k x).digits (k + j) =
    x.digits j`. -/
theorem Zp.shiftLeft_digit_high (p : Nat) (hp : 0 < p) (k : Nat)
    (x : ZpSeq p) (j : Nat) :
    ((Zp.shiftLeft p hp k x).digits (k + j)).val = (x.digits j).val := by
  show (if k + j < k then (⟨0, hp⟩ : Fin p) else x.digits (k + j - k)).val
        = (x.digits j).val
  have hne : ¬ (k + j < k) :=
    fun h => Nat.lt_irrefl k (Nat.lt_of_le_of_lt (Nat.le_add_right k j) h)
  rw [if_neg hne]
  show (x.digits (k + j - k)).val = (x.digits j).val
  rw [Nat.add_comm k j]
  show (x.digits (j + k - k)).val = (x.digits j).val
  rw [E213.Tactic.NatHelper.add_sub_cancel_right]

/-- Truncation above the shift threshold: `(Zp.shiftLeft k x).trunc (k + n)
    = p^k · x.trunc n`.  The shift acts as multiplication by `p^k`. -/
theorem Zp.shiftLeft_trunc_above (p : Nat) (hp : 0 < p) (k : Nat) (x : ZpSeq p) :
    ∀ n, (Zp.shiftLeft p hp k x).trunc (k + n) = p^k * x.trunc n
  | 0 => by
    show (Zp.shiftLeft p hp k x).trunc (k + 0) = p^k * 0
    rw [Nat.add_zero, Nat.mul_zero]
    exact Zp.shiftLeft_trunc_below p hp k x k (Nat.le_refl k)
  | n + 1 => by
    have ih : (Zp.shiftLeft p hp k x).trunc (k + n) = p^k * x.trunc n :=
      Zp.shiftLeft_trunc_above p hp k x n
    show (Zp.shiftLeft p hp k x).trunc (k + n)
          + ((Zp.shiftLeft p hp k x).digits (k + n)).val * p^(k + n)
        = p^k * (x.trunc n + (x.digits n).val * p^n)
    rw [ih, Zp.shiftLeft_digit_high p hp k x n]
    rw [Nat.mul_add]
    -- Goal: p^k · x.trunc n + (x.digits n).val · p^(k+n)
    --     = p^k · x.trunc n + p^k · ((x.digits n).val · p^n)
    -- Show the algebraic identity step-by-step on the second summand.
    have hstep : (x.digits n).val * p^(k + n)
                  = p^k * ((x.digits n).val * p^n) := by
      have hpow : p^(k + n) = p^k * p^n := pow_add_pure p k n
      calc (x.digits n).val * p^(k + n)
          = (x.digits n).val * (p^k * p^n) := by rw [hpow]
        _ = p^k * ((x.digits n).val * p^n) :=
            E213.Tactic.NatHelper.mul_left_comm _ _ _
    rw [hstep]

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

/-! ## Multiplication by one on the left (`1 · x = x`)

Symmetric to `mul_one_right`: for the left operand `ZpSeq.one`, the
convolution `Σ (one).digits i · x.digits (k-i)` collapses to the
single term at `i = 0`, contributing `1 · (x.digits k).val =
(x.digits k).val`.  All other terms have `(one).digits i = 0` for
`i ≥ 1`.
-/

/-- For all `j ≥ 0`, `mulRawSum p one x k (j + 1) = (x.digits k).val`.
    The `i = 0` term contributes `(x.digits k).val`; all later terms
    contribute 0 since `(one).digits i = 0` for `i ≥ 1`. -/
theorem Zp.mulRawSum_one_left_succ {p : Nat} (hp : 1 < p) (x : ZpSeq p) (k : Nat) :
    ∀ j, Zp.mulRawSum p (ZpSeq.one p hp) x k (j + 1) = (x.digits k).val
  | 0 => by
    show (0 : Nat) + ((ZpSeq.one p hp).digits 0).val * (x.digits (k - 0)).val
          = (x.digits k).val
    rw [Zp.one_digit_val hp 0, if_pos rfl, Nat.sub_zero, Nat.one_mul,
        Nat.zero_add]
  | j + 1 => by
    show Zp.mulRawSum p (ZpSeq.one p hp) x k (j + 1)
          + ((ZpSeq.one p hp).digits (j + 1)).val
              * (x.digits (k - (j + 1))).val
        = (x.digits k).val
    rw [Zp.mulRawSum_one_left_succ hp x k j]
    rw [Zp.one_digit_val hp (j + 1),
        if_neg (fun h => Nat.noConfusion h),
        Nat.zero_mul, Nat.add_zero]

/-- `mulRaw one x k = (x.digits k).val`. -/
theorem Zp.mulRaw_one_left {p : Nat} (hp : 1 < p) (x : ZpSeq p) (k : Nat) :
    Zp.mulRaw p (ZpSeq.one p hp) x k = (x.digits k).val :=
  Zp.mulRawSum_one_left_succ hp x k k

/-- Carry stays at zero when multiplying with `one` on the left. -/
theorem Zp.mulCarry_one_left {p : Nat} (hp : 1 < p) (x : ZpSeq p) :
    ∀ k, Zp.mulCarry p (ZpSeq.one p hp) x k = 0
  | 0 => rfl
  | k + 1 => by
    show (Zp.mulRaw p (ZpSeq.one p hp) x k
            + Zp.mulCarry p (ZpSeq.one p hp) x k) / p = 0
    rw [Zp.mulRaw_one_left hp x k, Zp.mulCarry_one_left hp x k, Nat.add_zero]
    exact Nat.div_eq_of_lt (x.digits k).isLt

/-- `1 · x = x` (digit level). -/
theorem Zp.mul_one_left_digit {p : Nat} (hp : 1 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x).digits k).val
      = (x.digits k).val := by
  show (Zp.mulRaw p (ZpSeq.one p hp) x k
          + Zp.mulCarry p (ZpSeq.one p hp) x k) % p
        = (x.digits k).val
  rw [Zp.mulRaw_one_left hp x k, Zp.mulCarry_one_left hp x k, Nat.add_zero]
  exact Nat.mod_eq_of_lt (x.digits k).isLt

/-- `(1 · x).trunc n = x.trunc n` — the truncation-level identity
    obtained from the per-digit `mul_one_left_digit` by induction. -/
theorem Zp.mul_one_left_trunc {p : Nat} (hp : 1 < p) (x : ZpSeq p) :
    ∀ n, (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x).trunc n
          = x.trunc n
  | 0 => rfl
  | n + 1 => by
    show (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x).trunc n
          + ((Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x).digits n).val
              * p^n
        = x.trunc n + (x.digits n).val * p^n
    rw [Zp.mul_one_left_trunc hp x n, Zp.mul_one_left_digit hp x n]

/-- `(x · 1).trunc n = x.trunc n`. -/
theorem Zp.mul_one_right_trunc {p : Nat} (hp : 1 < p) (x : ZpSeq p) :
    ∀ n, (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).trunc n
          = x.trunc n
  | 0 => rfl
  | n + 1 => by
    show (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).trunc n
          + ((Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).digits n).val
              * p^n
        = x.trunc n + (x.digits n).val * p^n
    rw [Zp.mul_one_right_trunc hp x n, Zp.mul_one_right_digit hp x n]

/-- `(x + 0).trunc n = x.trunc n`. -/
theorem Zp.add_zero_right_trunc {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ n, (Zp.add p hp x (ZpSeq.zero p hp)).trunc n = x.trunc n
  | 0 => rfl
  | n + 1 => by
    show (Zp.add p hp x (ZpSeq.zero p hp)).trunc n
          + ((Zp.add p hp x (ZpSeq.zero p hp)).digits n).val * p^n
        = x.trunc n + (x.digits n).val * p^n
    rw [Zp.add_zero_right_trunc hp x n, Zp.add_zero_right_digit p hp x n]

/-- `(0 + x).trunc n = x.trunc n`. -/
theorem Zp.add_zero_left_trunc {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ n, (Zp.add p hp (ZpSeq.zero p hp) x).trunc n = x.trunc n
  | 0 => rfl
  | n + 1 => by
    show (Zp.add p hp (ZpSeq.zero p hp) x).trunc n
          + ((Zp.add p hp (ZpSeq.zero p hp) x).digits n).val * p^n
        = x.trunc n + (x.digits n).val * p^n
    rw [Zp.add_zero_left_trunc hp x n, Zp.add_zero_left_digit p hp x n]

/-- `(x + y).trunc n = (y + x).trunc n` (commutativity at trunc). -/
theorem Zp.add_comm_trunc {p : Nat} (hp : 0 < p) (x y : ZpSeq p) :
    ∀ n, (Zp.add p hp x y).trunc n = (Zp.add p hp y x).trunc n
  | 0 => rfl
  | n + 1 => by
    show (Zp.add p hp x y).trunc n + ((Zp.add p hp x y).digits n).val * p^n
        = (Zp.add p hp y x).trunc n + ((Zp.add p hp y x).digits n).val * p^n
    rw [Zp.add_comm_trunc hp x y n, Zp.add_comm_digit p hp x y n]

/-- `(x + complement x).trunc n` digit-by-digit is `p - 1`. -/
theorem Zp.add_complement_trunc_digit {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ k, ((Zp.add p hp x (Zp.complement p hp x)).digits k).val = p - 1 :=
  fun k => Zp.add_complement_digit p hp x k

/-! ## Multiplication by zero on the left (`0 · x = 0`) -/

/-- Partial sum with `zero` on the left vanishes (every term factor
    `(zero.digits i).val = 0`). -/
theorem Zp.mulRawSum_zero_left {p : Nat} (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ∀ upper, Zp.mulRawSum p (ZpSeq.zero p hp) x k upper = 0
  | 0 => rfl
  | i + 1 => by
    show Zp.mulRawSum p (ZpSeq.zero p hp) x k i
          + ((ZpSeq.zero p hp).digits i).val * (x.digits (k - i)).val = 0
    rw [Zp.mulRawSum_zero_left hp x k i]
    show (0 : Nat) + 0 * (x.digits (k - i)).val = 0
    rw [Nat.zero_mul, Nat.zero_add]

/-- Raw convolution `mulRaw zero x k = 0`. -/
theorem Zp.mulRaw_zero_left {p : Nat} (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    Zp.mulRaw p (ZpSeq.zero p hp) x k = 0 :=
  Zp.mulRawSum_zero_left hp x k (k + 1)

/-- Carry from `0 · x` stays at zero. -/
theorem Zp.mulCarry_zero_left {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ k, Zp.mulCarry p (ZpSeq.zero p hp) x k = 0
  | 0 => rfl
  | k + 1 => by
    show (Zp.mulRaw p (ZpSeq.zero p hp) x k
            + Zp.mulCarry p (ZpSeq.zero p hp) x k) / p = 0
    rw [Zp.mulRaw_zero_left hp x k, Zp.mulCarry_zero_left hp x k]
    show (0 + 0) / p = 0
    rw [Nat.zero_add, Nat.zero_div]

/-- `0 · x = 0` (digit level). -/
theorem Zp.mul_zero_left_digit {p : Nat} (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    ((Zp.mul p hp (ZpSeq.zero p hp) x).digits k).val = 0 := by
  show (Zp.mulRaw p (ZpSeq.zero p hp) x k
          + Zp.mulCarry p (ZpSeq.zero p hp) x k) % p = 0
  rw [Zp.mulRaw_zero_left hp x k, Zp.mulCarry_zero_left hp x k]
  show (0 + 0) % p = 0
  rw [Nat.zero_add]
  exact E213.Tactic.NatHelper.zero_mod p

/-- `(0 · x).trunc n = 0`. -/
theorem Zp.mul_zero_left_trunc {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ n, (Zp.mul p hp (ZpSeq.zero p hp) x).trunc n = 0
  | 0 => rfl
  | n + 1 => by
    show (Zp.mul p hp (ZpSeq.zero p hp) x).trunc n
          + ((Zp.mul p hp (ZpSeq.zero p hp) x).digits n).val * p^n = 0
    rw [Zp.mul_zero_left_trunc hp x n, Zp.mul_zero_left_digit hp x n,
        Nat.zero_mul, Nat.add_zero]

/-- `(x · 0).trunc n = 0`. -/
theorem Zp.mul_zero_right_trunc {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ n, (Zp.mul p hp x (ZpSeq.zero p hp)).trunc n = 0
  | 0 => rfl
  | n + 1 => by
    show (Zp.mul p hp x (ZpSeq.zero p hp)).trunc n
          + ((Zp.mul p hp x (ZpSeq.zero p hp)).digits n).val * p^n = 0
    rw [Zp.mul_zero_right_trunc hp x n, Zp.mul_zero_right_digit p hp x n,
        Nat.zero_mul, Nat.add_zero]

/-! ## Multiplicative truncation correctness at `n = 1`

The base case `(Zp.mul x y).trunc 1 = (x.trunc 1 · y.trunc 1) % p`
is structurally direct: at level 1, every term reduces to the
zeroth digit, and the carry is identically zero.  This is the
foothold for the general `mul_trunc` theorem (analog of
`Zp.add_trunc`), which requires more elaborate convolution
bookkeeping and is left for the next session.
-/

/-- Multiplicative truncation correctness at `n = 1`:
    `(Zp.mul x y).trunc 1 = (x.trunc 1 · y.trunc 1) % p`. -/
theorem Zp.mul_trunc_one (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    (Zp.mul p hp x y).trunc 1 = (x.trunc 1 * y.trunc 1) % p := by
  -- Unfold trunc 1 = 0 + digit 0 * p^0 = digit 0.
  show (0 : Nat) + ((Zp.mul p hp x y).digits 0).val * p^0
        = (0 + (x.digits 0).val * p^0) * (0 + (y.digits 0).val * p^0) % p
  rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.mul_one,
      Nat.zero_add, Nat.zero_add, Nat.zero_add]
  -- Goal: ((mul x y).digits 0).val = (x.digits 0).val * (y.digits 0).val % p.
  show (Zp.mulRaw p x y 0 + Zp.mulCarry p x y 0) % p
        = (x.digits 0).val * (y.digits 0).val % p
  -- Unfold mulCarry 0 = 0 and mulRaw 0 = mulRawSum 0 1 = (x.digit 0)·(y.digit 0).
  show (Zp.mulRaw p x y 0 + 0) % p
        = (x.digits 0).val * (y.digits 0).val % p
  rw [Nat.add_zero]
  show ((0 : Nat) + (x.digits 0).val * (y.digits (0 - 0)).val) % p
        = (x.digits 0).val * (y.digits 0).val % p
  rw [Nat.sub_zero, Nat.zero_add]

/-! ## Structural identity for multiplication (analog of `add_trunc_eq`)

The "raw-sum" `mulSumRaw x y n := Σ_{k<n} mulRaw k · p^k` is the
formal sum of raw convolution values weighted by their digit
positions, before applying any carry propagation.  The digit-carry
FSM step `(mulRaw k + mulCarry k) = (mul.digits k) + mulCarry (k+1) · p`
cascades to give the structural identity:

    mulSumRaw x y n = (Zp.mul x y).trunc n + mulCarry n · p^n

Proof is by induction on `n`; the step reuses `split_mul_pow`.
-/

/-- Partial sum `Σ_{k=0..n-1} mulRaw k · p^k`. -/
def Zp.mulSumRaw (p : Nat) (x y : ZpSeq p) : Nat → Nat
  | 0 => 0
  | n + 1 => Zp.mulSumRaw p x y n + Zp.mulRaw p x y n * p^n

/-- Structural identity: `mulSumRaw` equals truncation plus the
    top-position carry contribution. -/
theorem Zp.mulSumRaw_eq_trunc (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    ∀ n, Zp.mulSumRaw p x y n
          = (Zp.mul p hp x y).trunc n + Zp.mulCarry p x y n * p^n
  | 0 => by show (0 : Nat) = 0 + 0 * p^0; rfl
  | n + 1 => by
    have ih : Zp.mulSumRaw p x y n
              = (Zp.mul p hp x y).trunc n + Zp.mulCarry p x y n * p^n :=
      Zp.mulSumRaw_eq_trunc p hp x y n
    have hpow : p^(n+1) = p^n * p := Nat.pow_succ p n
    show Zp.mulSumRaw p x y n + Zp.mulRaw p x y n * p^n
          = ((Zp.mul p hp x y).trunc n
                + ((Zp.mulRaw p x y n + Zp.mulCarry p x y n) % p) * p^n)
              + ((Zp.mulRaw p x y n + Zp.mulCarry p x y n) / p) * p^(n+1)
    calc Zp.mulSumRaw p x y n + Zp.mulRaw p x y n * p^n
        = ((Zp.mul p hp x y).trunc n + Zp.mulCarry p x y n * p^n)
            + Zp.mulRaw p x y n * p^n := by rw [ih]
      _ = (Zp.mul p hp x y).trunc n
            + (Zp.mulCarry p x y n + Zp.mulRaw p x y n) * p^n := by
              rw [Nat.add_assoc, ← E213.Tactic.NatHelper.add_mul]
      _ = (Zp.mul p hp x y).trunc n
            + (Zp.mulRaw p x y n + Zp.mulCarry p x y n) * p^n := by
              rw [Nat.add_comm (Zp.mulCarry p x y n) (Zp.mulRaw p x y n)]
      _ = (Zp.mul p hp x y).trunc n
            + (((Zp.mulRaw p x y n + Zp.mulCarry p x y n) % p) * p^n
                + ((Zp.mulRaw p x y n + Zp.mulCarry p x y n) / p) * (p^n * p)) := by
              rw [Zp.split_mul_pow]
      _ = ((Zp.mul p hp x y).trunc n
            + ((Zp.mulRaw p x y n + Zp.mulCarry p x y n) % p) * p^n)
          + ((Zp.mulRaw p x y n + Zp.mulCarry p x y n) / p) * (p^n * p) :=
            (Nat.add_assoc _ _ _).symm
      _ = ((Zp.mul p hp x y).trunc n
            + ((Zp.mulRaw p x y n + Zp.mulCarry p x y n) % p) * p^n)
          + ((Zp.mulRaw p x y n + Zp.mulCarry p x y n) / p) * p^(n+1) := by
              rw [hpow]

/-- Corollary: `mulSumRaw n` modulo `p^n` equals `(Zp.mul x y).trunc n`.
    Follows from the structural identity (the carry term is a
    multiple of `p^n`) plus the bound `trunc < p^n`. -/
theorem Zp.mulSumRaw_mod_eq_trunc (p : Nat) (hp : 0 < p) (x y : ZpSeq p)
    (n : Nat) :
    Zp.mulSumRaw p x y n % p^n = (Zp.mul p hp x y).trunc n := by
  have hstruct := Zp.mulSumRaw_eq_trunc p hp x y n
  have hlt : (Zp.mul p hp x y).trunc n < p^n :=
    ZpSeq.trunc_lt_p_pow hp _ n
  rw [hstruct, E213.Tactic.NatHelper.add_mul_mod_self_pure]
  exact Nat.mod_eq_of_lt hlt

/-! ## Bilinear-sum decomposition (step 2 of mul_trunc — partial)

To bridge `mulSumRaw n` and `x.trunc n · y.trunc n`, decompose
the latter as a bilinear sum:

  x.trunc a · y.trunc b = Σ_{i<a} Σ_{j<b} x_i · y_j · p^(i+j)

This sum, restricted to indices `i + j < n` and unrestricted in
the corners, exactly recovers `mulSumRaw n` via convolution
reindexing.  Indices `(i, j)` with both `< n` but `i + j ≥ n`
contribute a `p^n`-multiple, vanishing mod `p^n`.

We define the column sum `colSum i b` for the inner sum over `j`,
and the full bilinear sum `bilinSum a b` for the double sum.
-/

/-- Inner column sum: `Σ_{j<b} (x.digits i).val · (y.digits j).val · p^(i+j)`. -/
def Zp.colSum (p : Nat) (x y : ZpSeq p) (i : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => Zp.colSum p x y i b
              + (x.digits i).val * (y.digits b).val * p^(i + b)

/-- Bilinear sum `Σ_{i<a} colSum p x y i b`. -/
def Zp.bilinSum (p : Nat) (x y : ZpSeq p) (b : Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => Zp.bilinSum p x y b a + Zp.colSum p x y a b

/-- Closed form for `colSum`:
    `colSum i b = (x.digits i).val · p^i · y.trunc b`. -/
theorem Zp.colSum_eq (p : Nat) (x y : ZpSeq p) (i : Nat) :
    ∀ b, Zp.colSum p x y i b = (x.digits i).val * p^i * y.trunc b
  | 0 => by show (0 : Nat) = (x.digits i).val * p^i * 0; rw [Nat.mul_zero]
  | b + 1 => by
    show Zp.colSum p x y i b
          + (x.digits i).val * (y.digits b).val * p^(i + b)
        = (x.digits i).val * p^i * (y.trunc b + (y.digits b).val * p^b)
    rw [Zp.colSum_eq p x y i b, Nat.mul_add, pow_add_pure]
    -- Goal: x_i p^i y.trunc b + x_i y_b (p^i p^b)
    --     = x_i p^i y.trunc b + x_i p^i (y_b p^b)
    -- Reduces to: x_i y_b (p^i p^b) = x_i p^i (y_b p^b), which is
    -- (a · b) · (c · d) = (a · c) · (b · d) with a = x_i, b = y_b,
    -- c = p^i, d = p^b — `mul_mul_mul_comm_213`.
    rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213
          (x.digits i).val (y.digits b).val (p^i) (p^b)]

/-- Closed form for `bilinSum`: `bilinSum b a = x.trunc a · y.trunc b`. -/
theorem Zp.bilinSum_eq (p : Nat) (x y : ZpSeq p) (b : Nat) :
    ∀ a, Zp.bilinSum p x y b a = x.trunc a * y.trunc b
  | 0 => by show (0 : Nat) = 0 * y.trunc b; rw [Nat.zero_mul]
  | a + 1 => by
    show Zp.bilinSum p x y b a + Zp.colSum p x y a b
          = (x.trunc a + (x.digits a).val * p^a) * y.trunc b
    rw [Zp.bilinSum_eq p x y b a, Zp.colSum_eq p x y a b,
        E213.Tactic.NatHelper.add_mul]

/-! ## Multiplicative truncation correctness at `n = 2`

The next stepping stone after `mul_trunc_one`.  At `n = 2`, the
bilinear sum `bilinSum 2 2` has exactly one off-diagonal pair
`(i, j) = (1, 1)` with `i + j = 2 ≥ n = 2`.  Its contribution is
`x.digits 1 · y.digits 1 · p^2`, a multiple of `p^2`.

Hence: `bilinSum 2 2 = mulSumRaw 2 + (x.digits 1).val ·
(y.digits 1).val · p^2`, and after `% p^2` the off-diagonal term
vanishes, giving `bilinSum 2 2 % p^2 = mulSumRaw 2 % p^2 =
(Zp.mul x y).trunc 2`.
-/

/-- Multiplicative truncation correctness at `n = 2`. -/
theorem Zp.mul_trunc_two (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    (Zp.mul p hp x y).trunc 2 = (x.trunc 2 * y.trunc 2) % p^2 := by
  -- (Zp.mul x y).trunc 2 = mulSumRaw 2 % p^2  (Step 1 corollary)
  rw [← Zp.mulSumRaw_mod_eq_trunc p hp x y 2]
  -- Goal: mulSumRaw 2 % p^2 = (x.trunc 2 * y.trunc 2) % p^2
  -- Substitute x.trunc 2 * y.trunc 2 ← bilinSum 2 2 (Step 2 closed form).
  rw [← Zp.bilinSum_eq p x y 2 2]
  -- Goal: mulSumRaw 2 % p^2 = bilinSum 2 2 % p^2
  -- bilinSum 2 2 = mulSumRaw 2 + (x.digits 1).val · (y.digits 1).val · p^2.
  -- The mod-p^2 of (mulSumRaw 2 + ·*p^2) drops the second summand.
  rw [show Zp.bilinSum p x y 2 2
            = Zp.mulSumRaw p x y 2
                + (x.digits 1).val * (y.digits 1).val * p^2 from by
        -- LHS unfolds to: colSum 0 2 + colSum 1 2
        --              = (x_0 p^0 * y.trunc 2) + (x_1 p^1 * y.trunc 2)
        --              = (x_0 + x_1 p) * y.trunc 2
        --              = x.trunc 2 * y.trunc 2
        -- by bilinSum_eq.
        -- RHS = mulRaw 0 * p^0 + mulRaw 1 * p^1 + x_1 y_1 p^2
        --     = mulRaw 0 + mulRaw 1 p + x_1 y_1 p^2
        -- mulRaw 0 = x_0 y_0; mulRaw 1 = x_0 y_1 + x_1 y_0.
        -- So RHS = x_0 y_0 + (x_0 y_1 + x_1 y_0) p + x_1 y_1 p^2.
        -- And LHS via bilinSum_eq = x.trunc 2 * y.trunc 2
        --   = (x_0 + x_1 p)(y_0 + y_1 p)
        --   = x_0 y_0 + x_0 y_1 p + x_1 y_0 p + x_1 y_1 p^2
        --   = RHS by distributing the middle (x_0 y_1 + x_1 y_0) p.
        rw [Zp.bilinSum_eq]
        -- Goal: x.trunc 2 · y.trunc 2 = mulSumRaw 2 + x_1 y_1 p^2
        -- Unfold both sides.
        show (0 + (x.digits 0).val * p^0 + (x.digits 1).val * p^1)
              * (0 + (y.digits 0).val * p^0 + (y.digits 1).val * p^1)
            = ((0 + Zp.mulRaw p x y 0 * p^0) + Zp.mulRaw p x y 1 * p^1)
                + (x.digits 1).val * (y.digits 1).val * p^2
        -- mulRaw 0 = x_0 * y_0 by definition unfolding.
        -- mulRaw 1 = x_0 y_1 + x_1 y_0 by definition.
        show (0 + (x.digits 0).val * p^0 + (x.digits 1).val * p^1)
              * (0 + (y.digits 0).val * p^0 + (y.digits 1).val * p^1)
            = ((0 + (0 + (x.digits 0).val * (y.digits 0).val) * p^0)
                  + (0 + (x.digits 0).val * (y.digits 1).val
                          + (x.digits 1).val * (y.digits 0).val) * p^1)
                + (x.digits 1).val * (y.digits 1).val * p^2
        -- Now reduce p^0 = 1, p^1 = p, and verify by Nat arithmetic.
        rw [Nat.pow_zero, Nat.pow_one, Nat.mul_one, Nat.mul_one,
            Nat.mul_one, Nat.zero_add, Nat.zero_add, Nat.zero_add,
            Nat.zero_add, Nat.zero_add]
        -- Goal: (x_0 + x_1 p) * (y_0 + y_1 p)
        --     = (x_0 y_0 + (x_0 y_1 + x_1 y_0) p) + x_1 y_1 p^2
        -- Expand LHS by distributivity.
        rw [E213.Tactic.NatHelper.add_mul, Nat.mul_add, Nat.mul_add]
        -- Goal: (x_0 y_0 + x_0 (y_1 p)) + (x_1 p y_0 + x_1 p (y_1 p))
        --     = (x_0 y_0 + (x_0 y_1 + x_1 y_0) p) + x_1 y_1 p^2
        rw [Nat.add_assoc, ← Nat.add_assoc ((x.digits 0).val
                * ((y.digits 1).val * p))]
        rw [show (x.digits 0).val * ((y.digits 1).val * p)
                  + (x.digits 1).val * p * (y.digits 0).val
                = ((x.digits 0).val * (y.digits 1).val
                    + (x.digits 1).val * (y.digits 0).val) * p from by
              rw [E213.Tactic.NatHelper.add_mul]
              rw [← E213.Tactic.NatHelper.mul_assoc (x.digits 0).val
                    (y.digits 1).val p]
              rw [E213.Tactic.NatHelper.mul_assoc (x.digits 1).val p
                    (y.digits 0).val]
              rw [Nat.mul_comm p (y.digits 0).val]
              rw [← E213.Tactic.NatHelper.mul_assoc (x.digits 1).val
                    (y.digits 0).val p]]
        rw [Nat.add_assoc]
        rw [show (x.digits 1).val * p * ((y.digits 1).val * p)
                = (x.digits 1).val * (y.digits 1).val * p^2 from by
              rw [show p^2 = p * p from by rw [Nat.pow_succ, Nat.pow_one]]
              exact E213.Tactic.NatHelper.mul_mul_mul_comm_213 _ _ _ _]]
  -- Now: mulSumRaw 2 % p^2 = (mulSumRaw 2 + x_1 y_1 p^2) % p^2
  rw [E213.Tactic.NatHelper.add_mul_mod_self_pure]

/-! ## Multiplicative truncation correctness at `n = 3`

At `n = 3`, the off-diagonal pairs `(i, j)` with `i, j < 3` and
`i + j ≥ 3` are `(1, 2), (2, 1), (2, 2)`.  Their contributions
are `x_1 · y_2 · p^3`, `x_2 · y_1 · p^3`, and `x_2 · y_2 · p^4`
respectively — all multiples of `p^3`.

So `bilinSum 3 3 = mulSumRaw 3 + ((x_1 · y_2 + x_2 · y_1) + x_2 · y_2 · p) · p^3`,
and `mul_trunc 3` follows by the same chain as `mul_trunc_two`.

The proof is mechanical Nat distributivity (same shape as
`mul_trunc_two`, more terms).  Demonstrated case at `p = 5`,
`x = y = canonical_5adic_NU` would compute exactly; the general
proof is omitted in favor of the general bridge (future work).
-/

/-- Multiplicative truncation correctness at `n = 3` for the case
    `y = ZpSeq.one`, which collapses the off-diagonal terms via
    `mul_one_right_trunc` (no bridge needed). -/
theorem Zp.mul_trunc_three_one_right {p : Nat} (hp : 1 < p) (x : ZpSeq p) :
    (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).trunc 3
      = (x.trunc 3 * (ZpSeq.one p hp).trunc 3) % p^3 := by
  rw [Zp.mul_one_right_trunc hp x 3]
  rw [show (ZpSeq.one p hp).trunc 3 = 1 from ZpSeq.trunc_one_succ p hp 2]
  rw [Nat.mul_one]
  exact (Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow
            (Nat.lt_of_succ_lt hp) x 3)).symm

/-- Multiplicative truncation correctness for `y = ZpSeq.one` at
    any positive level `n + 1`.  Generalizes
    `mul_trunc_one_one` / `mul_trunc_two` / `mul_trunc_three_one_right`. -/
theorem Zp.mul_trunc_succ_one_right {p : Nat} (hp : 1 < p) (x : ZpSeq p)
    (n : Nat) :
    (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).trunc (n + 1)
      = (x.trunc (n + 1) * (ZpSeq.one p hp).trunc (n + 1)) % p^(n + 1) := by
  rw [Zp.mul_one_right_trunc hp x (n + 1)]
  rw [ZpSeq.trunc_one_succ p hp n, Nat.mul_one]
  exact (Nat.mod_eq_of_lt
            (ZpSeq.trunc_lt_p_pow (Nat.lt_of_succ_lt hp) x (n + 1))).symm

/-- Multiplicative truncation correctness for `y = ZpSeq.one` at
    any level `n` (including `n = 0`). -/
theorem Zp.mul_trunc_one_right {p : Nat} (hp : 1 < p) (x : ZpSeq p) :
    ∀ n, (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).trunc n
          = (x.trunc n * (ZpSeq.one p hp).trunc n) % p^n
  | 0 => rfl
  | n + 1 => Zp.mul_trunc_succ_one_right hp x n

/-- Multiplicative truncation correctness for `x = ZpSeq.one` at
    the successor level `n + 1`. -/
theorem Zp.mul_trunc_succ_one_left {p : Nat} (hp : 1 < p) (x : ZpSeq p)
    (n : Nat) :
    (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x).trunc (n + 1)
      = ((ZpSeq.one p hp).trunc (n + 1) * x.trunc (n + 1)) % p^(n + 1) := by
  rw [Zp.mul_one_left_trunc hp x (n + 1)]
  rw [ZpSeq.trunc_one_succ p hp n, Nat.one_mul]
  exact (Nat.mod_eq_of_lt
            (ZpSeq.trunc_lt_p_pow (Nat.lt_of_succ_lt hp) x (n + 1))).symm

/-- Multiplicative truncation correctness for `x = ZpSeq.one`
    at any level. -/
theorem Zp.mul_trunc_one_left {p : Nat} (hp : 1 < p) (x : ZpSeq p) :
    ∀ n, (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x).trunc n
          = ((ZpSeq.one p hp).trunc n * x.trunc n) % p^n
  | 0 => rfl
  | n + 1 => Zp.mul_trunc_succ_one_left hp x n

/-- Multiplicative truncation correctness for `y = ZpSeq.zero`. -/
theorem Zp.mul_trunc_zero_right {p : Nat} (hp : 0 < p) (x : ZpSeq p) (n : Nat) :
    (Zp.mul p hp x (ZpSeq.zero p hp)).trunc n
      = (x.trunc n * (ZpSeq.zero p hp).trunc n) % p^n := by
  rw [Zp.mul_zero_right_trunc hp x n, ZpSeq.trunc_zero p hp n,
      Nat.mul_zero]
  exact (E213.Tactic.NatHelper.zero_mod _).symm

/-- Multiplicative truncation correctness for `x = ZpSeq.zero`. -/
theorem Zp.mul_trunc_zero_left {p : Nat} (hp : 0 < p) (x : ZpSeq p) (n : Nat) :
    (Zp.mul p hp (ZpSeq.zero p hp) x).trunc n
      = ((ZpSeq.zero p hp).trunc n * x.trunc n) % p^n := by
  rw [Zp.mul_zero_left_trunc hp x n, ZpSeq.trunc_zero p hp n,
      Nat.zero_mul]
  exact (E213.Tactic.NatHelper.zero_mod _).symm

/-! ## Off-diagonal sum scaffold (for general `mul_trunc`)

For each row `i`, the off-diagonal contributions at level `n` are
the values `(x.digits i).val · (y.digits (n - i + m)).val · p^m`
for `m ∈ [0, i)` — equivalently, `(i, j)` pairs with `j = n - i + m`,
i.e., `j ∈ [n - i, n)`.  The outer accumulator sums these rows.

The full bridge `bilinSum n n = mulSumRaw n + offDiagSum n n · p^n`
is verified by hand for `n ∈ {0, 1, 2, 3}` and matches the
expected off-diagonal decomposition.  Lean proof: future work.
-/

/-- Inner off-diagonal row sum at level `n`, row `i`, up to count `m`. -/
def Zp.offDiagRow (p : Nat) (x y : ZpSeq p) (n i : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => Zp.offDiagRow p x y n i m
              + (x.digits i).val * (y.digits (n - i + m)).val * p^m

/-- Outer off-diagonal accumulator at level `n`, summing rows
    `i ∈ [0, upper)`. -/
def Zp.offDiagSum (p : Nat) (x y : ZpSeq p) (n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => Zp.offDiagSum p x y n i + Zp.offDiagRow p x y n i i

/-- Off-diagonal row at empty count is zero (definitional). -/
theorem Zp.offDiagRow_zero (p : Nat) (x y : ZpSeq p) (n i : Nat) :
    Zp.offDiagRow p x y n i 0 = 0 := rfl

/-- Off-diagonal sum at empty outer bound is zero (definitional). -/
theorem Zp.offDiagSum_zero (p : Nat) (x y : ZpSeq p) (n : Nat) :
    Zp.offDiagSum p x y n 0 = 0 := rfl

/-! ## colSum extension: telescoping over a starting offset

`colSum p x y i (a + c)` decomposes as `colSum p x y i a + (terms
from j = a to a + c - 1)`.  This lets us split `colSum p x y i n`
into the "diagonal part" (j < n - i) and the "off-diagonal part"
(j ∈ [n - i, n)).
-/

/-- Extension sum: `Σ_{m=0..c-1} x_i · y_{a+m} · p^(i+a+m)`.  The
    "tail" of `colSum` from upper = a to upper = a + c. -/
def Zp.extColSum (p : Nat) (x y : ZpSeq p) (i a : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => Zp.extColSum p x y i a m
              + (x.digits i).val * (y.digits (a + m)).val * p^(i + a + m)

/-- Telescoping: `colSum p x y i (a + c) = colSum p x y i a +
    extColSum p x y i a c`. -/
theorem Zp.colSum_extend (p : Nat) (x y : ZpSeq p) (i a : Nat) :
    ∀ c, Zp.colSum p x y i (a + c)
          = Zp.colSum p x y i a + Zp.extColSum p x y i a c
  | 0 => by
    show Zp.colSum p x y i (a + 0) = Zp.colSum p x y i a + 0
    rw [Nat.add_zero, Nat.add_zero]
  | c + 1 => by
    have ih : Zp.colSum p x y i (a + c)
              = Zp.colSum p x y i a + Zp.extColSum p x y i a c :=
      Zp.colSum_extend p x y i a c
    -- a + (c + 1) = (a + c) + 1, so colSum (a + (c+1)) unfolds via
    -- the colSum recursion at b = a + c.
    show Zp.colSum p x y i (a + c)
          + (x.digits i).val * (y.digits (a + c)).val * p^(i + (a + c))
        = Zp.colSum p x y i a
            + (Zp.extColSum p x y i a c
                + (x.digits i).val * (y.digits (a + c)).val
                    * p^(i + a + c))
    rw [ih, Nat.add_assoc (Zp.colSum p x y i a) (Zp.extColSum p x y i a c)]
    -- Now the remaining mismatch is p^(i + (a + c)) vs p^(i + a + c).
    -- Nat add is left-assoc, so i + a + c = (i + a) + c, and i + (a + c)
    -- needs associativity to match.
    rw [show i + (a + c) = i + a + c from (Nat.add_assoc i a c).symm]

/-- When the start offset `a = n - i` (so `i + a = n`), the extension
    sum factors as `p^n · offDiagRow p x y n i c`. -/
theorem Zp.extColSum_eq_offDiagRow (p : Nat) (x y : ZpSeq p)
    (i n : Nat) (h : i ≤ n) :
    ∀ c, Zp.extColSum p x y i (n - i) c
          = p^n * Zp.offDiagRow p x y n i c
  | 0 => by show (0 : Nat) = p^n * 0; rw [Nat.mul_zero]
  | c + 1 => by
    have ih : Zp.extColSum p x y i (n - i) c
              = p^n * Zp.offDiagRow p x y n i c :=
      Zp.extColSum_eq_offDiagRow p x y i n h c
    show Zp.extColSum p x y i (n - i) c
          + (x.digits i).val * (y.digits ((n - i) + c)).val
              * p^(i + (n - i) + c)
        = p^n * (Zp.offDiagRow p x y n i c
                  + (x.digits i).val * (y.digits (n - i + c)).val * p^c)
    rw [ih, Nat.mul_add]
    -- Goal: p^n * offDiagRow c + x_i * y_{(n-i)+c} * p^(i + (n-i) + c)
    --     = p^n * offDiagRow c + p^n * (x_i * y_{n-i+c} * p^c)
    -- Reduce i + (n - i) = n via sub_add_cancel.
    rw [show i + (n - i) = n from by
          rw [Nat.add_comm]
          exact E213.Tactic.NatHelper.sub_add_cancel h]
    -- Goal: ... + x_i * y * p^(n + c) = ... + p^n * (x_i * y * p^c)
    rw [pow_add_pure]
    -- Goal: ... + x_i * y * (p^n * p^c) = ... + p^n * (x_i * y * p^c)
    -- Use mul_left_comm: a * (b * c) = b * (a * c) with
    -- a = (x_i * y), b = p^n, c = p^c.
    rw [E213.Tactic.NatHelper.mul_left_comm
          ((x.digits i).val * (y.digits ((n - i) + c)).val) (p^n) (p^c)]

/-- Splitting colSum at the diagonal: for `i ≤ n`,
    `colSum p x y i n = colSum p x y i (n - i) + p^n · offDiagRow p x y n i i`. -/
theorem Zp.colSum_split (p : Nat) (x y : ZpSeq p) (i n : Nat) (h : i ≤ n) :
    Zp.colSum p x y i n
      = Zp.colSum p x y i (n - i) + p^n * Zp.offDiagRow p x y n i i := by
  -- Use colSum_extend with a = n - i, c = i (since (n - i) + i = n).
  have hsum : (n - i) + i = n :=
    E213.Tactic.NatHelper.sub_add_cancel h
  have h1 : Zp.colSum p x y i ((n - i) + i)
            = Zp.colSum p x y i (n - i) + Zp.extColSum p x y i (n - i) i :=
    Zp.colSum_extend p x y i (n - i) i
  rw [hsum] at h1
  rw [h1, Zp.extColSum_eq_offDiagRow p x y i n h i]

/-- Diagonal sum at level `n`: `Σ_{i<upper} colSum p x y i (n - i)`. -/
def Zp.diagSum (p : Nat) (x y : ZpSeq p) (n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => Zp.diagSum p x y n i + Zp.colSum p x y i (n - i)

/-- One-step `colSum` extension at the diagonal cut-off: for `i ≤ N`,
    `colSum p x y i ((N + 1) - i) = colSum p x y i (N - i)
    + x_i · y_{N-i} · p^N`. -/
private theorem colSum_one_step (p : Nat) (x y : ZpSeq p) (i N : Nat)
    (hi : i ≤ N) :
    Zp.colSum p x y i ((N + 1) - i)
      = Zp.colSum p x y i (N - i)
          + (x.digits i).val * (y.digits (N - i)).val * p^N := by
  have h1 : (N + 1) - i = (N - i) + 1 := by
    rw [Nat.add_comm N 1, E213.Tactic.NatHelper.add_sub_assoc 1 hi,
        Nat.add_comm 1 (N - i)]
  have h2 : i + (N - i) = N := by
    rw [Nat.add_comm]; exact E213.Tactic.NatHelper.sub_add_cancel hi
  rw [h1]
  -- Goal: colSum p x y i ((N - i) + 1) = colSum p x y i (N - i) + ... * p^N
  show Zp.colSum p x y i (N - i)
        + (x.digits i).val * (y.digits (N - i)).val * p^(i + (N - i))
      = Zp.colSum p x y i (N - i)
          + (x.digits i).val * (y.digits (N - i)).val * p^N
  rw [h2]

/-- Bilinear-sum decomposition: for `upper ≤ n`,
    `bilinSum p x y n upper = diagSum p x y n upper + p^n · offDiagSum p x y n upper`. -/
theorem Zp.bilinSum_decomp (p : Nat) (x y : ZpSeq p) (n : Nat) :
    ∀ upper, upper ≤ n → Zp.bilinSum p x y n upper
      = Zp.diagSum p x y n upper + p^n * Zp.offDiagSum p x y n upper
  | 0, _ => by show (0 : Nat) = 0 + p^n * 0; rw [Nat.mul_zero, Nat.add_zero]
  | i + 1, h => by
    have h_le : i ≤ n := Nat.le_of_succ_le h
    have ih : Zp.bilinSum p x y n i
              = Zp.diagSum p x y n i + p^n * Zp.offDiagSum p x y n i :=
      Zp.bilinSum_decomp p x y n i h_le
    show Zp.bilinSum p x y n i + Zp.colSum p x y i n
        = Zp.diagSum p x y n i + Zp.colSum p x y i (n - i)
            + p^n * (Zp.offDiagSum p x y n i + Zp.offDiagRow p x y n i i)
    rw [ih, Zp.colSum_split p x y i n h_le, Nat.mul_add]
    exact swap_inner (Zp.diagSum p x y n i) (p^n * Zp.offDiagSum p x y n i)
            (Zp.colSum p x y i (n - i)) (p^n * Zp.offDiagRow p x y n i i)

/-- Diagonal-sum level extension: for `upper ≤ N + 1`,
    `diagSum p x y (N + 1) upper = diagSum p x y N upper +
    p^N · mulRawSum p x y N upper`. -/
theorem Zp.diagSum_succ_level (p : Nat) (x y : ZpSeq p) (N : Nat) :
    ∀ upper, upper ≤ N + 1 →
      Zp.diagSum p x y (N + 1) upper
        = Zp.diagSum p x y N upper + p^N * Zp.mulRawSum p x y N upper
  | 0, _ => by
    show (0 : Nat) = 0 + p^N * 0
    rw [Nat.mul_zero, Nat.add_zero]
  | i + 1, h => by
    have hi : i ≤ N := Nat.le_of_succ_le_succ h
    have ih : Zp.diagSum p x y (N + 1) i
              = Zp.diagSum p x y N i + p^N * Zp.mulRawSum p x y N i :=
      Zp.diagSum_succ_level p x y N i (Nat.le_of_lt h)
    show Zp.diagSum p x y (N + 1) i + Zp.colSum p x y i ((N + 1) - i)
        = (Zp.diagSum p x y N i + Zp.colSum p x y i (N - i))
            + p^N * (Zp.mulRawSum p x y N i
                      + (x.digits i).val * (y.digits (N - i)).val)
    rw [ih, colSum_one_step p x y i N hi, Nat.mul_add]
    -- Goal: (diagSum_N_i + p^N · mulRawSum_N_i) + (colSum_(N-i) + x_i · y_{N-i} · p^N)
    --     = (diagSum_N_i + colSum_(N-i))
    --         + (p^N · mulRawSum_N_i + p^N · (x_i · y_{N-i}))
    -- Convert x_i · y_{N-i} · p^N → p^N · (x_i · y_{N-i}) via mul_comm.
    rw [show (x.digits i).val * (y.digits (N - i)).val * p^N
              = p^N * ((x.digits i).val * (y.digits (N - i)).val) from
            Nat.mul_comm _ _]
    -- Now apply swap_inner.
    exact swap_inner _ _ _ _

/-- The diagonal sum at the top index equals `mulSumRaw`:
    `diagSum p x y N N = mulSumRaw p x y N`. -/
theorem Zp.diagSum_eq_mulSumRaw (p : Nat) (x y : ZpSeq p) :
    ∀ N, Zp.diagSum p x y N N = Zp.mulSumRaw p x y N
  | 0 => rfl
  | N + 1 => by
    have ih : Zp.diagSum p x y N N = Zp.mulSumRaw p x y N :=
      Zp.diagSum_eq_mulSumRaw p x y N
    show Zp.diagSum p x y (N + 1) N + Zp.colSum p x y N ((N + 1) - N)
        = Zp.mulSumRaw p x y N + Zp.mulRaw p x y N * p^N
    have step1 : Zp.diagSum p x y (N + 1) N
                  = Zp.diagSum p x y N N + p^N * Zp.mulRawSum p x y N N :=
      Zp.diagSum_succ_level p x y N N (Nat.le_succ N)
    have hsub : (N + 1) - N = 1 := by
      rw [Nat.add_comm N 1]
      exact E213.Tactic.NatHelper.add_sub_cancel_right 1 N
    rw [step1, ih, hsub]
    -- Simplify colSum p x y N 1 = x_N · y_0 · p^N.
    rw [show Zp.colSum p x y N 1
              = (x.digits N).val * (y.digits 0).val * p^N from by
          show (0 : Nat) + (x.digits N).val * (y.digits 0).val * p^(N + 0)
                = (x.digits N).val * (y.digits 0).val * p^N
          rw [Nat.add_zero, Nat.zero_add]]
    -- Unfold mulRaw N = mulRawSum N N + x_N · y_0.
    rw [show Zp.mulRaw p x y N
              = Zp.mulRawSum p x y N N
                  + (x.digits N).val * (y.digits 0).val from by
          show Zp.mulRawSum p x y N N
                + (x.digits N).val * (y.digits (N - N)).val
              = Zp.mulRawSum p x y N N
                  + (x.digits N).val * (y.digits 0).val
          rw [Nat.sub_self]]
    -- Expand RHS: (mulRawSum + x_N · y_0) · p^N = mulRawSum · p^N + x_N · y_0 · p^N.
    rw [E213.Tactic.NatHelper.add_mul]
    -- Swap p^N · mulRawSum to mulRawSum · p^N.
    rw [Nat.mul_comm (p^N) (Zp.mulRawSum p x y N N)]
    -- Final: associativity.
    exact Nat.add_assoc _ _ _

/-- **The bridge** (structural identity for `mul_trunc`):
    `bilinSum p x y n n = mulSumRaw p x y n + p^n · offDiagSum p x y n n`.

    The bilinear-sum decomposition (`bilinSum_decomp` at upper = n,
    which requires n ≤ n) plus the diagonal-sum identity
    (`diagSum_eq_mulSumRaw`). -/
theorem Zp.bilinSum_eq_mulSumRaw_plus_offDiag (p : Nat) (x y : ZpSeq p)
    (n : Nat) :
    Zp.bilinSum p x y n n
      = Zp.mulSumRaw p x y n + p^n * Zp.offDiagSum p x y n n := by
  have h := Zp.bilinSum_decomp p x y n n (Nat.le_refl n)
  rw [h, Zp.diagSum_eq_mulSumRaw p x y n]

/-- **The bridge (mod form)**:
    `bilinSum p x y n n % p^n = mulSumRaw p x y n % p^n`. -/
theorem Zp.bilinSum_mod_eq_mulSumRaw_mod (p : Nat) (x y : ZpSeq p) (n : Nat) :
    Zp.bilinSum p x y n n % p^n = Zp.mulSumRaw p x y n % p^n := by
  rw [Zp.bilinSum_eq_mulSumRaw_plus_offDiag]
  -- Goal: (mulSumRaw + p^n · offDiagSum) % p^n = mulSumRaw % p^n
  rw [Nat.mul_comm (p^n) (Zp.offDiagSum p x y n n)]
  -- (mulSumRaw + offDiagSum · p^n) % p^n = mulSumRaw % p^n via add_mul_mod_self_pure.
  exact E213.Tactic.NatHelper.add_mul_mod_self_pure _ _ _

/-- **General `mul_trunc`**: the multiplicative ring-quotient theorem
    for arbitrary operands at any level `n`.

    Derivation:
      `(Zp.mul x y).trunc n`
        = `mulSumRaw n % p^n`            (by `mulSumRaw_mod_eq_trunc`)
        = `bilinSum n n % p^n`           (by the bridge)
        = `(x.trunc n * y.trunc n) % p^n`  (by `bilinSum_eq`). -/
theorem Zp.mul_trunc (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (n : Nat) :
    (Zp.mul p hp x y).trunc n = (x.trunc n * y.trunc n) % p^n := by
  rw [← Zp.mulSumRaw_mod_eq_trunc p hp x y n,
      ← Zp.bilinSum_mod_eq_mulSumRaw_mod p x y n,
      Zp.bilinSum_eq p x y n n]

/-! ## Shift smokes -/

/-- Smoke: shifting `one` by 1 puts `1` at position 1. -/
theorem Zp.smoke_shiftLeft_one_5_d1 :
    ((Zp.shiftLeft 5 (by decide) 1
        (ZpSeq.one 5 (by decide))).digits 1).val = 1 := by
  show (if (1 : Nat) < 1 then (⟨0, by decide⟩ : Fin 5)
        else (ZpSeq.one 5 (by decide)).digits (1 - 1)).val = 1
  rw [if_neg (by decide : ¬ ((1 : Nat) < 1))]
  rfl

/-- Smoke: shifting `one` by 1 puts `0` at position 0. -/
theorem Zp.smoke_shiftLeft_one_5_d0 :
    ((Zp.shiftLeft 5 (by decide) 1
        (ZpSeq.one 5 (by decide))).digits 0).val = 0 := by
  exact Zp.shiftLeft_digit_low 5 (by decide) 1 (ZpSeq.one 5 (by decide))
          0 (by decide)

end E213.Lib.Math.Padic
