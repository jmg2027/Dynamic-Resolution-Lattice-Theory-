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

end E213.Lib.Math.Padic
