import E213.Lib.Math.NumberSystems.Padic.Arith
import E213.Lib.Math.NumberSystems.Padic.Norm
import E213.Lib.Math.NumberSystems.Padic.Hensel
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.NatRing213
/-!
# Real213-p-adic Field (ℚ_p localization)

A p-adic number `ℚ_p` is a p-adic integer divided by some power
of `p`.  Concretely:

  ℚ_p = ℤ_p[1/p] = { (num, shift) : ZpSeq p × ℕ }

where the pair `(num, shift)` represents `num · p^(-shift)`.
Equivalently: an element of `ℚ_p` is a `ZpSeq p` plus a shift
recording how many factors of `p` to extract from the denominator.

This file scaffolds the type + basic equality predicate.  Full
arithmetic operations and field structure land in subsequent
commits as the campaign progresses.
-/

namespace E213.Lib.Math.NumberSystems.Padic

/-- A p-adic number: a `ZpSeq p` numerator with a denominator shift.
    The pair `⟨num, shift⟩` represents `num · p^(-shift)` — i.e.,
    `num`'s digit-`k` contributes to the position `p^(k - shift)`. -/
structure QpSeq (p : Nat) where
  num : ZpSeq p
  shift : Nat

/-- Embed a p-adic integer as a p-adic number with shift 0. -/
def QpSeq.ofZp (p : Nat) (x : ZpSeq p) : QpSeq p where
  num := x
  shift := 0

/-- The p-adic zero in `ℚ_p` (numerator zero, any shift; canonical
    shift 0). -/
def QpSeq.zero (p : Nat) (hp : 0 < p) : QpSeq p :=
  QpSeq.ofZp p (ZpSeq.zero p hp)

/-- The p-adic one in `ℚ_p`. -/
def QpSeq.one (p : Nat) (hp : 1 < p) : QpSeq p :=
  QpSeq.ofZp p (ZpSeq.one p hp)

/-- Shift unfolding for `ofZp`. -/
theorem QpSeq.ofZp_shift (p : Nat) (x : ZpSeq p) :
    (QpSeq.ofZp p x).shift = 0 := rfl

/-- Numerator unfolding for `ofZp`. -/
theorem QpSeq.ofZp_num (p : Nat) (x : ZpSeq p) :
    (QpSeq.ofZp p x).num = x := rfl

/-! ## Multiplication on ℚ_p

For `(num₁, s₁) · (num₂, s₂)` representing
`(num₁ / p^s₁) · (num₂ / p^s₂) = (num₁ · num₂) / p^(s₁+s₂)`,
define:
    `(num₁, s₁) · (num₂, s₂) := ⟨Zp.mul num₁ num₂, s₁ + s₂⟩`.

The shift accumulates additively under multiplication.
-/

/-- Multiplication on `QpSeq`. -/
def QpSeq.mul (p : Nat) (hp : 0 < p) (a b : QpSeq p) : QpSeq p where
  num := Zp.mul p hp a.num b.num
  shift := a.shift + b.shift

/-- The shift of a product is the sum of shifts. -/
theorem QpSeq.mul_shift (p : Nat) (hp : 0 < p) (a b : QpSeq p) :
    (QpSeq.mul p hp a b).shift = a.shift + b.shift := rfl

/-- The numerator of a product is the product of numerators
    (in `ZpSeq`). -/
theorem QpSeq.mul_num (p : Nat) (hp : 0 < p) (a b : QpSeq p) :
    (QpSeq.mul p hp a b).num = Zp.mul p hp a.num b.num := rfl

/-- Embedding respects multiplication: `ofZp (x · y) = ofZp x · ofZp y`. -/
theorem QpSeq.ofZp_mul (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    QpSeq.mul p hp (QpSeq.ofZp p x) (QpSeq.ofZp p y)
      = QpSeq.ofZp p (Zp.mul p hp x y) := rfl

/-- Smoke: `1 · 1 = 1` in ℚ_p (digit-0 of the resulting numerator). -/
theorem QpSeq.smoke_mul_one_one_5 :
    ((QpSeq.mul 5 (by decide)
        (QpSeq.one 5 (by decide))
        (QpSeq.one 5 (by decide))).num.digits 0).val = 1 := rfl

/-! ## Addition on ℚ_p (same-shift)

When both operands have the same shift `s`, addition is just
numerator-addition (via `Zp.add`) with the shift preserved:
    `(num₁, s) + (num₂, s) := ⟨Zp.add num₁ num₂, s⟩`.

The general case (unequal shifts) needs a `Zp.shiftLeft`
operation; we handle it in a subsequent commit.
-/

/-- Addition on `QpSeq` when shifts agree.  -/
def QpSeq.addAligned (p : Nat) (hp : 0 < p) (a b : QpSeq p)
    (_h : a.shift = b.shift) : QpSeq p where
  num := Zp.add p hp a.num b.num
  shift := a.shift

/-- Numerator of an aligned sum is the underlying `Zp.add`. -/
theorem QpSeq.addAligned_num (p : Nat) (hp : 0 < p) (a b : QpSeq p)
    (h : a.shift = b.shift) :
    (QpSeq.addAligned p hp a b h).num = Zp.add p hp a.num b.num := rfl

/-- Shift of an aligned sum is the common shift. -/
theorem QpSeq.addAligned_shift (p : Nat) (hp : 0 < p) (a b : QpSeq p)
    (h : a.shift = b.shift) :
    (QpSeq.addAligned p hp a b h).shift = a.shift := rfl

/-- Embedding respects same-shift addition: aligned shifts are 0. -/
theorem QpSeq.ofZp_add (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    QpSeq.addAligned p hp (QpSeq.ofZp p x) (QpSeq.ofZp p y) rfl
      = QpSeq.ofZp p (Zp.add p hp x y) := rfl

/-! ## Addition on ℚ_p (general shifts)

When shifts differ, align them by shifting the lower-shift
numerator left.  Specifically: let `s = max a.shift b.shift`;
each numerator is shifted left by `s - own.shift` (which is 0
for the higher-shift operand, identity-shift) before adding.
-/

/-- General addition on `QpSeq`: align shifts via `Zp.shiftLeft`. -/
def QpSeq.add (p : Nat) (hp : 0 < p) (a b : QpSeq p) : QpSeq p :=
  let s := Nat.max a.shift b.shift
  ⟨Zp.add p hp
      (Zp.shiftLeft p hp (s - a.shift) a.num)
      (Zp.shiftLeft p hp (s - b.shift) b.num),
   s⟩

/-- The shift of the result of `add` is `max` of the input shifts. -/
theorem QpSeq.add_shift (p : Nat) (hp : 0 < p) (a b : QpSeq p) :
    (QpSeq.add p hp a b).shift = Nat.max a.shift b.shift := rfl

/-- `ofZp` embeds: shift-0 additions go through unchanged. -/
theorem QpSeq.add_ofZp (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    QpSeq.add p hp (QpSeq.ofZp p x) (QpSeq.ofZp p y)
      = QpSeq.ofZp p (Zp.add p hp
                        (Zp.shiftLeft p hp 0 x)
                        (Zp.shiftLeft p hp 0 y)) := rfl

/-! ## Negation on ℚ_p

Negation preserves the shift and negates the numerator (via `Zp.neg`).
-/

/-- Negation on `QpSeq`. -/
def QpSeq.neg (p : Nat) (hp : 1 < p) (a : QpSeq p) : QpSeq p where
  num := Zp.neg p hp a.num
  shift := a.shift

/-- The shift of `-a` matches `a`. -/
theorem QpSeq.neg_shift (p : Nat) (hp : 1 < p) (a : QpSeq p) :
    (QpSeq.neg p hp a).shift = a.shift := rfl

/-- The numerator of `-a` is `Zp.neg` of `a`'s numerator. -/
theorem QpSeq.neg_num (p : Nat) (hp : 1 < p) (a : QpSeq p) :
    (QpSeq.neg p hp a).num = Zp.neg p hp a.num := rfl

/-- Smoke: digit-0 of `-1` in 5-adic ℚ_p is `4` (= 5 - 1). -/
theorem QpSeq.smoke_neg_one_5_d0 :
    ((QpSeq.neg 5 (by decide) (QpSeq.one 5 (by decide))).num.digits 0).val
      = 4 := rfl

/-! ## Subtraction on ℚ_p

Defined as `a - b := a + (-b)`.
-/

/-- Subtraction on `QpSeq`. -/
def QpSeq.sub (p : Nat) (hp : 1 < p) (a b : QpSeq p) : QpSeq p :=
  QpSeq.add p (Nat.lt_of_succ_lt hp) a (QpSeq.neg p hp b)

/-- Shift of `a - b` equals shift of `a + (-b)`. -/
theorem QpSeq.sub_shift (p : Nat) (hp : 1 < p) (a b : QpSeq p) :
    (QpSeq.sub p hp a b).shift = Nat.max a.shift b.shift := rfl

/-- Smoke: subtraction with same shift on `1 - 1` digit-0 — depends
    on the carry behavior of `Zp.add one (Zp.neg one)`.  Verified
    structurally: numerator-level matches `(1) + (-1)`, which (per
    the underlying \`add_neg_one_one_trunc_succ\`) trims to 0 in
    truncation. -/
theorem QpSeq.smoke_sub_one_one_shift_5 :
    (QpSeq.sub 5 (by decide) (QpSeq.one 5 (by decide))
       (QpSeq.one 5 (by decide))).shift = 0 := rfl

/-! ## ℕ embedding ℚ_p

Any natural number `n` embeds into ℚ_p via the base-p expansion
of `n` (shift 0).
-/

/-- Embed `ℕ` into `ℚ_p` (shift 0). -/
def QpSeq.ofNat (p : Nat) (hp : 0 < p) (n : Nat) : QpSeq p :=
  QpSeq.ofZp p (ZpSeq.digits_of_nat p hp n)

/-- Digit unfolding: by definition. -/
theorem QpSeq.ofNat_digit (p : Nat) (hp : 0 < p) (n k : Nat) :
    ((QpSeq.ofNat p hp n).num.digits k).val = (n / p^k) % p := rfl

/-- Shift of `ofNat` is always 0. -/
theorem QpSeq.ofNat_shift (p : Nat) (hp : 0 < p) (n : Nat) :
    (QpSeq.ofNat p hp n).shift = 0 := rfl

/-- Smoke: `7 ↪ ℚ_2` has digit-0 = 1, digit-1 = 1, digit-2 = 1
    (since 7 = 111₂). -/
theorem QpSeq.smoke_ofNat_7_2_d0 :
    ((QpSeq.ofNat 2 (by decide) 7).num.digits 0).val = 1 := rfl

theorem QpSeq.smoke_ofNat_7_2_d2 :
    ((QpSeq.ofNat 2 (by decide) 7).num.digits 2).val = 1 := rfl

/-! ## Multiplicative inverse on ℚ_p

For `a : QpSeq p` representing `a.num · p^(-a.shift)` with
`a.num.digits 0` coprime to `p`, the inverse is
    `1/a = (1/a.num) · p^(a.shift) = invFull(a.num) · p^(a.shift)`.

As a `QpSeq`, this is `(Zp.shiftLeft a.shift (invFull a.num), 0)`
— numerator is the shifted full p-adic inverse, shift is 0.
-/

/-- Multiplicative inverse on `QpSeq` (requires unit numerator). -/
def QpSeq.inv (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (a.num.digits 0).val p).1 = 1) : QpSeq p where
  num := Zp.shiftLeft p (Nat.lt_of_succ_lt hp) a.shift
            (Zp.invFull p (Nat.lt_of_succ_lt hp) a.num h_gcd)
  shift := 0

/-- The shift of `QpSeq.inv` is always 0 (inverse is "integer-shaped"). -/
theorem QpSeq.inv_shift (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (a.num.digits 0).val p).1 = 1) :
    (QpSeq.inv p hp a h_gcd).shift = 0 := rfl

/-- The numerator unfolding for `QpSeq.inv`. -/
theorem QpSeq.inv_num (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (a.num.digits 0).val p).1 = 1) :
    (QpSeq.inv p hp a h_gcd).num
      = Zp.shiftLeft p (Nat.lt_of_succ_lt hp) a.shift
            (Zp.invFull p (Nat.lt_of_succ_lt hp) a.num h_gcd) := rfl

/-! ## Division on ℚ_p

Division `a / b` defined as `a · b⁻¹`, requiring `b.num.digits 0`
coprime to `p` (so `b⁻¹` exists).
-/

/-- Division on `QpSeq` (requires unit denominator). -/
def QpSeq.div (p : Nat) (hp : 1 < p) (a b : QpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (b.num.digits 0).val p).1 = 1) : QpSeq p :=
  QpSeq.mul p (Nat.lt_of_succ_lt hp) a (QpSeq.inv p hp b h_gcd)

/-- The shift of `a / b` equals `a.shift` (since `inv` has shift 0). -/
theorem QpSeq.div_shift (p : Nat) (hp : 1 < p) (a b : QpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (b.num.digits 0).val p).1 = 1) :
    (QpSeq.div p hp a b h_gcd).shift = a.shift := by
  show a.shift + (QpSeq.inv p hp b h_gcd).shift = a.shift
  rw [QpSeq.inv_shift, Nat.add_zero]

/-- The numerator of `a / b` is `a.num · b.num⁻¹`. -/
theorem QpSeq.div_num (p : Nat) (hp : 1 < p) (a b : QpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (b.num.digits 0).val p).1 = 1) :
    (QpSeq.div p hp a b h_gcd).num
      = Zp.mul p (Nat.lt_of_succ_lt hp) a.num (QpSeq.inv p hp b h_gcd).num := rfl

/-! ## General division on ℚ_p (non-unit denominator)

`QpSeq.inv` / `QpSeq.div` require the denominator's numerator to be a
**unit** (digit-0 coprime to `p`, valuation 0).  A general nonzero
`b.num` factors as `p^v · u` with `u` a unit (`v = v_p(b.num)` the
valuation, `u = shiftRight v b.num`).  Then

  `1/b = 1/(b.num · p^(−b.shift)) = u⁻¹ · p^(b.shift − v)`,

representable in `ℚ_p` because the shift carries the `p^(b.shift − v)`
factor.  In `QpSeq` coordinates (`num · p^(−shift)`), exactly one of
the Nat-truncated differences `b.shift − v`, `v − b.shift` is nonzero:

  `invGeneral b v = ⟨shiftLeft (b.shift − v) (invFull u), v − b.shift⟩`.

At `v = 0` (unit numerator) this reduces to `QpSeq.inv`
(`invGeneral_unit_eq_inv`), so it is a genuine generalisation.  The
caller supplies the valuation `v` and the unit witness on `u`
(the first non-zero digit cannot be searched purely on an arbitrary
sequence — `b.num` could be `0`, valuation `∞`). -/

/-- **General multiplicative inverse** on `QpSeq`: invert a denominator
    of arbitrary valuation `v`.  `h_gcd` witnesses that the unit part
    `u = shiftRight v a.num` has digit-0 coprime to `p`. -/
def QpSeq.invGeneral (p : Nat) (hp : 1 < p) (a : QpSeq p) (v : Nat)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight p v a.num).digits 0).val p).1 = 1) : QpSeq p where
  num := Zp.shiftLeft p (Nat.lt_of_succ_lt hp) (a.shift - v)
            (Zp.invFull p (Nat.lt_of_succ_lt hp) (Zp.shiftRight p v a.num) h_gcd)
  shift := v - a.shift

/-- Shift of `invGeneral` is `v − a.shift` (Nat-truncated). -/
theorem QpSeq.invGeneral_shift (p : Nat) (hp : 1 < p) (a : QpSeq p) (v : Nat)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight p v a.num).digits 0).val p).1 = 1) :
    (QpSeq.invGeneral p hp a v h_gcd).shift = v - a.shift := rfl

/-- Numerator unfolding for `invGeneral`. -/
theorem QpSeq.invGeneral_num (p : Nat) (hp : 1 < p) (a : QpSeq p) (v : Nat)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight p v a.num).digits 0).val p).1 = 1) :
    (QpSeq.invGeneral p hp a v h_gcd).num
      = Zp.shiftLeft p (Nat.lt_of_succ_lt hp) (a.shift - v)
          (Zp.invFull p (Nat.lt_of_succ_lt hp) (Zp.shiftRight p v a.num) h_gcd) := rfl

/-- **Consistency**: at valuation `v = 0` (unit numerator) `invGeneral`
    equals the unit-only `QpSeq.inv`.  `shiftRight 0` is the identity
    on digit-0 and `a.shift − 0 = a.shift`, `0 − a.shift = 0`. -/
theorem QpSeq.invGeneral_unit_eq_inv (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (h_gcd0 : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight p 0 a.num).digits 0).val p).1 = 1)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (a.num.digits 0).val p).1 = 1) :
    (QpSeq.invGeneral p hp a 0 h_gcd0).num.digits
      = (QpSeq.inv p hp a h_gcd).num.digits :=
  -- `shiftRight 0 a.num ≡ a.num` (since `j + 0 ≡ j`) and `a.shift − 0 ≡ a.shift`;
  -- the `h_gcd` proofs are proof-irrelevant, so the two terms are definitionally equal.
  rfl

/-- **General division** `a / b` for arbitrary-valuation denominator:
    `a · invGeneral b v`. -/
def QpSeq.divGeneral (p : Nat) (hp : 1 < p) (a b : QpSeq p) (v : Nat)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight p v b.num).digits 0).val p).1 = 1) : QpSeq p :=
  QpSeq.mul p (Nat.lt_of_succ_lt hp) a (QpSeq.invGeneral p hp b v h_gcd)

/-- Shift of `divGeneral`: `a.shift + (v − b.shift)`. -/
theorem QpSeq.divGeneral_shift (p : Nat) (hp : 1 < p) (a b : QpSeq p) (v : Nat)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight p v b.num).digits 0).val p).1 = 1) :
    (QpSeq.divGeneral p hp a b v h_gcd).shift = a.shift + (v - b.shift) := rfl

/-- Smoke: invert `p = 5` in `ℚ_5`.  `5 = p^1 · 1` has valuation 1 and
    unit part `1`, so `1/5 = p^(−1)`: `invGeneral` returns shift `1`
    and numerator digit-0 `= 1` (the inverse of the unit `1`). -/
theorem QpSeq.smoke_invGeneral_p_5_shift
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout 1 5).1 = 1) :
    (QpSeq.invGeneral 5 (by decide)
      (QpSeq.ofNat 5 (by decide) 5) 1 h_gcd).shift = 1 := rfl

/-- Smoke: the unit part of `5 ∈ ℤ_5` (after dropping valuation 1) has
    digit-0 `= 1` — confirming `5 = p · 1`. -/
theorem QpSeq.smoke_shiftRight_5_unit_digit :
    ((Zp.shiftRight 5 1 (ZpSeq.digits_of_nat 5 (by decide) 5)).digits 0).val = 1 := rfl

/-! ## General-division correctness

`invGeneral (ofZp y) v` represents `u⁻¹ · p^(−v)` (numerator `invFull u`,
shift `v`), where `u = shiftRight v y` is the unit part of a
valuation-`≥v` `y`.  The ℚ_p value of `y · (1/y)` is therefore
`(y · u⁻¹) · p^(−v)`, so correctness is the **numerator identity**
`y · u⁻¹ ≡ p^v` at every truncation: the `p^v` and the shift `p^(−v)`
cancel to value `1`.  `div_general_value` proves exactly this.

Two pure helpers do the shift bookkeeping:
`mul_mod_mul_left_pure` factors a power out of a modulus
(`(p^v · Y) % p^(v+m) = p^v · (Y % p^m)`) and `trunc_add_mod` says a
higher truncation reduces to a lower one mod the lower power
(`x.trunc (b+c) % p^b = x.trunc b`). -/

/-- PURE Nat: `(a · b) % (a · c) = a · (b % c)` (factor a common left
    multiple out of a modulus).  ∅-axiom replacement for the propext-
    tainted `Nat.mul_mod_mul_left`. -/
private theorem mul_mod_mul_left_pure (a b c : Nat) (hc : 0 < c) :
    (a * b) % (a * c) = a * (b % c) := by
  have hdm : c * (b / c) + b % c = b := E213.Meta.Nat.AddMod213.div_add_mod b c
  have key : a * (b % c) + (b / c) * (a * c) = a * b := by
    rw [Nat.mul_comm (b / c) (a * c), E213.Tactic.NatHelper.mul_assoc a c (b / c),
        ← Nat.mul_add, Nat.add_comm (b % c) (c * (b / c)), hdm]
  rw [← key, E213.Tactic.NatHelper.add_mul_mod_self_pure (a * (b % c)) (a * c) (b / c)]
  cases a with
  | zero => rw [Nat.zero_mul, Nat.zero_mul]
  | succ k =>
    exact Nat.mod_eq_of_lt
      (E213.Meta.Nat.NatRing213.nat_mul_lt_mul_left (Nat.succ_pos k) (Nat.mod_lt b hc))

/-- A truncation reduces mod a lower power: `x.trunc (b + c) % p^b = x.trunc b`.
    The higher digits sit at positions `≥ b`, contributing `0` mod `p^b`. -/
private theorem trunc_add_mod (p : Nat) (hp : 0 < p) (x : ZpSeq p) (b : Nat) :
    ∀ c, x.trunc (b + c) % p^b = x.trunc b
  | 0 => by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow hp x b)
  | c + 1 => by
    show (x.trunc (b + c) + (x.digits (b + c)).val * p^(b + c)) % p^b = x.trunc b
    have hrw : (x.digits (b + c)).val * p^(b + c)
             = (x.digits (b + c)).val * p^c * p^b := by
      rw [E213.Meta.Nat.PureNat.pow_add p b c, Nat.mul_comm (p^b) (p^c),
          ← E213.Tactic.NatHelper.mul_assoc (x.digits (b + c)).val (p^c) (p^b)]
    rw [hrw, E213.Tactic.NatHelper.add_mul_mod_self_pure
          (x.trunc (b + c)) (p^b) ((x.digits (b + c)).val * p^c)]
    exact trunc_add_mod p hp x b c

/-- **General-division correctness** (numerator identity): for `y` of
    valuation `≥ v` (`hlow`) with unit part `u = shiftRight v y` (`h_gcd`),
    `y · u⁻¹ ≡ p^v` at every truncation.  Since `1/y = u⁻¹ · p^(−v)`
    (`invGeneral (ofZp y) v`), this is `y · (1/y) ≡ 1` in `ℚ_p` with the
    `p^v` matched by the shift `p^(−v)`. -/
theorem Zp.div_general_value (p : Nat) (hp : 1 < p) (y : ZpSeq p) (v : Nat)
    (hlow : ∀ j, j < v → (y.digits j).val = 0)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight p v y).digits 0).val p).1 = 1) (n : Nat) :
    (Zp.mul p (Nat.lt_of_succ_lt hp) y
      (Zp.invFull p (Nat.lt_of_succ_lt hp) (Zp.shiftRight p v y) h_gcd)).trunc (v + (n + 1))
      = (Zp.shiftLeft p (Nat.lt_of_succ_lt hp) v (ZpSeq.one p hp)).trunc (v + (n + 1)) := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  have hinner : ((Zp.shiftRight p v y).trunc (n + 1)
      * (Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd).trunc (v + (n + 1))) % p^(n + 1) = 1 := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure ((Zp.shiftRight p v y).trunc (n + 1))
          ((Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd).trunc (v + (n + 1))) (p^(n + 1))]
    rw [show (Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd).trunc (v + (n + 1)) % p^(n + 1)
          = (Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd).trunc (n + 1) from by
        rw [Nat.add_comm v (n + 1)]
        exact trunc_add_mod p hp' (Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd) (n + 1) v]
    rw [← Zp.mul_trunc p hp' (Zp.shiftRight p v y)
          (Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd) (n + 1)]
    exact Zp.mul_invFull_correct p hp (Zp.shiftRight p v y) h_gcd n
  rw [Zp.shiftLeft_trunc_above p hp' v (ZpSeq.one p hp) (n + 1),
      ZpSeq.trunc_one_succ p hp n, Nat.mul_one]
  rw [Zp.mul_trunc p hp' y (Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd) (v + (n + 1))]
  rw [show y.trunc (v + (n + 1)) = p^v * (Zp.shiftRight p v y).trunc (n + 1) from by
        rw [← Zp.shiftLeft_shiftRight_trunc_of_low_zero p hp' v y hlow (v + (n + 1))]
        exact Zp.shiftLeft_trunc_above p hp' v (Zp.shiftRight p v y) (n + 1)]
  rw [E213.Tactic.NatHelper.mul_assoc (p^v) ((Zp.shiftRight p v y).trunc (n + 1))
        ((Zp.invFull p hp' (Zp.shiftRight p v y) h_gcd).trunc (v + (n + 1)))]
  rw [show p^(v + (n + 1)) = p^v * p^(n + 1) from E213.Meta.Nat.PureNat.pow_add p v (n + 1)]
  rw [mul_mod_mul_left_pure (p^v) _ (p^(n + 1)) (Nat.pos_pow_of_pos (n + 1) hp')]
  rw [hinner, Nat.mul_one]

/-- Smoke: `5 · (1/5) ≡ 1` in `ℚ_5`.  `y = 5` has valuation 1 and unit
    part `1`, so `5 · 1⁻¹ ≡ 5¹` (= `shiftLeft 1 one`) — the numerator
    side of value `1`. -/
theorem Zp.smoke_div_general_value_5
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              ((Zp.shiftRight 5 1 (ZpSeq.digits_of_nat 5 (by decide) 5)).digits 0).val 5).1 = 1) :
    (Zp.mul 5 (by decide) (ZpSeq.digits_of_nat 5 (by decide) 5)
       (Zp.invFull 5 (by decide)
         (Zp.shiftRight 5 1 (ZpSeq.digits_of_nat 5 (by decide) 5)) h_gcd)).trunc 2
      = (Zp.shiftLeft 5 (by decide) 1 (ZpSeq.one 5 (by decide))).trunc 2 :=
  Zp.div_general_value 5 (by decide) (ZpSeq.digits_of_nat 5 (by decide) 5) 1
    (fun j hj => by
      cases j with
      | zero => decide
      | succ k => exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero k)) h_gcd 0

/-! ## Square root on ℚ_p

For `a = (num, shift)`, the square root satisfies
`sqrt(a) = (sqrtFull(num), shift / 2)`.  This requires the shift
to be **even**: in p-adic terms, `√p` does not exist in `ℚ_p`,
so we only define sqrt when `shift = 2 · k` for some `k`.

The shift-even hypothesis is taken as `a.shift = 2 * (a.shift / 2)`
— a clean PURE statement equivalent to `a.shift % 2 = 0`.
-/

/-- Square root on `QpSeq` (requires sqrt base for numerator
    and even shift). -/
def QpSeq.sqrt (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (sb : Zp.SqrtBase p a.num)
    (_heven : a.shift = 2 * (a.shift / 2)) : QpSeq p where
  num := Zp.sqrtFull p (Nat.lt_of_succ_lt hp) a.num sb
  shift := a.shift / 2

/-- Shift of `QpSeq.sqrt` is `a.shift / 2`. -/
theorem QpSeq.sqrt_shift (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (sb : Zp.SqrtBase p a.num)
    (heven : a.shift = 2 * (a.shift / 2)) :
    (QpSeq.sqrt p hp a sb heven).shift = a.shift / 2 := rfl

/-- Numerator of `QpSeq.sqrt` is `Zp.sqrtFull a.num`. -/
theorem QpSeq.sqrt_num (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (sb : Zp.SqrtBase p a.num)
    (heven : a.shift = 2 * (a.shift / 2)) :
    (QpSeq.sqrt p hp a sb heven).num
      = Zp.sqrtFull p (Nat.lt_of_succ_lt hp) a.num sb := rfl

/-- The shift of `sqrt² = sqrt · sqrt` matches `a.shift` via the
    even-shift hypothesis. -/
theorem QpSeq.sqr_sqrt_shift (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (sb : Zp.SqrtBase p a.num)
    (heven : a.shift = 2 * (a.shift / 2)) :
    (QpSeq.mul p (Nat.lt_of_succ_lt hp)
      (QpSeq.sqrt p hp a sb heven)
      (QpSeq.sqrt p hp a sb heven)).shift = a.shift := by
  show a.shift / 2 + a.shift / 2 = a.shift
  rw [show a.shift / 2 + a.shift / 2 = 2 * (a.shift / 2) by
        rw [Nat.two_mul]]
  exact heven.symm

/-- **ℚ_p sqrt correctness** (numerator part):
    `(sqrt a)² .num ≡ a.num (mod p^(n+1))` for all `n`. -/
theorem QpSeq.sqr_sqrt_num_correct (p : Nat) (hp : 1 < p) (a : QpSeq p)
    (sb : Zp.SqrtBase p a.num)
    (heven : a.shift = 2 * (a.shift / 2)) (n : Nat) :
    ((QpSeq.mul p (Nat.lt_of_succ_lt hp)
      (QpSeq.sqrt p hp a sb heven)
      (QpSeq.sqrt p hp a sb heven)).num).trunc (n + 1)
      = a.num.trunc (n + 1) :=
  Zp.sqr_sqrtFull_correct p hp a.num sb n

end E213.Lib.Math.NumberSystems.Padic
