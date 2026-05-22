import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Norm
import E213.Meta.Tactic.NatHelper
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

namespace E213.Lib.Math.Padic

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

end E213.Lib.Math.Padic
