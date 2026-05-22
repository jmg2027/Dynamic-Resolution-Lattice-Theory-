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

end E213.Lib.Math.Padic
