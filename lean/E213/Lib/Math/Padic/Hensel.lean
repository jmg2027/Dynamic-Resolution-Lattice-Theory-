import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Norm
import E213.Lib.Math.ModArith.ModBezoutInvariant
import E213.Meta.Tactic.NatHelper
/-!
# Real213-p-adic Hensel scaffold

Foundations for Hensel lifting in `ZpSeq p`.  The classical theorem
states: given a polynomial `f` with `f(a₀) ≡ 0 (mod p)` and
`f'(a₀) ≢ 0 (mod p)`, there is a unique p-adic integer `a` lifting
`a₀ ∈ F_p` such that `f(a) = 0` in `ℤ_p`.

The primary application in DRLT context: **multiplicative inverse**.
Given `x : ZpSeq p` with `(x.digits 0).val` coprime to `p`,
construct `y : ZpSeq p` such that `Zp.mul x y` is digit-by-digit
the all-one (`ZpSeq.one`) sequence — i.e., `x · y = 1` in ℤ_p.

The base case (digit 0 of y) uses the modular-arithmetic substrate
from `E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout`.
Subsequent digits are determined by the Hensel lift / FSM
correction at each level.

This module scaffolds the type signatures.  The full constructions
land here as the campaign progresses.
-/

namespace E213.Lib.Math.Padic

/-! ## Coprimality predicate

`Zp.unit0 x` — the digit-0 of `x` is nonzero.  This is the
necessary condition for `x` to be invertible in `ℤ_p` (and
sufficient when `p` is prime).
-/

/-- The unit predicate: digit-0 nonzero. -/
def Zp.unit0 {p : Nat} (x : ZpSeq p) : Prop :=
  (x.digits 0).val ≠ 0

/-- `unit0` is decidable. -/
instance Zp.unit0_decidable {p : Nat} (x : ZpSeq p) : Decidable (Zp.unit0 x) :=
  by unfold Zp.unit0; infer_instance

/-- For `ZpSeq.one`, `unit0` holds (when `1 < p`). -/
theorem Zp.unit0_one {p : Nat} (hp : 1 < p) : Zp.unit0 (ZpSeq.one p hp) := by
  show ((ZpSeq.one p hp).digits 0).val ≠ 0
  show (if (0 : Nat) = 0 then (1 : Nat) else 0) ≠ 0
  rw [if_pos rfl]
  exact fun h => Nat.noConfusion h

/-- `ZpSeq.zero` is not a unit. -/
theorem Zp.not_unit0_zero {p : Nat} (hp : 0 < p) :
    ¬ Zp.unit0 (ZpSeq.zero p hp) := by
  show ¬ ((ZpSeq.zero p hp).digits 0).val ≠ 0
  show ¬ (0 ≠ 0)
  exact fun h => h rfl

/-! ## Digit-0 inverse via Bezout

Given `x : ZpSeq p` with `(x.digits 0).val` coprime to `p`
(`gcd = 1`), the digit-0 of `x`'s inverse is the modular Bezout
inverse: a `Fin p` satisfying `(x.digits 0).val · y₀ ≡ 1 (mod p)`.

For prime `p`, `unit0 x` (digit-0 nonzero) is enough by Fermat;
for general `p`, we need the explicit gcd-1 hypothesis.

This is the base case of Hensel lifting for the multiplicative
inverse construction.
-/

/-- The digit-0 of `x`'s inverse — the modular Bezout witness
    for `(x.digits 0).val` mod `p`. -/
def Zp.invDigit0 (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ZpDigit p :=
  let mi := E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout
              (x.digits 0).val p hp h_gcd
  ⟨mi.inv, mi.inv_lt⟩

/-- The digit-0 inverse satisfies the modular identity
    `(x.digits 0).val · invDigit0 ≡ 1 (mod p)`. -/
theorem Zp.invDigit0_eq (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ((x.digits 0).val * (Zp.invDigit0 p hp x h_gcd).val) % p = 1 % p :=
  (E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout
    (x.digits 0).val p hp h_gcd).inv_eq

/-! ## Smoke applications -/

/-- Smoke: for `x : ZpSeq 5` with digit-0 = 2, the inverse digit
    is `3` (since `2 · 3 = 6 ≡ 1 (mod 5)`). -/
example (digits_rest : Nat → ZpDigit 5)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout 2 5).1 = 1) :
    (Zp.invDigit0 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else digits_rest k⟩
      h_gcd).val = 3 := by
  show (E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout
          2 5 (by decide) h_gcd).inv = 3
  rfl

/-! ## Level-1 inverse template

The "template" inverse: digit 0 is `invDigit0`, all other digits 0.
At level 1, this template multiplied by `x` truncates to `1 % p`
— the base case of the full Hensel lift.
-/

/-- The level-1 inverse template: only digit 0 is set (to the
    Bezout inverse); all higher digits are zero. -/
def Zp.invTemplate (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) : ZpSeq p where
  digits := fun k =>
    if k = 0 then Zp.invDigit0 p hp x h_gcd else ⟨0, hp⟩

/-- Digit-0 of the template equals `invDigit0`. -/
theorem Zp.invTemplate_digit_zero (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ((Zp.invTemplate p hp x h_gcd).digits 0).val
      = (Zp.invDigit0 p hp x h_gcd).val := by
  show (if (0 : Nat) = 0 then Zp.invDigit0 p hp x h_gcd
        else (⟨0, hp⟩ : Fin p)).val
      = (Zp.invDigit0 p hp x h_gcd).val
  rw [if_pos rfl]

/-- Higher digits of the template are zero. -/
theorem Zp.invTemplate_digit_succ (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (k : Nat) :
    ((Zp.invTemplate p hp x h_gcd).digits (k + 1)).val = 0 := by
  show (if (k + 1 : Nat) = 0 then Zp.invDigit0 p hp x h_gcd
        else (⟨0, hp⟩ : Fin p)).val = 0
  rw [if_neg (fun h => Nat.noConfusion h)]

end E213.Lib.Math.Padic
