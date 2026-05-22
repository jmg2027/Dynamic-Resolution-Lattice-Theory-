import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Norm
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

end E213.Lib.Math.Padic
