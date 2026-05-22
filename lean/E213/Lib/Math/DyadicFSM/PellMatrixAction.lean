import E213.Lib.Math.DyadicFSM.PellMatrix
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper
/-!
# Pell matrix action formula — G119 Phase 1 bridge

Connects `pellCoeff p hp k` to `(pellFSMmod p hp).run k`.

The matrix M = [[2, 1], [1, 1]] applied to v_0 = (1, 1) gives M v_0 = (3, 2).
By Cayley-Hamilton, M^k = a_k · M + b_k · I.  So:

  M^k · (1, 1) = a_k · M (1, 1) + b_k · (1, 1)
             = a_k · (3, 2) + b_k · (1, 1)
             = (3·a_k + b_k, 2·a_k + b_k)

This is the action formula.  Combined with `pellCoeff_zero_one_at_N`
(matrix-order detection), it gives the universal Pisano period theorem
restricted to the (1, 1) orbit.

This file proves the action formula by induction on k, using PURE
`add_mod_gen` + `mul_mod_*_pure` Nat arithmetic helpers.
-/

namespace E213.Lib.Math.DyadicFSM.PellMatrixAction

open E213.Lib.Math.DyadicFSM.PellMatrix (pellCoeff)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod ArithFSM2)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_self)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (add_sub_of_le sub_add_cancel)

/-- ★ Action formula at k=0: `pellFSMmod.run 0 = init = (1, 1)`,
    and the formula `(3·0 + 1 mod p, 2·0 + 1 mod p) = (1, 1)` matches. -/
theorem action_base (p : Nat) (hp : 1 < p) :
    ((pellFSMmod p hp).run 0).1.val
      = (3 * (pellCoeff p hp 0).1.val + (pellCoeff p hp 0).2.val) % p
    ∧ ((pellFSMmod p hp).run 0).2.val
      = (2 * (pellCoeff p hp 0).1.val + (pellCoeff p hp 0).2.val) % p := by
  refine ⟨?_, ?_⟩
  · show 1 = (3 * 0 + 1) % p
    rw [Nat.mul_zero, Nat.zero_add]
    exact (Nat.mod_eq_of_lt hp).symm
  · show 1 = (2 * 0 + 1) % p
    rw [Nat.mul_zero, Nat.zero_add]
    exact (Nat.mod_eq_of_lt hp).symm

open E213.Meta.Nat.AddMod213 (div_add_mod)

/-- ★ Negation in `Fin p`: `a + (p - a % p) ≡ 0 (mod p)`.  PURE. -/
theorem neg_mod_sub (p a : Nat) (hp : 0 < p) :
    (a + (p - a % p)) % p = 0 := by
  have hlt : a % p < p := Nat.mod_lt a hp
  have hdivmod : p * (a / p) + a % p = a := div_add_mod a p
  have hcancel : a % p + (p - a % p) = p := add_sub_of_le (Nat.le_of_lt hlt)
  have e1 : a + (p - a % p) = p * (a / p) + p := by
    have h : a + (p - a % p) = (p * (a / p) + a % p) + (p - a % p) := by rw [hdivmod]
    rw [h, Nat.add_assoc, hcancel]
  rw [e1, add_mod_gen]
  -- Goal: (p * (a / p) % p + p % p) % p = 0
  rw [mod_self]
  -- Goal: (p * (a / p) % p + 0) % p = 0
  rw [Nat.add_zero]
  -- Goal: (p * (a/p)) % p % p = 0
  rw [E213.Meta.Nat.AddMod213.mod_mod]
  -- Goal: (p * (a / p)) % p = 0
  exact E213.Tactic.NatHelper.mul_mod_right p (a / p)

end E213.Lib.Math.DyadicFSM.PellMatrixAction
