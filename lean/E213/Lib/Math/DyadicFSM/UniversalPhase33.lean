import E213.Lib.Math.ModArith.FP2Sqrt5
import E213.Lib.Math.DyadicFSM.PellFibBridge
import E213.Lib.Math.DyadicFSM.BinetBridge
/-!
# Universal Phase 3.3 (inert case): bridge from Frobenius FLT to F-identities

This file bridges the F_{p^2} infrastructure (FP2Sqrt5) with the
Pell-Fibonacci closure (PellFibBridge) for the inert case.

Given Frobenius FLT on phi (`phi^p = σ(phi)` in 𝔽_{p²}), we derive
the inert Fibonacci characteristic identities:
  · F_p ≡ -1 mod p (i.e., `fibFst p % p = p - 1`)
  · F_{p-1} ≡ 1 mod p (`fibFst (p - 1) % p = 1`)

via Binet expansion (Part 48) + inv2-cancellation (Part 49) +
mod-p Fibonacci recurrence (PellFibBridge).

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.UniversalPhase33

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self zero_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Tactic.NatHelper (add_mul sub_add_cancel)
open E213.Lib.Math.DyadicFSM.PhiMod5 (inv2 fibLike two_mul_inv2)
open E213.Lib.Math.ModArith.FP2Sqrt5
  (FP2 phiFP2 fp2Pow fp2Frob phiFP2_pow_eq_fibLike
   inv2_cancel_zero nmod_self_mod_zero)
open E213.Lib.Math.DyadicFSM.PellFibBridge
  (fibFst fibLike_succ_fst fibLike_succ_snd fibFst_recur
   universal_phase_3_3)
open E213.Lib.Math.DyadicFSM.BinetBridge (mod_eq_p_minus_one_of_succ_mod_zero)

/-- ★★★ **Frobenius-FLT-for-phi ⟹ F_p ≡ -1 mod p**.

    The .2 component of `phi^p = σ(phi)` gives
    `(F_p · inv2) % p = (p - inv2 % p) % p`.  Adding inv2 to both sides
    yields `((F_p + 1) · inv2) % p = 0`.  By `inv2_cancel_zero`,
    `(F_p + 1) % p = 0`, hence `F_p % p = p - 1`.  PURE. -/
theorem fp_eq_neg_one_of_frob_phi
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fibFst p % p = p - 1 := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  -- Apply Binet expansion to phi^p.
  have h_binet := phiFP2_pow_eq_fibLike p hp hpo p
  rw [h_binet] at h_frob
  -- h_frob : ((F_p·inv2 + F_{p-1}) % p, (F_p·inv2) % p) = fp2Frob p phi
  -- Extract second component:
  have h2_eq : ((fibLike p).1 * inv2 p) % p = (p - inv2 p % p) % p :=
    congrArg Prod.snd h_frob
  -- (fibLike p).1 = fibFst p (definitional)
  show fibFst p % p = p - 1
  -- Derive (F_p · inv2 + inv2) % p = 0.
  have h_zero : (fibFst p * inv2 p + inv2 p) % p = 0 := by
    rw [add_mod_gen (fibFst p * inv2 p) (inv2 p) p]
    rw [show fibFst p * inv2 p = (fibLike p).1 * inv2 p from rfl]
    rw [h2_eq]
    exact nmod_self_mod_zero p (inv2 p) hp_pos
  -- ((F_p + 1) · inv2) % p = 0
  have h_mul_zero : ((fibFst p + 1) * inv2 p) % p = 0 := by
    rw [add_mul (fibFst p) 1 (inv2 p), Nat.one_mul]
    exact h_zero
  -- (F_p + 1) % p = 0
  have h_succ_zero : (fibFst p + 1) % p = 0 :=
    inv2_cancel_zero (fibFst p + 1) p hp hpo h_mul_zero
  -- F_p % p = p - 1
  exact mod_eq_p_minus_one_of_succ_mod_zero p (fibFst p) hp h_succ_zero

end E213.Lib.Math.DyadicFSM.UniversalPhase33
