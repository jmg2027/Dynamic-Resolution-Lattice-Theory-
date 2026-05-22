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
  (FP2 phiFP2 fp2Pow fp2Frob fp2Mul fp2Mul_comm fp2Pow_succ
   phiFP2_pow_eq_fibLike phiFP2_mul_frob_phi_eq
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

/-- ★★ **phi^(p+1) = (-1, 0) under Frobenius FLT**:
    `phi^(p+1) = phi · phi^p = phi · σ(phi) = (p - 1, 0)`. -/
theorem phiFP2_pow_pp1_of_frob
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fp2Pow p (phiFP2 p) (p + 1) = (p - 1, 0) := by
  rw [fp2Pow_succ p (phiFP2 p) p, h_frob, fp2Mul_comm p (fp2Frob p (phiFP2 p)) (phiFP2 p)]
  exact phiFP2_mul_frob_phi_eq p hp hpo

/-- ★★★ **Frobenius-FLT-for-phi ⟹ F_{p+1} ≡ 0 mod p**.

    Via phi^(p+1) = (-1, 0) (above) + Binet at p+1.  PURE. -/
theorem fpp1_eq_zero_of_frob_phi
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fibFst (p + 1) % p = 0 := by
  have h_pp1 := phiFP2_pow_pp1_of_frob p hp hpo h_frob
  -- Apply Binet to phi^(p+1).
  have h_binet := phiFP2_pow_eq_fibLike p hp hpo (p + 1)
  rw [h_binet] at h_pp1
  -- h_pp1 : ((F_{p+1}·inv2 + F_p) % p, (F_{p+1}·inv2) % p) = (p-1, 0)
  -- Extract second:
  have h2 : ((fibLike (p + 1)).1 * inv2 p) % p = 0 :=
    congrArg Prod.snd h_pp1
  -- (fibLike (p+1)).1 = fibFst (p+1) (definitional)
  show fibFst (p + 1) % p = 0
  -- Use inv2_cancel_zero with X = fibFst (p+1)
  exact inv2_cancel_zero (fibFst (p + 1)) p hp hpo h2

/-- ★★★ **Frobenius-FLT-for-phi ⟹ F_{p-1} ≡ 1 mod p**.

    Combines `F_p ≡ -1` and `F_{p+1} ≡ 0` with the Fibonacci recurrence
    `F_{p+1} = F_p + F_{p-1}` (via `fibFst_recur` at index p-1).
    Uses `mod_cancel_right` to compare residues.  PURE. -/
theorem fpm1_eq_one_of_frob_phi
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fibFst (p - 1) % p = 1 := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  have hp_le : 1 ≤ p := Nat.le_of_lt hp
  have h_F_p : fibFst p % p = p - 1 := fp_eq_neg_one_of_frob_phi p hp hpo h_frob
  have h_F_pp1 : fibFst (p + 1) % p = 0 := fpp1_eq_zero_of_frob_phi p hp hpo h_frob
  -- Fibonacci recurrence: F_{p+1} = F_p + F_{p-1}.
  -- via fibFst_recur (p-1) : fibFst ((p-1) + 2) = fibFst ((p-1) + 1) + fibFst (p-1)
  -- with (p-1) + 1 = p, (p-1) + 2 = p + 1.
  have h_pm1_p1 : (p - 1) + 1 = p := sub_add_cancel hp_le
  have h_pm1_p2 : (p - 1) + 2 = p + 1 := by
    rw [show (p - 1) + 2 = ((p - 1) + 1) + 1 from rfl, h_pm1_p1]
  have h_F_pp1_eq : fibFst (p + 1) = fibFst p + fibFst (p - 1) := by
    rw [← h_pm1_p2, fibFst_recur (p - 1), h_pm1_p1]
  -- (F_p + F_{p-1}) % p = 0
  have h_zero : (fibFst p + fibFst (p - 1)) % p = 0 := by
    rw [← h_F_pp1_eq]; exact h_F_pp1
  -- Substitute F_p % p = p - 1 via add_mod_gen.
  rw [add_mod_gen (fibFst p) (fibFst (p - 1)) p] at h_zero
  rw [h_F_p] at h_zero
  -- h_zero : ((p - 1) + fibFst (p-1) % p) % p = 0
  -- Compare with ((p - 1) + 1) % p = 0:
  have h_compare : ((p - 1) + 1) % p = 0 := by
    rw [h_pm1_p1]; exact mod_self p
  -- Apply mod_cancel_right via comm:
  have h_lt_X : fibFst (p - 1) % p < p := Nat.mod_lt _ hp_pos
  have h_lt_1 : (1 : Nat) < p := hp
  -- Reorganize h_zero to (X + (p-1)) % p form via comm.
  have h_zero' : (fibFst (p - 1) % p + (p - 1)) % p = 0 := by
    rw [Nat.add_comm (fibFst (p - 1) % p) (p - 1)]; exact h_zero
  have h_compare' : (1 + (p - 1)) % p = 0 := by
    rw [Nat.add_comm 1 (p - 1)]; exact h_compare
  exact E213.Lib.Math.ModArith.ModBezoutInvariant.mod_cancel_right
    p _ _ (p - 1) hp_pos h_lt_X h_lt_1 (h_zero'.trans h_compare'.symm)

/-- ★★★★★ **Universal Phase 3.3 via Frobenius FLT on phi**.

    The structurally cleanest formulation: given Frobenius FLT on phi
    in 𝔽_{p²} (`phi^p = σ(phi)`) — which is a single equation
    decidable per prime by `decide` — the full Phase 3.3 matrix-order
    closure follows.

    Internal chain:
      1. h_frob ⟹ F_p ≡ -1 mod p (`fp_eq_neg_one_of_frob_phi`)
      2. h_frob ⟹ F_{p-1} ≡ 1 mod p (`fpm1_eq_one_of_frob_phi`)
      3. Apply `universal_phase_3_3` (Part 44).

    PURE.  This compresses the inert F-identities (two hypotheses
    in universal_phase_3_3) into a single Frobenius FLT hypothesis. -/
theorem universal_phase_3_3_via_frob
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    E213.Lib.Math.DyadicFSM.PellMatrix.pellCoeff p hp (p + 1)
      = E213.Lib.Math.DyadicFSM.PellMatrix.pellCoeff p hp 0 :=
  universal_phase_3_3 p hp
    (fp_eq_neg_one_of_frob_phi p hp hpo h_frob)
    (fpm1_eq_one_of_frob_phi p hp hpo h_frob)

/-! ## Per-prime smokes for `universal_phase_3_3_via_frob` -/

/-- Smoke at p=3: phi^3 = sigma(phi) decided by `decide`. -/
theorem universal_phase_3_3_via_frob_at_3 :
    E213.Lib.Math.DyadicFSM.PellMatrix.pellCoeff 3 (by decide) 4
      = E213.Lib.Math.DyadicFSM.PellMatrix.pellCoeff 3 (by decide) 0 :=
  universal_phase_3_3_via_frob 3 (by decide) (by decide) (by decide)

/-- Smoke at p=7: phi^7 = sigma(phi) decided by `decide`. -/
theorem universal_phase_3_3_via_frob_at_7 :
    E213.Lib.Math.DyadicFSM.PellMatrix.pellCoeff 7 (by decide) 8
      = E213.Lib.Math.DyadicFSM.PellMatrix.pellCoeff 7 (by decide) 0 :=
  universal_phase_3_3_via_frob 7 (by decide) (by decide) (by decide)

end E213.Lib.Math.DyadicFSM.UniversalPhase33
