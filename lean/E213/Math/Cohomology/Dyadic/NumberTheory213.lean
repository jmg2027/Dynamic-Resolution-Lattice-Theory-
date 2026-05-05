import E213.Math.Cohomology.Dyadic.ProductFSMPeriod
import E213.Math.Cohomology.Dyadic.Pisano.Predictor
import E213.Math.Cohomology.Dyadic.Pisano.Predictor7
import E213.Math.Cohomology.Dyadic.AlgebraicDegree
import E213.Math.Cohomology.Dyadic.Pell.ProperBridge

import E213.Math.Cohomology.Dyadic.ArithFSM
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod5
import E213.Math.Cohomology.Dyadic.Legendre.V213
/-!
# 213-native number theory — consolidated v1 + v2 + v3 master capstones

Bundles the three pillars of 213-native number theory:

  Step 1 — Lens Composition (CRT multiplicativity)
  Step 2 — Legendre Lens (branch oracle) + n-prime Pisano predictor
  Step 3 — Algebraic Degree Tower (ArithFSM₁ ⊂ ₂ ⊂ ₃)
  Step 4 (v3) — Discriminant-parametric Pell proper (D=5, D=8)

All within ≤ {propext, Quot.sound}.  No external Mathlib.

Three capstone theorems retained for backward compatibility:
  - `number_theory_213_capstone`     (v1, 4-prime Pisano evidence)
  - `number_theory_213_capstone_v2`  (v2, 7-prime Pisano evidence)
  - `number_theory_213_capstone_v3`  (v3, parametric discriminant)
-/

namespace E213.Math.Cohomology.Dyadic.NumberTheory213

open E213.Math.Cohomology.Dyadic.Legendre.V213 (legendre213)
open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5)


/-- ★★★★★★★★ v1: 213-native number theory edifice (4-prime). -/
theorem number_theory_213_capstone :
    -- Step 1: CRT multiplicativity (LCM stream closure)
    (∀ (bs1 bs2 : Nat → Bool) (p q : Nat),
      0 < p → 0 < q →
      (∀ k, bs1 (k + p) = bs1 k) → (∀ k, bs2 (k + q) = bs2 k) →
      ∀ (g : Bool → Bool → Bool) k,
        g (bs1 (k + Nat.lcm p q)) (bs2 (k + Nat.lcm p q))
        = g (bs1 k) (bs2 k))
    -- Step 2: Pisano predictor realises Pell period at all 4 primes
    ∧ ((∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
          = pellFSMmod3.bits k)
        ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
          = pellFSMmod5.bits k)
        ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
          = pellFSMmod7.bits k)
        ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
          = pellFSMmod11.bits k))
    -- Step 3: Algebraic degree tower (containments + concrete witnesses)
    ∧ ((∀ bs, HasDegree1 bs → HasDegree2 bs)
        ∧ (∀ bs, HasDegree2 bs → HasDegree3 bs)
        ∧ HasDegree2 pellFSMmod3.bits
        ∧ HasDegree3 tribFSMmod2.bits) :=
  ⟨bs_combined_periodic_lcm,
   pisano_predict_realises_pell,
   ⟨degree1_imp_degree2,
    degree2_imp_degree3,
    pellFSMmod3_has_degree2,
    tribFSMmod2_has_degree3⟩⟩

/-- ★★★★★★★★★ v2: with 7-prime Pisano predictor evidence. -/
theorem number_theory_213_capstone_v2 :
    -- Step 1: CRT (universal stream-level)
    (∀ (bs1 bs2 : Nat → Bool) (p q : Nat),
      0 < p → 0 < q →
      (∀ k, bs1 (k + p) = bs1 k) → (∀ k, bs2 (k + q) = bs2 k) →
      ∀ (g : Bool → Bool → Bool) k,
        g (bs1 (k + Nat.lcm p q)) (bs2 (k + Nat.lcm p q))
        = g (bs1 k) (bs2 k))
    -- Step 2: Pisano predictor at 7 primes
    ∧ ((∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
          = pellFSMmod3.bits k)
        ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
          = pellFSMmod5.bits k)
        ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
          = pellFSMmod7.bits k)
        ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
          = pellFSMmod11.bits k)
        ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
          = pellFSMmod13.bits k)
        ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide))
          = pellFSMmod17.bits k)
        ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by decide))
          = pellFSMmod19.bits k))
    -- Step 3: degree tower with concrete witnesses
    ∧ ((∀ bs, HasDegree1 bs → HasDegree2 bs)
        ∧ (∀ bs, HasDegree2 bs → HasDegree3 bs)
        ∧ HasDegree2 pellFSMmod3.bits
        ∧ HasDegree3 tribFSMmod2.bits) :=
  ⟨bs_combined_periodic_lcm,
   pisano_predict_realises_pell_7,
   ⟨degree1_imp_degree2,
    degree2_imp_degree3,
    pellFSMmod3_has_degree2,
    tribFSMmod2_has_degree3⟩⟩

/-- ★★★★★★★★★★ v3: discriminant-parametric (D=5, D=8). -/
theorem number_theory_213_capstone_v3 :
    -- Inherits v2 structure (Step 1)
    (∀ (bs1 bs2 : Nat → Bool) (p q : Nat),
      0 < p → 0 < q →
      (∀ k, bs1 (k + p) = bs1 k) → (∀ k, bs2 (k + q) = bs2 k) →
      ∀ (g : Bool → Bool → Bool) k,
        g (bs1 (k + Nat.lcm p q)) (bs2 (k + Nat.lcm p q))
        = g (bs1 k) (bs2 k))
    -- Pell proper (D=8) at 3 primes, both branches
    ∧ (legendre213 8 3 (by decide) = ⟨2, by decide⟩
        ∧ legendre213 8 5 (by decide) = ⟨2, by decide⟩
        ∧ legendre213 8 7 (by decide) = ⟨1, by decide⟩
        ∧ pisano_predict_proper 3 (by decide) = 8
        ∧ pisano_predict_proper 5 (by decide) = 12
        ∧ pisano_predict_proper 7 (by decide) = 6) := by
  refine ⟨bs_combined_periodic_lcm, ?_⟩
  refine ⟨legendre_8_mod_3, legendre_8_mod_5, legendre_8_mod_7,
          ?_, ?_, ?_⟩ <;> decide

end E213.Math.Cohomology.Dyadic.NumberTheory213