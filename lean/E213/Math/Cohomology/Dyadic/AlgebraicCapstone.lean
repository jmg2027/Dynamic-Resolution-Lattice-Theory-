import E213.Math.Cohomology.Dyadic.Pell.Capstone
import E213.Math.Cohomology.Dyadic.Trib.Capstone
import E213.Math.Cohomology.Dyadic.Trib.FSMmod3
import E213.Math.Cohomology.Dyadic.Trib.FSMmod5
import E213.Math.Cohomology.Dyadic.Fib.FSMmod3
import E213.Math.Cohomology.Dyadic.Fib.FSMmod5
import E213.Math.Cohomology.Dyadic.ArithFSM.V3Hardness

/-!
# Unified algebraic Tier 1 capstone

Bundles the quadratic (ArithFSM2/Pell) and cubic (ArithFSM3/Tribonacci)
closures into a single mega-theorem.

Both classes:
  • universal periodicity at bit AND signature level
  • polynomial period bound (5n² and 5n³)
  • aperiodic hardness (no transcendental escape)

This is the formal expression of "Tier 1 (algebraic) ⊊ Tier 2
(transcendental)" *via the K_{3,2}^{(2)} signature lens*, for
both quadratic and cubic algebraic classes.
-/

namespace E213.Math.Cohomology.Dyadic.AlgebraicCapstone
open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.V3 (tribFSMmod2 tribFSMmod2_bits_period_4)
open E213.Math.Cohomology.Dyadic.Trib.FSMmod3 (tribFSMmod3 tribFSMmod3_bits_period_13)
open E213.Math.Cohomology.Dyadic.Trib.FSMmod5 (tribFSMmod5 tribFSMmod5_bits_period_31)
open E213.Math.Cohomology.Dyadic.Fib.FSMmod3 (fibFSMmod3 fibFSMmod3_bits_period_8)
open E213.Math.Cohomology.Dyadic.Fib.FSMmod5 (fibFSMmod5 fibFSMmod5_bits_period_20)
open E213.Math.Cohomology.Dyadic.ConcretePellSig (pellFSMmod3_signature_period_4)
open E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)
open E213.Math.Cohomology.Dyadic.ArithFSM.Hardness (aperiodic_bits_imp_not_ArithFSM2)
open E213.Math.Cohomology.Dyadic.ArithFSM.V3 (tribFSMmod2_signature_period_4_from_1)
open E213.Math.Cohomology.Dyadic.ArithFSM.V3Bound (arithFSM3_signature_period_bound)
open E213.Math.Cohomology.Dyadic.ArithFSM.V3Hardness (aperiodic_bits_imp_not_ArithFSM3)

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)
open E213.Math.Cohomology.Dyadic.ArithFSM.V3 (ArithFSM3)
open E213.Math.Cohomology.Dyadic.Signature (signature)
open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3)


/-- ★★★★★★★★ Unified algebraic capstone: quadratic Pell + cubic
    Tribonacci both fully closed in the K_{3,2}^{(2)} signature
    lens with polynomial period bounds and Tier 2 hardness. -/
theorem algebraic_tier1_capstone :
    -- quadratic (Pell ArithFSM2) closure
    ((∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
      ∧ (∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k)
      ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM2 n),
          ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n)
            ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k)
      ∧ (∀ (bs : Nat → Bool),
          (∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) →
          ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n),
            ¬ (∀ k, m.bits k = bs k)))
    -- cubic (Tribonacci ArithFSM3) closure
    ∧ ((∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k)
        ∧ (∀ k, k ≥ 1 →
            signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k)
        ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM3 n),
            ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n * n)
              ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k)
        ∧ (∀ (bs : Nat → Bool),
            (∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) →
            ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM3 n),
              ¬ (∀ k, m.bits k = bs k))) :=
  ⟨⟨pellFSMmod3_bits_period_4,
    pellFSMmod3_signature_period_4,
    @arithFSM2_signature_period_bound,
    aperiodic_bits_imp_not_ArithFSM2⟩,
   ⟨tribFSMmod2_bits_period_4,
    tribFSMmod2_signature_period_4_from_1,
    @arithFSM3_signature_period_bound,
    aperiodic_bits_imp_not_ArithFSM3⟩⟩

end E213.Math.Cohomology.Dyadic.AlgebraicCapstone
