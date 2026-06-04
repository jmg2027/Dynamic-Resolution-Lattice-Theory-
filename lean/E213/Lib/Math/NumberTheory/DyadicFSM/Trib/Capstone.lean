import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3Hardness

import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3Bound
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3toBitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.BitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature
/-!
# Tribonacci ArithFSM3 family — capstone

Cubic-class capstone, parallel to `DyadicPellCapstone`.

Bundles 6 conjuncts:

1. Tribonacci mod 2: bit period 4 (universal)
2. Tribonacci mod 2: signature period 4 from step 1
3. ArithFSM3(n) ⊂ BitFSM(n³) bit-stream equivalence (universal)
4. ArithFSM3(n) signature period ≤ 5n³ (universal quantitative)
5. Tribonacci mod 2: explicit signature period bound 40
6. Aperiodic bs ⇒ no ArithFSM3(n) generates it (Tier 2 hardness)

All conjuncts PURE (`#print axioms tribonacci_capstone` returns
"does not depend on any axioms"; verified).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Trib.Capstone
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3 (tribFSMmod2 tribFSMmod2_bits_period_4 tribFSMmod2_signature_period_4_from_1)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3Bound (tribFSMmod2_signature_period_bound toBitFSM3_bits_eq arithFSM3_signature_period_bound)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3Hardness (aperiodic_bits_imp_not_ArithFSM3)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3toBitFSM

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)
open E213.Lib.Math.NumberTheory.DyadicFSM.BitFSM (BitFSM)


/-- ★★★★★★★ Tribonacci capstone: Tier 1 (cubic, Tribonacci-style)
    fully characterised in the K_{3,2}^{(2)} signature lens. -/
theorem tribonacci_capstone :
    -- bit periodicity
    (∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k)
    -- concrete signature periodicity (pre-period 1)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k)
    -- ArithFSM3(n) ⊂ BitFSM(n³) bit-stream equivalence
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) (k : Nat),
        (ArithFSM3.toBitFSM hn m).bits k = m.bits k)
    -- ArithFSM3(n) signature period ≤ 5n³
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM3 n),
        ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n * n)
          ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k)
    -- Tribonacci mod 2: explicit signature period bound 40
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 40
        ∧ ∀ k, k ≥ N →
          signature tribFSMmod2.bits (k + P) = signature tribFSMmod2.bits k)
    -- aperiodic ⇒ no ArithFSM3(n) (Tier 2 hardness)
    ∧ (∀ (bs : Nat → Bool),
        (∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) →
        ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM3 n),
          ¬ (∀ k, m.bits k = bs k)) :=
  ⟨tribFSMmod2_bits_period_4,
   tribFSMmod2_signature_period_4_from_1,
   @toBitFSM3_bits_eq,
   @arithFSM3_signature_period_bound,
   tribFSMmod2_signature_period_bound,
   aperiodic_bits_imp_not_ArithFSM3⟩

end E213.Lib.Math.NumberTheory.DyadicFSM.Trib.Capstone
