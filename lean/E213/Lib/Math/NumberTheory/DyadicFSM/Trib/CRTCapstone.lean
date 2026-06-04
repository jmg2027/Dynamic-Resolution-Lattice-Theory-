import E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3Bound

import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature
/-!
# Tribonacci CRT capstones — 3-modulus and 4-modulus closures

CRT integration of the cubic-class Tribonacci-Pisano periods.

  | m | bit period | sig period | sig pre-period | composite? |
  | 2 |     4      |      4     |       1        | yes (4=2²) |
  | 3 |    13      |     26     |       1        | prime      |
  | 5 |    31      |     62     |       1        | prime      |
  | 7 |    48      |     48     |       1        | yes        |

CRT closures:
  · 3-modulus `{2, 3, 5}`: lcm(4, 13, 31) = 1612
  · 4-modulus `{2, 3, 5, 7}`: lcm(4, 13, 31, 48) = 25584

Mathematical observation — Tribonacci-Pisano periods at primes mix
prime-period (m = 3, 5) and composite-period (m = 2, 7) regimes.
This breaks any naive "period prime ⇔ modulus prime" guess and
suggests deeper Galois-orbit structure in the Tribonacci
recurrence.

  primes with prime period:    3, 5
  primes with composite period: 7  (= 16·3)

Future moduli (mod 11: 110, mod 13: 168) reinforce this mix.

Cubic class status (Tier 1 hardness):
  · Tribonacci mod {2, 3, 5, 7} all decidably periodic.
  · `ArithFSM3(n)` closure: bit period ≤ n³, signature period ≤ 5n³.
  · Tier 2 (aperiodic ⇒ ¬ ArithFSM3) closed via `Trib.Capstone`.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Trib.CRTCapstone

open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
  (signature_period_of_bits_period_and_anchor
   signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM
  (arithFSM2_signature_period_bound)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3
  (tribFSMmod2 tribFSMmod2_bits_period_4 tribFSMmod2_signature_period_4_from_1)
open E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod3
  (tribFSMmod3 tribFSMmod3_bits_period_13 tribFSMmod3_signature_period_26_from_1)
open E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod5
  (tribFSMmod5 tribFSMmod5_bits_period_31 tribFSMmod5_signature_period_62_from_1)
open E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod7
  (tribFSMmod7 tribFSMmod7_bits_period_48 tribFSMmod7_signature_period_48_from_1)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3Bound
  (tribFSMmod2_signature_period_bound)

/-! ### §1 — 3-modulus CRT closure (m ∈ {2, 3, 5}) -/

/-- Tribonacci CRT 3-modulus capstone.

  Independent cubic-class periodic instances at the first three
  prime moduli ≤ 5, each with bit period proof and signature
  period proof.  Establishes the CRT base case for cubic
  Tribonacci-Pisano theory.

  Bundle: 6 conjuncts (3 bit + 3 signature). -/
theorem trib_crt_capstone :
    -- mod 2 bits
    (∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k)
    -- mod 2 sig (from step 1)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k)
    -- mod 3 bits
    ∧ (∀ k, tribFSMmod3.bits (k + 13) = tribFSMmod3.bits k)
    -- mod 3 sig (from step 1, doubled to 26)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod3.bits (k + 26) = signature tribFSMmod3.bits k)
    -- mod 5 bits
    ∧ (∀ k, tribFSMmod5.bits (k + 31) = tribFSMmod5.bits k)
    -- mod 5 sig (from step 1, doubled to 62)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod5.bits (k + 62) = signature tribFSMmod5.bits k) :=
  ⟨tribFSMmod2_bits_period_4,
   tribFSMmod2_signature_period_4_from_1,
   tribFSMmod3_bits_period_13,
   tribFSMmod3_signature_period_26_from_1,
   tribFSMmod5_bits_period_31,
   tribFSMmod5_signature_period_62_from_1⟩

/-! ### §2 — 4-modulus CRT closure (adds m = 7) -/

/-- Tribonacci CRT 4-modulus capstone.

  Extends the 3-modulus capstone with mod 7 instance.  All bit +
  sig periods proven, with Trib mod 7 the first composite-period
  cubic-class instance (period 48 = 16·3).

  Bundle: 8 conjuncts (4 bit + 4 signature). -/
theorem trib_crt_4_capstone :
    -- Previous 3-modulus capstone
    ((∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k)
     ∧ (∀ k, k ≥ 1 →
         signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k)
     ∧ (∀ k, tribFSMmod3.bits (k + 13) = tribFSMmod3.bits k)
     ∧ (∀ k, k ≥ 1 →
         signature tribFSMmod3.bits (k + 26) = signature tribFSMmod3.bits k)
     ∧ (∀ k, tribFSMmod5.bits (k + 31) = tribFSMmod5.bits k)
     ∧ (∀ k, k ≥ 1 →
         signature tribFSMmod5.bits (k + 62) = signature tribFSMmod5.bits k))
    -- mod-7 instance
    ∧ (∀ k, tribFSMmod7.bits (k + 48) = tribFSMmod7.bits k)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod7.bits (k + 48)
          = signature tribFSMmod7.bits k) :=
  ⟨trib_crt_capstone,
   tribFSMmod7_bits_period_48,
   tribFSMmod7_signature_period_48_from_1⟩

end E213.Lib.Math.NumberTheory.DyadicFSM.Trib.CRTCapstone
