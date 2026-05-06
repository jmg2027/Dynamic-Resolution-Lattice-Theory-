import E213.Lib.Math.DyadicFSM.Trib.CRTCapstone
import E213.Lib.Math.DyadicFSM.Trib.FSMmod7

import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.DyadicFSM.ArithFSM.V3Bound
import E213.Lib.Math.DyadicFSM.ConcretePellSig
import E213.Lib.Math.DyadicFSM.Signature
import E213.Lib.Math.DyadicFSM.Trib.FSMmod3
import E213.Lib.Math.DyadicFSM.Trib.FSMmod5
/-!
# Tribonacci CRT — 4 cubic moduli {2, 3, 5, 7}

Extends `DyadicTribCRTCapstone` from 3 cubic moduli to 4.

  | m | bit period | sig period | sig pre-period | composite? |
  | 2 |     4      |      4     |       1        | yes (4=2²) |
  | 3 |    13      |     26     |       1        | prime      |
  | 5 |    31      |     62     |       1        | prime      |
  | 7 |    48      |     48     |       1        | yes        |

CRT closure: lcm(4, 13, 31, 48) = 25584.

★ Mathematical observation ★ — Tribonacci-Pisano periods at primes
mix prime-period (m=3, 5) and composite-period (m=2, 7) regimes.
This breaks any naive "period prime ⇔ modulus prime" guess and
suggests deeper Galois-orbit structure in the Tribonacci recurrence.

  primes with prime period:    3, 5
  primes with composite period: 7  (= 16·3)

Future moduli (mod 11: 110, mod 13: 168) reinforce this mix.
-/

namespace E213.Lib.Math.DyadicFSM.Trib.CRT4Capstone
open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (tribFSMmod2 tribFSMmod2_bits_period_4 tribFSMmod2_signature_period_4_from_1)
open E213.Lib.Math.DyadicFSM.Trib.FSMmod3 (tribFSMmod3 tribFSMmod3_bits_period_13 tribFSMmod3_signature_period_26_from_1)
open E213.Lib.Math.DyadicFSM.Trib.FSMmod5 (tribFSMmod5 tribFSMmod5_bits_period_31 tribFSMmod5_signature_period_62_from_1)
open E213.Lib.Math.DyadicFSM.Trib.FSMmod7 (tribFSMmod7 tribFSMmod7_bits_period_48 tribFSMmod7_signature_period_48_from_1)
open E213.Lib.Math.DyadicFSM.Trib.CRTCapstone (trib_crt_capstone)
open E213.Lib.Math.DyadicFSM.ArithFSM.V3Bound (tribFSMmod2_signature_period_bound)

open E213.Lib.Math.DyadicFSM.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- ★★★★★★★★ Tribonacci CRT 4-modulus capstone.

  Extends 3-modulus capstone with mod 7 instance.  All bit + sig
  periods proven, with Trib mod 7 the first composite-period
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
    -- New mod-7 instance
    ∧ (∀ k, tribFSMmod7.bits (k + 48) = tribFSMmod7.bits k)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod7.bits (k + 48)
          = signature tribFSMmod7.bits k) :=
  ⟨trib_crt_capstone,
   tribFSMmod7_bits_period_48,
   tribFSMmod7_signature_period_48_from_1⟩

end E213.Lib.Math.DyadicFSM.Trib.CRT4Capstone
