import E213.Math.Cohomology.Dyadic.Trib.CRTCapstone
import E213.Math.Cohomology.Dyadic.Trib.FSMmod7

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

namespace E213.Math.Cohomology.Dyadic.Trib.CRT4Capstone

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

end E213.Math.Cohomology.Dyadic.Trib.CRT4Capstone
