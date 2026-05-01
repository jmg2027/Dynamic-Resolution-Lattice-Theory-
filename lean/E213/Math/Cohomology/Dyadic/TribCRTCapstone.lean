import E213.Math.Cohomology.Dyadic.ArithFSM3
import E213.Math.Cohomology.Dyadic.TribFSMmod3
import E213.Math.Cohomology.Dyadic.TribFSMmod5

/-!
# Tribonacci CRT capstone — 3 cubic moduli {2, 3, 5}

  | m | bit period | sig period | sig pre-period |
  | 2 |     4      |      4     |       1        |
  | 3 |    13      |     26     |       1        |
  | 4 |    --      |     --     |       (skipped, not prime) |
  | 5 |    31      |     62     |       1        |

Three independent cubic moduli verified.  Wall–Sun (Tribonacci-
Pisano) periods are *prime* at m ∈ {3, 5}: π(3) = 13, π(5) = 31.
This is non-trivial Galois behaviour for the cubic plastic-style
recurrence — periods are NOT divisors of m³ - 1 in general.

CRT closure: the Tribonacci trajectory mod 30 (= 2·3·5) has period
lcm(4, 13, 31) = 1612, computable as a product BitFSM via the
ArithFSM3 ⊂ BitFSM(n³) embedding.

Cubic class status (Tier 1 hardness):
  * Tribonacci mod {2, 3, 5} all decidably periodic.
  * ArithFSM3(n) closure: bit period ≤ n³, signature period ≤ 5n³.
  * Tier 2 (aperiodic ⇒ ¬ ArithFSM3) closed via DyadicTribCapstone.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★★★★ Tribonacci CRT 3-modulus capstone.

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

end E213.Math.Cohomology.Dyadic.Conjecture
