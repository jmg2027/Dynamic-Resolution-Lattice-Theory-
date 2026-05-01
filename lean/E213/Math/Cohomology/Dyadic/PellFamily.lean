import E213.Math.Cohomology.Dyadic.ArithFSMmod7
import E213.Math.Cohomology.Dyadic.PellBounds

/-!
# Pell ArithFSM family — full 4-modulus closure

Bundles the four Pell instances (mod 2, 3, 5, 7) with their
TIGHT signature periods and universal 5n² guarantees.

  | mod | n² | TIGHT bit | TIGHT sig | guarantee 5n² |
  |  2  |  4 |    3      |    6 (pre)|     20       |
  |  3  |  9 |    4      |    4      |     45       |
  |  5  | 25 |   10      |   10      |    125       |
  |  7  | 49 |    8      |    8      |    245       |
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★★ Pell family closure: bit + signature periods +
    guarantees, all four moduli. -/
theorem pell_family_closure :
    -- bit periods
    (∀ k, pellFSMmod2.bits (k + 3) = pellFSMmod2.bits k)
    ∧ (∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + 8) = pellFSMmod7.bits k)
    -- TIGHT signature periods (mod 3, 5, 7 pure; mod 2 from step 1)
    ∧ (∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k)
    ∧ (∀ k, signature pellFSMmod5.bits (k + 10) = signature pellFSMmod5.bits k)
    ∧ (∀ k, signature pellFSMmod7.bits (k + 8) = signature pellFSMmod7.bits k)
    ∧ (∀ k, k ≥ 1 →
        signature pellFSMmod2.bits (k + 6) = signature pellFSMmod2.bits k)
    -- universal 5n² guarantees
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 20
        ∧ ∀ k, k ≥ N →
          signature pellFSMmod2.bits (k + P) = signature pellFSMmod2.bits k)
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 45
        ∧ ∀ k, k ≥ N →
          signature pellFSMmod3.bits (k + P) = signature pellFSMmod3.bits k)
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 125
        ∧ ∀ k, k ≥ N →
          signature pellFSMmod5.bits (k + P) = signature pellFSMmod5.bits k)
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 245
        ∧ ∀ k, k ≥ N →
          signature pellFSMmod7.bits (k + P) = signature pellFSMmod7.bits k) :=
  ⟨pellFSMmod2_bits_period_3,
   pellFSMmod3_bits_period_4,
   pellFSMmod5_bits_period_10,
   pellFSMmod7_bits_period_8,
   pellFSMmod3_signature_period_4,
   pellFSMmod5_signature_period_10,
   pellFSMmod7_signature_period_8,
   pellFSMmod2_signature_period_6_from_1,
   pellFSMmod2_signature_period_bound,
   pellFSMmod3_signature_period_bound,
   pellFSMmod5_signature_period_bound,
   pellFSMmod7_signature_period_bound⟩

end E213.Math.Cohomology.Dyadic.Conjecture
