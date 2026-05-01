import E213.Math.Cohomology.DyadicArithFSMHardness
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Pell ArithFSM family — capstone

Bundles the Tier 1 (algebraic, Pell-style) closure into a single
theorem with the following 6 conjuncts:

1. Pell mod 2: bit period 3 (universal)
2. Pell mod 3: bit period 4, signature period 4
3. Pell mod 5: bit period 10, signature period 10
4. ArithFSM2(n) ⊂ BitFSM(n²) (bit-stream equivalence)
5. ArithFSM2(n) signature period ≤ 5n² (quantitative bound)
6. Aperiodic bs ⇒ no ArithFSM2(n) generates it (Tier 2 hardness)

All conjuncts at ≤ {propext, Quot.sound}.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★★★ Pell capstone: Tier 1 (algebraic, Pell-style)
    fully characterised in the K_{3,2}^{(2)} signature lens.

    Combines:
      • concrete bit periods (3, 4, 10) for Pell mod {2, 3, 5},
      • concrete signature periods (4, 10) for mod {3, 5} and
        eventual period 6 from step 1 for mod 2,
      • universal bit-stream equivalence ArithFSM2(n) ↔ BitFSM(n²),
      • universal signature period bound 5n² for any ArithFSM2(n),
      • Tier 2 hardness (aperiodic ⇒ no ArithFSM2). -/
theorem pell_capstone :
    -- bit periodicity (mod 2, 3, 5)
    (∀ k, pellFSMmod2.bits (k + 3) = pellFSMmod2.bits k)
    ∧ (∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    -- concrete signature periodicity (mod 3, 5)
    ∧ (∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k)
    ∧ (∀ k, signature pellFSMmod5.bits (k + 10) = signature pellFSMmod5.bits k)
    -- mod 2 has signature period 6 from step 1
    ∧ (∀ k, k ≥ 1 →
        signature pellFSMmod2.bits (k + 6) = signature pellFSMmod2.bits k)
    -- ArithFSM2(n) ⊂ BitFSM(n²) bit-stream equivalence
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat),
        (m.toBitFSM hn).bits k = m.bits k)
    -- ArithFSM2(n) signature period ≤ 5n²
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM2 n),
        ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n)
          ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k)
    -- aperiodic ⇒ no ArithFSM2(n) (Tier 2 hardness)
    ∧ (∀ (bs : Nat → Bool),
        (∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) →
        ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n),
          ¬ (∀ k, m.bits k = bs k)) :=
  ⟨pellFSMmod2_bits_period_3,
   pellFSMmod3_bits_period_4,
   pellFSMmod5_bits_period_10,
   pellFSMmod3_signature_period_4,
   pellFSMmod5_signature_period_10,
   pellFSMmod2_signature_period_6_from_1,
   @toBitFSM_bits_eq,
   @arithFSM2_signature_period_bound,
   aperiodic_bits_imp_not_ArithFSM2⟩

end E213.Math.Cohomology.DyadicConjecture
