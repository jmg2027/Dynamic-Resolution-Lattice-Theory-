import E213.Math.Cohomology.DyadicTier2Hardness

/-!
# Thue-Morse — aperiodic 2-automatic bit stream

Thue-Morse: t(n) = parity of popcount(n) in binary.
Pattern: 0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0,...

Class between Tier 0 (periodic) and "truly random": aperiodic
but finitely describable via popcount.  Not BitFSM-generable
(if conjectured aperiodicity holds).
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Thue-Morse: parity of binary popcount. -/
def thueMorse (n : Nat) : Bool :=
  (List.range (n + 1)).foldl (fun acc i => xor acc (n.testBit i)) false

/-- First 8 values: 0,1,1,0,1,0,0,1. -/
theorem thueMorse_first8 :
    thueMorse 0 = false ∧ thueMorse 1 = true
    ∧ thueMorse 2 = true ∧ thueMorse 3 = false
    ∧ thueMorse 4 = true ∧ thueMorse 5 = false
    ∧ thueMorse 6 = false ∧ thueMorse 7 = true := by decide

/-- Not period 1, 2, 4, 7, 8: differ at index 0. -/
theorem thueMorse_not_period_at_0 :
    thueMorse 1 ≠ thueMorse 0
    ∧ thueMorse 2 ≠ thueMorse 0
    ∧ thueMorse 4 ≠ thueMorse 0
    ∧ thueMorse 7 ≠ thueMorse 0
    ∧ thueMorse 8 ≠ thueMorse 0 := by decide

/-- Not period 3, 5, 6: differ at small witnesses. -/
theorem thueMorse_not_period_3_5_6 :
    thueMorse (2 + 3) ≠ thueMorse 2
    ∧ thueMorse (1 + 5) ≠ thueMorse 1
    ∧ thueMorse (4 + 6) ≠ thueMorse 4 := by decide

/-- ★★★ Aperiodic for periods 1..8: explicit witness for each. -/
theorem thueMorse_aperiodic_short :
    (∃ k, thueMorse (k + 1) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 2) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 3) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 4) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 5) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 6) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 7) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 8) ≠ thueMorse k) := by
  obtain ⟨h1, h2, h4, h7, h8⟩ := thueMorse_not_period_at_0
  obtain ⟨h3, h5, h6⟩ := thueMorse_not_period_3_5_6
  exact ⟨⟨0, h1⟩, ⟨0, h2⟩, ⟨2, h3⟩, ⟨0, h4⟩,
         ⟨1, h5⟩, ⟨4, h6⟩, ⟨0, h7⟩, ⟨0, h8⟩⟩

/-- ★★ Self-similarity verified for n ≤ 7:
    t(2n) = t(n) and t(2n+1) = !t(n).  Decidable on bounded range. -/
theorem thueMorse_self_similar_small :
    (∀ n, n ≤ 7 → thueMorse (2 * n) = thueMorse n)
    ∧ (∀ n, n ≤ 7 → thueMorse (2 * n + 1) = !thueMorse n) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ★★★★ K_{3,2}^{(2)} signature of Thue-Morse is also aperiodic
    for periods 1, 2, 3, 4 (small range, decidable). -/
theorem thueMorse_signature_aperiodic_small :
    signature thueMorse 1 ≠ signature thueMorse 0
    ∧ signature thueMorse 3 ≠ signature thueMorse 1
    ∧ signature thueMorse 5 ≠ signature thueMorse 2
    ∧ signature thueMorse 7 ≠ signature thueMorse 3 := by decide

end E213.Math.Cohomology.DyadicConjecture
