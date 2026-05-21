import E213.Lib.Math.DyadicFSM.Tier.Tier2Hardness

import E213.Lib.Math.DyadicFSM.Signature.Signature
/-!
# Thue-Morse — aperiodic 2-automatic bit stream

Thue-Morse: t(n) = parity of popcount(n) in binary.
Pattern: 0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0,...

Class between Tier 0 (periodic) and "truly random": aperiodic
but finitely describable via popcount.  Not BitFSM-generable
(if conjectured aperiodicity holds).
-/

namespace E213.Lib.Math.DyadicFSM.ThueMorse

open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)


/-- 213-native bit extractor (LSB at position 0).  ∅-axiom — uses
    Nat./, Nat.%, Nat.pow only (no `Nat.testBit`, which leaks
    propext via its Lean-core definition). -/
def bit213 (n j : Nat) : Bool := (n / 2^j) % 2 == 1

/-- Thue-Morse: parity of binary popcount.  ∅-axiom via `bit213`. -/
def thueMorse (n : Nat) : Bool :=
  (List.range (n + 1)).foldl (fun acc i => xor acc (bit213 n i)) false

/-- ★ Thue-Morse master — first 8 values, aperiodicity for periods
    1..8 (with explicit witnesses) and 9..16, self-similarity
    t(2n) = t(n) and t(2n+1) = !t(n) for n ≤ 7, and K_{3,2}^{(2)}
    signature aperiodicity + first-8 trajectory.

    Pattern: 0,1,1,0,1,0,0,1.  Aperiodic but finitely describable
    via popcount.  Not BitFSM-generable. -/
theorem thueMorse_master :
    -- First 8 values
    (thueMorse 0 = false ∧ thueMorse 1 = true
     ∧ thueMorse 2 = true ∧ thueMorse 3 = false
     ∧ thueMorse 4 = true ∧ thueMorse 5 = false
     ∧ thueMorse 6 = false ∧ thueMorse 7 = true)
    -- Aperiodic 1..8 (explicit witness for each period)
    ∧ (∃ k, thueMorse (k + 1) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 2) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 3) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 4) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 5) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 6) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 7) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 8) ≠ thueMorse k)
    -- Aperiodic 9..16
    ∧ thueMorse (1 + 9) ≠ thueMorse 1
    ∧ thueMorse (2 + 10) ≠ thueMorse 2
    ∧ thueMorse (0 + 11) ≠ thueMorse 0
    ∧ thueMorse (8 + 12) ≠ thueMorse 8
    ∧ thueMorse (0 + 13) ≠ thueMorse 0
    ∧ thueMorse (0 + 14) ≠ thueMorse 0
    ∧ thueMorse (2 + 15) ≠ thueMorse 2
    ∧ thueMorse (0 + 16) ≠ thueMorse 0
    -- Self-similarity for n ≤ 7
    ∧ (∀ n, n ≤ 7 → thueMorse (2 * n) = thueMorse n)
    ∧ (∀ n, n ≤ 7 → thueMorse (2 * n + 1) = !thueMorse n)
    -- K_{3,2}^{(2)} signature aperiodicity for 1, 2, 3, 4
    ∧ signature thueMorse 1 ≠ signature thueMorse 0
    ∧ signature thueMorse 3 ≠ signature thueMorse 1
    ∧ signature thueMorse 5 ≠ signature thueMorse 2
    ∧ signature thueMorse 7 ≠ signature thueMorse 3
    -- Signature trajectory first 8 indices: 0, 3, 1, 4, 1, 4, 1, 3
    ∧ signature thueMorse 0 = ⟨0, by decide⟩
    ∧ signature thueMorse 1 = ⟨3, by decide⟩
    ∧ signature thueMorse 2 = ⟨1, by decide⟩
    ∧ signature thueMorse 3 = ⟨4, by decide⟩
    ∧ signature thueMorse 4 = ⟨1, by decide⟩
    ∧ signature thueMorse 5 = ⟨4, by decide⟩
    ∧ signature thueMorse 6 = ⟨1, by decide⟩
    ∧ signature thueMorse 7 = ⟨3, by decide⟩ := by
  refine ⟨?_, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨2, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩, ⟨4, ?_⟩,
          ⟨0, ?_⟩, ⟨0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide | (intro _ _; decide)

end E213.Lib.Math.DyadicFSM.ThueMorse
