import E213.Math.Cohomology.Dyadic.ThueMorse

/-!
# Subword complexity of K_{3,2}^{(2)} signature trajectories

Define `subwordCount` (length-L substring count over first M
positions) as a quantitative complexity measure on Fin 5
trajectories.

For BitFSM-generated streams, subword count is BOUNDED (≤ joint
state count = 5n).  For aperiodic streams, subword count typically
GROWS with L.

This file gives concrete decidable computations of subword counts
for periodic and aperiodic example signatures.
-/

namespace E213.Math.Cohomology.Dyadic.Archive.SubwordComplexity

open E213.Math.Cohomology.Dyadic.Signature (signature)
open E213.Math.Cohomology.Dyadic.ThueMorse (thueMorse)


/-- Length-L substrings of trajectory `s` starting at position
    0..M-1. -/
def subwords (s : Nat → Fin 5) (L M : Nat) : List (List (Fin 5)) :=
  (List.range M).map (fun k => (List.range L).map (fun i => s (k + i)))

/-- Distinct subword count: length-L substrings sampled over M positions. -/
def subwordCount (s : Nat → Fin 5) (L M : Nat) : Nat :=
  (subwords s L M).eraseDups.length

/-- For 1/3 (period 2 from sig 1), subword count at L=2 over 8
    positions is small (bounded by period). -/
theorem one_third_signature_subword_count_2_8 :
    subwordCount (signature bit13) 2 8 = 3 := by decide

/-- For Thue-Morse (aperiodic), subword count at L=2 over 8
    positions is RICHER. -/
theorem thueMorse_signature_subword_count_2_8 :
    subwordCount (signature thueMorse) 2 8 = 5 := by decide

/-- For 1/3 at L=3, even more bounded (still 3). -/
theorem one_third_signature_subword_count_3_8 :
    subwordCount (signature bit13) 3 8 = 3 := by decide

/-- For Thue-Morse at L=3, complexity grows. -/
theorem thueMorse_signature_subword_count_3_8 :
    subwordCount (signature thueMorse) 3 8 = 6 := by decide

/-- ★★★ Subword complexity DISTINGUISHES periodic from aperiodic
    at small L: 1/3 has bounded growth, Thue-Morse grows. -/
theorem subword_distinguishes_periodic_aperiodic :
    subwordCount (signature bit13) 2 8 < subwordCount (signature thueMorse) 2 8
    ∧ subwordCount (signature bit13) 3 8
        < subwordCount (signature thueMorse) 3 8 := by decide

/-- For 1/3 even at L=8 (= 4 × period), still 3 distinct subwords. -/
theorem one_third_signature_subword_count_8_16 :
    subwordCount (signature bit13) 8 16 = 3 := by decide

/-- ★★★★ Subword counts for periodic (1/3) vs aperiodic (Thue-Morse)
    at M=16: periodic stays bounded, Thue-Morse strictly grows. -/
theorem subword_growth_separation :
    subwordCount (signature bit13) 1 16 < subwordCount (signature thueMorse) 1 16
    ∧ subwordCount (signature bit13) 2 16 < subwordCount (signature thueMorse) 2 16
    ∧ subwordCount (signature bit13) 3 16 < subwordCount (signature thueMorse) 3 16
    ∧ subwordCount (signature bit13) 4 16
        < subwordCount (signature thueMorse) 4 16 := by decide

end E213.Math.Cohomology.Dyadic.Archive.SubwordComplexity
