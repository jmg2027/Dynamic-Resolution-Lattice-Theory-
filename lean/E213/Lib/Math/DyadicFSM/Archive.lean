import E213.Lib.Math.DyadicFSM.ThueMorse
import E213.Lib.Math.DyadicFSM.Tier.TierBridge
import E213.Lib.Math.DyadicFSM.Signature.Signature

/-!
# DyadicFSM.Archive — historical sub-cluster

Preserved for reference .
Two themes into a single file:

  * `Archive.SubwordComplexity` — `subwordCount` (length-L
    substring count) as a complexity measure on Fin 5 trajectories.
    For BitFSM streams, subword count is BOUNDED (≤ joint state
    count = 5n); for aperiodic streams, count grows with L.
  * `Archive.EdgeSignature` — alternative K_{3,2}^{(2)} lens:
    track EDGE (Fin 12) traversed at each step rather than vertex
    (Fin 5).  Each edge encodes (vertex, bit,
    parallel-edge-multiplicity).
-/

namespace E213.Lib.Math.DyadicFSM.Archive.SubwordComplexity

open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ThueMorse (thueMorse)
open E213.Lib.Math.DyadicFSM.Tier.TierBridge (bit13)

/-- Length-L substrings of trajectory `s` starting at position 0..M-1. -/
def subwords (s : Nat → Fin 5) (L M : Nat) : List (List (Fin 5)) :=
  (List.range M).map (fun k => (List.range L).map (fun i => s (k + i)))

/-- Distinct subword count: length-L substrings sampled over M positions. -/
def subwordCount (s : Nat → Fin 5) (L M : Nat) : Nat :=
  (subwords s L M).eraseDups.length

theorem one_third_signature_subword_count_2_8 :
    subwordCount (signature bit13) 2 8 = 3 := by decide

theorem thueMorse_signature_subword_count_2_8 :
    subwordCount (signature thueMorse) 2 8 = 5 := by decide

theorem one_third_signature_subword_count_3_8 :
    subwordCount (signature bit13) 3 8 = 3 := by decide

theorem thueMorse_signature_subword_count_3_8 :
    subwordCount (signature thueMorse) 3 8 = 6 := by decide

/-- ★★★ Subword complexity DISTINGUISHES periodic from aperiodic
    at small L. -/
theorem subword_distinguishes_periodic_aperiodic :
    subwordCount (signature bit13) 2 8 < subwordCount (signature thueMorse) 2 8
    ∧ subwordCount (signature bit13) 3 8
        < subwordCount (signature thueMorse) 3 8 := by decide

theorem one_third_signature_subword_count_8_16 :
    subwordCount (signature bit13) 8 16 = 3 := by decide

/-- ★★★★ Periodic stays bounded, Thue-Morse strictly grows. -/
theorem subword_growth_separation :
    subwordCount (signature bit13) 1 16 < subwordCount (signature thueMorse) 1 16
    ∧ subwordCount (signature bit13) 2 16 < subwordCount (signature thueMorse) 2 16
    ∧ subwordCount (signature bit13) 3 16 < subwordCount (signature thueMorse) 3 16
    ∧ subwordCount (signature bit13) 4 16
        < subwordCount (signature thueMorse) 4 16 := by decide

end E213.Lib.Math.DyadicFSM.Archive.SubwordComplexity

namespace E213.Lib.Math.DyadicFSM.Archive.EdgeSignature

open E213.Lib.Math.DyadicFSM.Signature.Signature (nextVertex signature)
open E213.Lib.Math.DyadicFSM.ThueMorse (thueMorse)
open E213.Lib.Math.DyadicFSM.Tier.TierBridge (bit13)

/-- Edge from vertex v with bit b in K_{3,2}^{(2)}. -/
def edgeFromBit (v : Fin 5) (b : Bool) : Fin 12 :=
  match v.val, b with
  | 0, false => ⟨0, by decide⟩
  | 0, true  => ⟨3, by decide⟩
  | 1, false => ⟨4, by decide⟩
  | 1, true  => ⟨7, by decide⟩
  | 2, false => ⟨8, by decide⟩
  | 2, true  => ⟨11, by decide⟩
  | 3, false => ⟨0, by decide⟩
  | 3, true  => ⟨5, by decide⟩
  | 4, false => ⟨7, by decide⟩
  | 4, true  => ⟨11, by decide⟩
  | _, _ => ⟨0, by decide⟩

/-- Edge signature: trajectory of K_{3,2}^{(2)} edges. -/
def edgeSignature (bs : Nat → Bool) (k : Nat) : Fin 12 :=
  edgeFromBit (signature bs k) (bs k)

theorem bit13_edge_signature_first4 :
    edgeSignature bit13 0 = ⟨0, by decide⟩
    ∧ edgeSignature bit13 1 = ⟨5, by decide⟩
    ∧ edgeSignature bit13 2 = ⟨4, by decide⟩
    ∧ edgeSignature bit13 3 = ⟨5, by decide⟩ := by decide

theorem thueMorse_edge_signature_first4 :
    edgeSignature thueMorse 0 = ⟨0, by decide⟩
    ∧ edgeSignature thueMorse 1 = ⟨5, by decide⟩
    ∧ edgeSignature thueMorse 2 = ⟨7, by decide⟩
    ∧ edgeSignature thueMorse 3 = ⟨7, by decide⟩ := by decide

/-- ★★★ Edge sequences differ at position 2 — different paths
    through K_{3,2}^{(2)}. -/
theorem edge_signatures_differ_at_2 :
    edgeSignature bit13 2 ≠ edgeSignature thueMorse 2 := by decide

end E213.Lib.Math.DyadicFSM.Archive.EdgeSignature
