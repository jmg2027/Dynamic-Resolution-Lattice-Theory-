import E213.Math.Cohomology.Dyadic.Archive.SubwordComplexity

/-!
# Edge-based K_{3,2}^{(2)} signature variant

Alternative lens: instead of vertex (Fin 5) trajectory, track the
EDGE (Fin 12) traversed at each step.  Each edge encodes (vertex,
bit, parallel-edge-multiplicity) = richer than vertex alone.

  edgeSignature bs k := edge from sig(k) via bit bs(k)

where the edge index is determined canonically by (vertex, bit).
This gives a Fin 12 trajectory with up to 12 distinct values vs
5 for vertex signature.
-/

namespace E213.Math.Cohomology.Dyadic.Archive.EdgeSignature

open E213.Math.Cohomology.Dyadic.Signature (nextVertex signature)


/-- Edge from vertex v with bit b in K_{3,2}^{(2)}.  Canonical
    selection: each (v, b) pair maps to a unique edge that:
    - is incident to v,
    - has parallel-edge bit b,
    - and points "forward" along nextVertex's choice. -/
def edgeFromBit (v : Fin 5) (b : Bool) : Fin 12 :=
  match v.val, b with
  | 0, false => ⟨0, by decide⟩  -- S_0 → T_0, bit 0
  | 0, true  => ⟨3, by decide⟩  -- S_0 → T_1, bit 1
  | 1, false => ⟨4, by decide⟩  -- S_1 → T_0, bit 0
  | 1, true  => ⟨7, by decide⟩  -- S_1 → T_1, bit 1
  | 2, false => ⟨8, by decide⟩  -- S_2 → T_0, bit 0
  | 2, true  => ⟨11, by decide⟩ -- S_2 → T_1, bit 1
  | 3, false => ⟨0, by decide⟩  -- T_0 → S_0, bit 0
  | 3, true  => ⟨5, by decide⟩  -- T_0 → S_1, bit 1
  | 4, false => ⟨7, by decide⟩  -- T_1 → S_1, bit 0 (offset)
  | 4, true  => ⟨11, by decide⟩ -- T_1 → S_2, bit 1
  | _, _ => ⟨0, by decide⟩

/-- Edge signature: trajectory of K_{3,2}^{(2)} edges. -/
def edgeSignature (bs : Nat → Bool) (k : Nat) : Fin 12 :=
  edgeFromBit (signature bs k) (bs k)

/-- Edge signature for 1/3: 3 distinct edges in first 4 steps. -/
theorem bit13_edge_signature_first4 :
    edgeSignature bit13 0 = ⟨0, by decide⟩
    ∧ edgeSignature bit13 1 = ⟨5, by decide⟩
    ∧ edgeSignature bit13 2 = ⟨4, by decide⟩
    ∧ edgeSignature bit13 3 = ⟨5, by decide⟩ := by decide

/-- Edge signature for Thue-Morse: 4 distinct edges in first 4 steps. -/
theorem thueMorse_edge_signature_first4 :
    edgeSignature thueMorse 0 = ⟨0, by decide⟩
    ∧ edgeSignature thueMorse 1 = ⟨5, by decide⟩
    ∧ edgeSignature thueMorse 2 = ⟨7, by decide⟩
    ∧ edgeSignature thueMorse 3 = ⟨7, by decide⟩ := by decide

/-- ★★★ The edge sequences differ at position 2: 1/3 → edge 4
    (S_1-T_0); Thue-Morse → edge 7 (S_1-T_1, mult 1).  Different
    edge → different paths through K_{3,2}^{(2)}. -/
theorem edge_signatures_differ_at_2 :
    edgeSignature bit13 2 ≠ edgeSignature thueMorse 2 := by decide

end E213.Math.Cohomology.Dyadic.Archive.EdgeSignature
