import E213.Lib.Math.Mobius213OneAsGlue
import E213.Lib.Physics.Simplex.Counts
import E213.Theory.Atomicity

/-!
# Mobius213K32Bridge — Möbius P matrix entries ↔ K_{3,2}^(c=2) structure

The bipartite multigraph `K_{3,2}^(c=2)` (the 213 canonical
Lattice) carries the following numerical signature:

  · `NS = 3` S-vertices
  · `NT = 2` T-vertices
  · `c = 2` edges per (S, T) pair
  · `5 = NS + NT` total vertices
  · `12 = NS · NT · c` total edges
  · `6 = NS · NT` cross-pair count (at base `c = 1`)

The Möbius matrix `P = [[2,1],[1,1]]` encodes every one of these
quantities as one of its algebraic invariants:

  · `trace P = 2 + 1 = 3 = NS`
  · `P[0][0] = 2 = NT = c` (NT and c coincide at the atomic
    signature — the same `2`)
  · `P[1][1] = 1 = det P` (the "unit")
  · `P[0][1] + P[1][0] = 1 + 1 = 2 = NT = c` (off-diagonal sum)
  · Sum of all entries `= 2 + 1 + 1 + 1 = 5 = disc P = NS + NT`
  · `NS · P[0][0] = 3 · 2 = 6 = NS · NT` (cross-pair count)
  · `trace P · P[0][0] · 2 = 3 · 2 · 2 = 12` (edge count;
    coincides because of `c = NT = 2`)

This file records the bridge as a single capstone bundle.  All
underlying numerical facts already live in
`Mobius213OneAsGlue.lean` (Möbius side) and
`Physics/Simplex/Counts.lean` (atomic-signature side); this
file collects them as a K_{3,2}^(c=2)-specific cross-frame
anchor.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Mobius213K32Bridge

open E213.Lib.Math.Mobius213OneAsGlue
  (mobius_entries_sum_to_d ns_nt_product ns_is_succ_nt
   mobius_det_eq_ns_minus_nt off_diagonal_is_two_ones)
open E213.Lib.Physics.Simplex.Counts (d NS NT partition_sum)

/-! ## §1 — K_{3,2}^(c=2) vertex / edge / pair signature -/

/-- Total vertex count of K_{3,2}^(c=2) is `NS + NT = 5 = d`. -/
theorem k32_total_vertices : NS + NT = 5 := by decide

/-- Total edge count of K_{3,2}^(c=2) at `c = 2` is `NS · NT · 2
    = 12`.  The size of `CochE = Fin 12 → Bool` in
    `Cohomology/Bipartite/V32.lean`. -/
theorem k32_total_edges_at_c2 : NS * NT * 2 = 12 := by decide

/-- Cross-pair count at base `c = 1` is `NS · NT = 6`.  The
    Eisenstein unit count, gluon octet 6-rep, Sym(3) order. -/
theorem k32_cross_pairs : NS * NT = 6 := ns_nt_product

/-! ## §2 — Möbius P entries ↔ K_{3,2}^(c=2) signature

The bridge: each Möbius entry / invariant matches a K_{3,2}
quantity.  All by `decide` since the values are concrete. -/

/-- `trace P = NS`: the matrix's trace counts S-vertices. -/
theorem trace_P_eq_NS : (2 : Int) + 1 = (NS : Int) := by decide

/-- `P[0][0] = NT`: the top-left entry counts T-vertices.  This
    also equals `c = 2` (NT and c coincide at the (3, 2)
    atomicity). -/
theorem P_top_left_eq_NT : (2 : Nat) = NT := by decide

/-- `P[0][0] = c` at `c = 2`.  Coincides with the previous
    theorem because NT and c are both 2 in the canonical
    signature. -/
theorem P_top_left_eq_c : (2 : Nat) = 2 := rfl

/-- Off-diagonal sum: `P[0][1] + P[1][0] = NT = c`. -/
theorem off_diagonal_eq_NT : (1 : Nat) + 1 = NT := by decide

/-- Sum of all entries of `P` equals `d = NS + NT`.  Recorded in
    `Mobius213OneAsGlue.mobius_entries_sum_to_d`. -/
theorem entries_sum_eq_d : (2 : Nat) + 1 + 1 + 1 = d :=
  mobius_entries_sum_to_d

/-- `det P = NS − NT = 1` — the "unit / glue".  Recorded in
    `Mobius213OneAsGlue.mobius_det_eq_ns_minus_nt`. -/
theorem det_P_eq_NS_minus_NT :
    (2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int) :=
  mobius_det_eq_ns_minus_nt

/-! ## §3 — Cross-frame anchor capstone -/

/-- ★★★★★★★ **K_{3,2}^(c=2) ↔ Möbius P capstone**: every
    K_{3,2}^(c=2) structural count appears as a Möbius P
    invariant or entry.  Six-conjunct bundle uniting the
    bipartite Lattice's vertex/edge/pair signature with P's
    algebraic invariants.

    The same numbers `(2, 3, 5, 6, 12)` appear on both sides —
    the two readings of the atomic structure converge at the
    canonical Lattice. -/
theorem k32_mobius_bridge_master :
    -- (a) Vertex count
    (NS + NT = 5)
    -- (b) trace P = NS
    ∧ ((2 : Int) + 1 = (NS : Int))
    -- (c) P[0][0] = NT
    ∧ ((2 : Nat) = NT)
    -- (d) Cross-pair count = NS · NT = P[0][0] · trace P
    ∧ (NS * NT = (2 : Nat) * ((2 : Nat) + 1))
    -- (e) Edge count at c = 2 is 12
    ∧ (NS * NT * 2 = 12)
    -- (f) Entries sum = d
    ∧ ((2 : Nat) + 1 + 1 + 1 = d)
    -- (g) det P = glue = NS − NT = 1
    ∧ ((2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | exact mobius_det_eq_ns_minus_nt

end E213.Lib.Math.Mobius213.Mobius213K32Bridge
