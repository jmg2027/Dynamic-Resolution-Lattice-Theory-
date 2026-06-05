/-!
# K_{3,2}^{(c=2)} bipartite adjacency — the §6.2 graph the simplex erased (∅-axiom)

This session's free slash-reading gave the regular `n`-simplex = the *complete*
graph `K_{n+1}` (all vertex pairs adjacent, fully `S_{n+1}`-symmetric:
`AngleStructure/SimplexOrthogonality.lean`).  That symmetry erases any
distinction between vertices.  The 213 canonical Lattice `K_{3,2}^{(c=2)}` is the
*same* 5-vertex set re-read with the §6.2 **state / transition** (operator /
object) split — `N_S = 3` one kind, `N_T = 2` the other — so edges run **only
across** the two kinds, never within (`TernaryBinary.lean` gives the axes; this
file gives the adjacency the axes induce).

The bipartition is exactly the asymmetry the complete simplex symmetrized away:
the complete `K_5` has `C(5,2) = 10` edges; the §6.2 split removes the
`C(3,2)+C(2,2) = 3+1 = 4` within-kind edges, leaving the `3·2 = 6` cross pairs,
each taken with multiplicity `c = 2` → `12` edges.

Vertices `0,1,2` = S (state/operator), `3,4` = T (transition/object), matching
`Cohomology/Bipartite/V32`.  All facts decidable over concrete lists → PURE.
-/

namespace E213.Lib.Math.Geometry.BipartiteDecomp.K32Adjacency

/-- The `N_S = 3` state (operator) side: vertices `< 3`. -/
def isS (v : Nat) : Bool := v < 3

/-- The `N_T = 2` transition (object) side: vertices `3, 4`. -/
def isT (v : Nat) : Bool := decide (3 ≤ v) && v < 5

/-- Bipartite adjacency: an edge connects a state to a transition (either order)
    and *never* two of the same kind.  This is the §6.2 operator↔object
    incidence — connection only across the split. -/
def adj (u v : Nat) : Bool := (isS u && isT v) || (isT u && isS v)

/-- The 5 vertices. -/
def verts : List Nat := List.range 5

/-- ★ **Bipartite — no within-state edge.**  No two S-vertices are adjacent. -/
theorem no_state_state :
    verts.all (fun u => verts.all (fun v => !(isS u && isS v && adj u v))) = true := by
  decide

/-- ★ **Bipartite — no within-transition edge.**  No two T-vertices adjacent. -/
theorem no_transition_transition :
    verts.all (fun u => verts.all (fun v => !(isT u && isT v && adj u v))) = true := by
  decide

/-- ★ **Complete across the split.**  Every (state, transition) pair is adjacent
    — the full `K_{3,2}` cross structure. -/
theorem cross_complete :
    verts.all (fun u => verts.all (fun v => !(isS u && isT v) || adj u v)) = true := by
  decide

/-! ## Edge multiset (multiplicity `c = 2`) and degrees -/

/-- The 12 edges of `K_{3,2}^{(c=2)}`: each of the `3·2` cross pairs twice. -/
def edges : List (Nat × Nat) :=
  [(0,3),(0,3),(0,4),(0,4),(1,3),(1,3),(1,4),(1,4),(2,3),(2,3),(2,4),(2,4)]

/-- Degree of an S-vertex = number of incident edges. -/
def degS (s : Nat) : Nat := (edges.filter (fun e => e.1 == s)).length

/-- Degree of a T-vertex = number of incident edges. -/
def degT (t : Nat) : Nat := (edges.filter (fun e => e.2 == t)).length

/-- ★ **Edge count** `= N_S · N_T · c = 12`. -/
theorem edge_count : edges.length = 12 := by decide

/-- ★ **Every edge crosses the split** (S-endpoint `< 3`, T-endpoint `∈ {3,4}`):
    a concrete witness of bipartiteness on the edge set. -/
theorem edges_cross :
    edges.all (fun e => isS e.1 && isT e.2) = true := by decide

/-- ★ **S-degree `= N_T · c = 4`** at every state vertex. -/
theorem state_degree : degS 0 = 4 ∧ degS 1 = 4 ∧ degS 2 = 4 := by decide

/-- ★ **T-degree `= N_S · c = 6`** at every transition vertex. -/
theorem transition_degree : degT 3 = 6 ∧ degT 4 = 6 := by decide

/-- ★ **Handshake**: `Σ deg = 2 · |E| = 24` — `3·4` (state side) `+ 2·6`
    (transition side). -/
theorem handshake : degS 0 + degS 1 + degS 2 + degT 3 + degT 4 = 2 * 12 := by decide

/-! ## Contrast with the complete simplex -/

/-- ★ **The split removes the within-kind edges.**  Complete `K_5` has `10`
    edges; bipartite `K_{3,2}` (at `c = 1`) keeps only the `6` cross pairs — the
    `C(3,2)+C(2,2) = 4` within-kind edges are exactly what the §6.2 split drops
    from the symmetric (simplex) reading. -/
theorem simplex_minus_within :
    (5 * 4) / 2 - (3 * 2 / 2 + 2 * 1 / 2) = 3 * 2 := by decide

/-- ★★★ **Master.**  The §6.2 bipartite graph, ∅-axiom: no within-kind edges
    (state–state, transition–transition), complete across the split, `12` edges,
    S-degree `4`, T-degree `6`, handshake `24`, and the complete-`K_5`-minus-
    within-edges identity that recovers the `6` cross pairs. -/
theorem k32_adjacency_master :
    (verts.all (fun u => verts.all (fun v => !(isS u && isS v && adj u v))) = true)
    ∧ (verts.all (fun u => verts.all (fun v => !(isT u && isT v && adj u v))) = true)
    ∧ edges.length = 12
    ∧ (degS 0 = 4 ∧ degS 1 = 4 ∧ degS 2 = 4)
    ∧ (degT 3 = 6 ∧ degT 4 = 6)
    ∧ (degS 0 + degS 1 + degS 2 + degT 3 + degT 4 = 2 * 12)
    ∧ ((5 * 4) / 2 - (3 * 2 / 2 + 2 * 1 / 2) = 3 * 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Geometry.BipartiteDecomp.K32Adjacency
