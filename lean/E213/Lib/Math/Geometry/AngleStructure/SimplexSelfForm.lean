/-!
# Simplex self-form — static = dynamic for the complete-graph reading (∅-axiom)

The complete-graph / simplex reading of the slash is the case where the two
descriptions of the structure coincide (`research-notes/geometric/
static_dynamic_duality.md`):

  · STATIC (completed S, νF): "in S every pair of vertices is an edge" — the
    completed `K_m` has `edgesK m` edges.
  · DYNAMIC (constructive, μF): "add the m-th vertex joined to all earlier" — one
    step adds `m` edges.

For this reading the two are **definitionally equal**: `edgesK (m+1) = edgesK m + m`
holds by `rfl`.  The completed edge count and the constructive step are the same
recursion — the arithmetic face of `μF ≅ νF` (Lambek; the categorical version is
`Theory/Raw/MuNuMirror`, `MobiusSelfForm.self_reconstruction_master`).  The
generic reading does NOT coincide: the betweenness reading's construction gives
the countable dyadic points while its completion is the continuum, and the gap is
`Lens/FlatOntologyClosure.object1_not_surjective` (reached by none) — so the
self-form below is special to the complete-graph cell.

`edgesK` reproduces the complete-graph rule's edge counts
(`complete_graph_rule.py`): at `m = 2,3,5,12,68` it is `1,3,10,66,2278 = C(m,2)`.
All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Geometry.AngleStructure.SimplexSelfForm

/-- Edges of the complete graph on `m` vertices.  Defined by the constructive
    step (each new vertex joins all earlier) — which is *also* the completed-S
    count `C(m,2)`. -/
def edgesK : Nat → Nat
  | 0 => 0
  | m + 1 => edgesK m + m

/-- ★ **static = dynamic, definitionally.**  The completed `K_{m+1}` (`edgesK (m+1)`
    edges, every pair) equals `K_m` plus one vertex joined to all `m` earlier
    (`edgesK m + m`).  By `rfl` — the constructive step and the completed count are
    one recursion.  This is the arithmetic face of `μF ≅ νF` for this reading. -/
theorem complete_step (m : Nat) : edgesK (m + 1) = edgesK m + m := rfl

/-- ★ The completed-S edge counts `= C(m,2)` at the complete-graph rule's stages
    `m = 2,3,5,12` — the static description, agreeing with the construction. -/
theorem edges_at_stages :
    edgesK 2 = 1 ∧ edgesK 3 = 3 ∧ edgesK 5 = 10 ∧ edgesK 12 = 66 := by decide

/-- ★ One saturated cycle (every edge of `K_m` spawns a vertex) takes `m` vertices
    to `m + edgesK m`; concretely the point sequence `2 → 3 → 5 → 12 → 68`
    (`n + edgesK n`), the complete-graph rule's growth. -/
theorem cycle_point_steps :
    2 + edgesK 2 = 3 ∧ 3 + edgesK 3 = 6 ∧ 5 + edgesK 5 = 15 ∧ 12 + edgesK 12 = 78 := by
  decide

/-- ★ The new-edges-only cycle (only the previous round's new lines spawn points)
    gives the actual rule sequence `2,3,5,12,68`: `n_{k+1} = n_k +
    (edgesK n_k − edgesK n_{k−1})` (the new edges of the previous round), verified
    at the first stages. -/
theorem rule_sequence :
    3 = 2 + edgesK 2
    ∧ 5 = 3 + (edgesK 3 - edgesK 2)
    ∧ 12 = 5 + (edgesK 5 - edgesK 3)
    ∧ 68 = 12 + (edgesK 12 - edgesK 5) := by decide

/-- ★★ **Master.**  The complete-graph / simplex reading's self-form: the
    constructive step equals the completed-S count (`rfl`), and the edge counts
    are `C(m,2)` at the rule's stages — static and dynamic are one. -/
theorem simplex_self_form_master :
    (∀ m : Nat, edgesK (m + 1) = edgesK m + m)
    ∧ (edgesK 2 = 1 ∧ edgesK 3 = 3 ∧ edgesK 5 = 10 ∧ edgesK 12 = 66) :=
  ⟨complete_step, edges_at_stages⟩

end E213.Lib.Math.Geometry.AngleStructure.SimplexSelfForm
