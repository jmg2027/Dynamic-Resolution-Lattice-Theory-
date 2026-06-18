import E213.Lib.Math.Cohomology.Examples.K5
import E213.Lib.Math.Cohomology.Fractal.Level

/-!
# Step 4 — K_{3,2}^(c=2) ⊆ K₅ underlying-edge subset (∅-axiom)

K_{3,2}^(c=2) (12 edges, c=2 multiplicity) maps each edge to its
underlying simple-edge endpoints, which lie in K₅'s 10 edges.

**Proven**: every K_{3,2}^(c=2) edge has a matching K₅ edge.
**Refuted**: the multigraph reading (multiplicities collapse).
-/

namespace E213.Lib.Math.Foundations.UniverseChain.BipartiteFractal

open E213.Lib.Math.Cohomology.Examples.K5
  renaming srcFin → srcFinK, tgtFin → tgtFinK
open E213.Lib.Math.Cohomology.Fractal.Level (numV)

/-! ## K_{3,2}^{(c=2)} edge-endpoint encoding (inlined)

The K_{3,2}^{(c=2)} graph has 12 edges (`Fin 12`).  Edge `e` decodes
to S-index `(e/2)/2 ∈ {0,1,2}`, T-index `(e/2)%2 ∈ {0,1}` (T-vertices
placed at indices 3, 4 in `Fin 5`), multiplicity `e%2`.  These are the
endpoint extractors of the bipartite Lattice, inlined here so the
fractal-embedding statement does not depend on a cohomology carrier. -/

/-- Source vertex (S-idx) of bipartite edge `e`. -/
def srcOfB (e : Nat) : Nat := (e / 2) / 2

/-- Target vertex (T-idx + 3) of bipartite edge `e`. -/
def tgtOfB (e : Nat) : Nat := 3 + (e / 2) % 2

/-- Source vertex of edge `e` as `Fin 5`. -/
def srcFinB (e : Fin 12) : Fin 5 :=
  ⟨srcOfB e.val % 5, Nat.mod_lt _ (by decide)⟩

/-- Target vertex of edge `e` as `Fin 5`. -/
def tgtFinB (e : Fin 12) : Fin 5 :=
  ⟨tgtOfB e.val % 5, Nat.mod_lt _ (by decide)⟩

/-- Bipartite edge `e`'s underlying simple-edge endpoints. -/
def bipUnderlyingPair (e : Fin 12) : Fin 5 × Fin 5 :=
  (srcFinB e, tgtFinB e)

/-- K₅ edge `k`'s endpoints. -/
def k5Pair (k : Fin 10) : Fin 5 × Fin 5 :=
  (srcFinK k, tgtFinK k)

/-- Edge map: K_{3,2}^(c=2) edge → K₅ edge (if-chain). -/
def edgeMap (e : Fin 12) : Fin 10 :=
  let v := e.val
  if v ≤ 1 then ⟨2, by decide⟩
  else if v ≤ 3 then ⟨3, by decide⟩
  else if v ≤ 5 then ⟨5, by decide⟩
  else if v ≤ 7 then ⟨6, by decide⟩
  else if v ≤ 9 then ⟨7, by decide⟩
  else ⟨8, by decide⟩

/-- ★ **Underlying-edge containment**: ∀-form, decide. -/
theorem edgeMap_correct : ∀ e : Fin 12,
    bipUnderlyingPair e = k5Pair (edgeMap e) := by decide

/-- ★ ∃-form: existence of K₅ edge. -/
theorem bip_edge_in_K5 (e : Fin 12) :
    ∃ k : Fin 10, bipUnderlyingPair e = k5Pair k :=
  ⟨edgeMap e, edgeMap_correct e⟩

/-- ★ **Multiplicity collapse** — refutes "as multigraphs". -/
theorem multiplicity_lost :
    ∃ e₁ e₂ : Fin 12, e₁ ≠ e₂
    ∧ bipUnderlyingPair e₁ = bipUnderlyingPair e₂ :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, by decide⟩

/-- ★ Vertex count match: both have 5 vertices. -/
theorem step4_vertex_match : (5 : Nat) = numV 1 := by decide

/-- ★★★ **Step 4 capstone**. -/
theorem step4_bundle :
    (∀ e : Fin 12, bipUnderlyingPair e = k5Pair (edgeMap e))
    ∧ (∃ e₁ e₂ : Fin 12, e₁ ≠ e₂
        ∧ bipUnderlyingPair e₁ = bipUnderlyingPair e₂)
    ∧ (5 : Nat) = numV 1 :=
  ⟨edgeMap_correct, multiplicity_lost, step4_vertex_match⟩

end E213.Lib.Math.Foundations.UniverseChain.BipartiteFractal
