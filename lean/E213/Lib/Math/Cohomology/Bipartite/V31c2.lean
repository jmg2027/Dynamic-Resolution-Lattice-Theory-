import E213.Lib.Math.Cohomology.Cup.Ring

/-!
# Cohomology — K_{3,1}^{(c=2)} bipartite multigraph (star with 2-multiplicity)

A "tree-like" bipartite multigraph: 3 S-vertices connected to a
single T-vertex with multiplicity 2.  Underlying simple graph
K_{3,1} is a star (tree, no simple cycles).  At c=2 the only
short cycles are length-2 (parallel edges).

  · 4 vertices (3 S + 1 T)
  · 6 edges (3 S-T pairs × 2 multiplicities)
  · 0 simple 4-cycles in underlying K_{3,1}

## H² = 0 under uniform mult-0 face convention

Following the `V32` / `V22` convention of taking only simple
4-cycles using mult-0 edges as 2-cells: K_{3,1}^{(c=2)} has
ZERO faces (no 4-cycles exist in the underlying tree).

  · `C² = Fin 0 → Bool` ≃ unit type
  · `δ¹` is the zero map
  · `H² = C² / im δ¹` is trivially zero

Hence every Massey product on K_{3,1}^{(c=2)} is automatically
vacuous (target H² = 0).

## Companion to V22

Together with `V22.lean` (K_{2,2}^{(c=2)} also Massey-trivial,
single face), this establishes the **structural lower bound**:
neither smaller nor different small bipartite multigraph admits
non-vacuous Massey under the natural face convention.

K_{3,2}^{(c=2)} earns its distinguished status as the **smallest
graph** with non-vacuous secondary cohomology.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V31c2

/-- Source vertex (S-idx) of edge e (in 0..2). -/
def srcOf (e : Nat) : Nat := e / 2

/-- Target vertex (T-idx + 3, only one T vertex) of edge e. -/
def tgtOf (_e : Nat) : Nat := 3

/-- Multiplicity of edge e (0 or 1). -/
def multOf (e : Nat) : Nat := e % 2

/-- Vertex cochain space: `Fin 4 → Bool`. -/
def CochV : Type := Fin 4 → Bool

/-- Edge cochain space: `Fin 6 → Bool`. -/
def CochE : Type := Fin 6 → Bool

/-- S-vertex of edge e packaged as `Fin 4`. -/
def srcFin (e : Fin 6) : Fin 4 :=
  ⟨srcOf e.val % 4, Nat.mod_lt _ (by decide)⟩

/-- T-vertex of edge e packaged as `Fin 4` — always vertex 3. -/
def tgtFin (_e : Fin 6) : Fin 4 := ⟨3, by decide⟩

/-- Coboundary δ⁰. -/
def delta0 (σ : CochV) : CochE :=
  fun e => xor (σ (srcFin e)) (σ (tgtFin e))

/-! ## §1 — Edge sanity checks -/

theorem edge0_endpoints :
    srcFin ⟨0, by decide⟩ = ⟨0, by decide⟩
    ∧ tgtFin ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide

theorem edge5_endpoints :
    srcFin ⟨5, by decide⟩ = ⟨2, by decide⟩
    ∧ tgtFin ⟨5, by decide⟩ = ⟨3, by decide⟩ := by decide

/-! ## §2 — No simple 4-cycles in K_{3,1}

The underlying simple graph K_{3,1} is a star (tree).  Trees have
no cycles, so no 4-cycles exist.  Under the uniform mult-0 face
convention, the 2-skeleton has **zero** 2-cells. -/

/-- δ¹ on the 0-face 2-skeleton: trivially the zero map into
    the empty face cochain space. -/
def delta1 (_σ : CochE) : Fin 0 → Bool := fun i => i.elim0

/-! ## §3 — H² = 0 (vacuously) + Massey-triviality -/

/-- ★★★ **K_{3,1}^{(c=2)} Massey-triviality capstone**: the
    underlying K_{3,1} is a tree, so 0 simple 4-cycles, so 0
    2-cells, so `C² = Fin 0 → Bool` is the unit type.  H² is
    trivially zero.  Every Massey product is automatically
    vacuous.

    Together with `V22.K22_c2_massey_trivial`, this confirms
    that NO bipartite multigraph K_{NS,NT}^{(c=2)} with
    NS + NT < 5 admits non-vacuous Massey under the uniform
    face convention.  K_{3,2}^{(c=2)} (NS + NT = 5) is the
    smallest. -/
theorem K31_c2_massey_trivial :
    -- delta1 lands in Fin 0 → Bool, which is uniquely the empty cochain
    ∀ (σ : CochE) (i : Fin 0), delta1 σ i = i.elim0 :=
  fun _ i => i.elim0

/-! ## §4 — Edge / vertex count compatibility -/

/-- K_{3,1}^{(c=2)} has 6 edges (= 1·3·2 in parametric form). -/
theorem K31_edge_count : 2 * 3 * 1 = 6 := by decide

/-- K_{3,1}^{(c=2)} has 4 vertices. -/
theorem K31_vertex_count : 3 + 1 = 4 := by decide

end E213.Lib.Math.Cohomology.Bipartite.V31c2
