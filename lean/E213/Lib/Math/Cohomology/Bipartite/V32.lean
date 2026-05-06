import E213.Lib.Math.Cohomology.Cup.Ring

/-!
# Cohomology — K_{3,2}^{(2)} bipartite multigraph

A separate cochain construction for the bipartite multigraph
K_{3,2}^{(2)} (5 vertices: 3 S + 2 T; 12 edges, each S-T pair
twice).  The simplex framework (Δⁿ⁻¹) used in CA-CD acts on
k-subsets of {0..n-1}; this is graph-on-edges instead.

Edge e ∈ Fin 12: S-idx = (e/2)/2 ∈ {0,1,2}, T-idx = (e/2)%2 ∈
{0,1}, multiplicity = e%2.  Vertices: S = 0,1,2; T = 3,4.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V32

/-- Source vertex (S-idx) of edge e. -/
def srcOf (e : Nat) : Nat := (e / 2) / 2

/-- Target vertex (T-idx + 3) of edge e. -/
def tgtOf (e : Nat) : Nat := 3 + (e / 2) % 2

/-- Vertex cochain: Fin 5 → Bool. -/
def CochV : Type := Fin 5 → Bool

/-- Edge cochain: Fin 12 → Bool. -/
def CochE : Type := Fin 12 → Bool

/-- Source vertex as Fin 5 (mod for safety; actual < 3). -/
def srcFin (e : Fin 12) : Fin 5 :=
  ⟨srcOf e.val % 5, Nat.mod_lt _ (by decide)⟩

/-- Target vertex as Fin 5 (mod for safety; actual ∈ {3,4}). -/
def tgtFin (e : Fin 12) : Fin 5 :=
  ⟨tgtOf e.val % 5, Nat.mod_lt _ (by decide)⟩

/-- Coboundary δ₀: (δσ)(e) = σ(src e) XOR σ(tgt e). -/
def delta0 (σ : CochV) : CochE :=
  fun e => xor (σ (srcFin e)) (σ (tgtFin e))

/-- Edge 0 has S-vertex 0 and T-vertex 3. -/
theorem edge0_endpoints :
    srcFin ⟨0, by decide⟩ = ⟨0, by decide⟩
    ∧ tgtFin ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide

/-- Edge 11 (last) has S-vertex 2 and T-vertex 4. -/
theorem edge11_endpoints :
    srcFin ⟨11, by decide⟩ = ⟨2, by decide⟩
    ∧ tgtFin ⟨11, by decide⟩ = ⟨4, by decide⟩ := by decide

/-- All-true vertex cochain. -/
def allTrueV : CochV := fun _ => true

/-- Zero vertex cochain. -/
def zeroV : CochV := fun _ => false

/-- Vertex-0 indicator. -/
def v0V : CochV := fun i => i.val == 0

/-- δ₀(zeroV) = zero edge cochain. -/
theorem delta0_zero : ∀ e : Fin 12, delta0 zeroV e = false := by decide

/-- δ₀(allTrueV) = zero edge cochain (constant in ker). -/
theorem delta0_allTrue : ∀ e : Fin 12, delta0 allTrueV e = false := by decide

/-- δ₀(v0V) on edge 0 (S=0, T=3): true XOR false = true. -/
theorem delta0_v0_at_edge0 : delta0 v0V ⟨0, by decide⟩ = true := by decide

/-- δ₀(v0V) on edge 11 (S=2, T=4): false XOR false = false. -/
theorem delta0_v0_at_edge11 : delta0 v0V ⟨11, by decide⟩ = false := by decide

end E213.Lib.Math.Cohomology.Bipartite.V32
