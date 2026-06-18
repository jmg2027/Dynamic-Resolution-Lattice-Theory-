import E213.Lib.Math.Cohomology.Cup.Ring

/-!
# Parametric cochain spaces for K_{NS,NT}^{(c)}

Generalizes `V32.lean` from the K_{3,2}^{(c=2)} special case to
arbitrary (NS, NT, c) deployments.

## Edge encoding

For K_{NS,NT}^{(c)} the edges form `Fin (c * NS * NT)`.  An edge
`e` decomposes as the triple `(s, t, m)`:
  · multiplicity m = e % c   (in 0..c-1)
  · T-index    t = (e / c) % NT   (in 0..NT-1)
  · S-index    s = (e / c) / NT   (in 0..NS-1)

Vertices are `Fin (NS + NT)`: indices 0..NS-1 are S-side, indices
NS..NS+NT-1 are T-side.

## Goal

Provide the parametric Cochain spaces and δ⁰ operator for
K_{NS,NT}^{(c)} (consumed by `Delta0AndConnectedness`,
`Betti/KernelConstancyUniversal`, `EulerAndCapstone`); the
K_{3,2}^{(c=2)} cohomology specializes at (NS, NT, c) = (3, 2, 2).
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.CochSpaces

/-- Vertex cochain space for K_{NS,NT}^{(c)}: functions
    `Fin (NS + NT) → Bool`.  Vertices 0..NS-1 = S-side,
    NS..NS+NT-1 = T-side. -/
def CochV (NS NT : Nat) : Type := Fin (NS + NT) → Bool

/-- Edge cochain space for K_{NS,NT}^{(c)}: functions
    `Fin (c * NS * NT) → Bool`.  Edge e decomposes as
    (s, t, m) per the encoding above. -/
def CochE (NS NT c : Nat) : Type := Fin (c * NS * NT) → Bool

/-! ## Edge endpoint extractors -/

/-- S-vertex index of edge e (in 0..NS-1).  Pure Nat arithmetic. -/
def srcOf (c NT : Nat) (e : Nat) : Nat := (e / c) / NT

/-- T-vertex index of edge e (in 0..NT-1).  Pure Nat arithmetic. -/
def tgtOf (c NT : Nat) (e : Nat) : Nat := (e / c) % NT

/-- Multiplicity of edge e (in 0..c-1). -/
def multOf (c : Nat) (e : Nat) : Nat := e % c

/-! ## Edge endpoints as `Fin (NS + NT)` -/

/-- S-vertex of edge e packaged as `Fin (NS + NT)`.  Uses safe mod
    for the type-level guarantee; actual value < NS by construction. -/
def srcFin (NS NT c : Nat) (hNT : 0 < NS + NT) (e : Fin (c * NS * NT)) :
    Fin (NS + NT) :=
  ⟨srcOf c NT e.val % (NS + NT), Nat.mod_lt _ hNT⟩

/-- T-vertex of edge e packaged as `Fin (NS + NT)`.  T-side indices
    start at NS, so we add NS to the T-index. -/
def tgtFin (NS NT c : Nat) (hNT : 0 < NS + NT) (e : Fin (c * NS * NT)) :
    Fin (NS + NT) :=
  ⟨(NS + tgtOf c NT e.val) % (NS + NT), Nat.mod_lt _ hNT⟩

/-! ## Parametric coboundary δ⁰ -/

/-- Coboundary δ⁰ on K_{NS,NT}^{(c)}: edges get XOR of endpoint
    vertex values.  Parameterized by (NS, NT, c) and a non-trivial
    vertex-count witness. -/
def delta0 (NS NT c : Nat) (hNT : 0 < NS + NT)
    (σ : CochV NS NT) : CochE NS NT c :=
  fun e => xor (σ (srcFin NS NT c hNT e)) (σ (tgtFin NS NT c hNT e))

/-! ## K_{3,2}^{(c=2)} specialization sanity check -/

/-- Specialisation `(NS, NT, c) = (3, 2, 2)` gives the V32 edge count. -/
theorem K32_edge_count : 2 * 3 * 2 = 12 := by decide

/-- Specialisation `(NS, NT, c) = (3, 2, 2)` gives the V32 vertex count. -/
theorem K32_vertex_count : 3 + 2 = 5 := by decide

/-- Edge 0 in K_{3,2}^{(c=2)} has S-vertex 0 and T-vertex 0
    (multiplicity 0).  Recovers V32 numeric witnesses. -/
theorem K32_edge0_endpoints :
    srcOf 2 2 0 = 0
    ∧ tgtOf 2 2 0 = 0
    ∧ multOf 2 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Last edge (e=11) in K_{3,2}^{(c=2)} has S-vertex 2 and T-vertex 1.
    Recovers V32 numeric witnesses. -/
theorem K32_edge11_endpoints :
    srcOf 2 2 11 = 2
    ∧ tgtOf 2 2 11 = 1
    ∧ multOf 2 11 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Generic vertex / edge counts -/

/-- For K_{NS,NT}^{(c=1)} (simple bipartite): edges = NS · NT. -/
theorem simple_bipartite_edge_count (NS NT : Nat) :
    1 * NS * NT = NS * NT := by
  rw [Nat.one_mul]

end E213.Lib.Math.Cohomology.Bipartite.Parametric.CochSpaces
