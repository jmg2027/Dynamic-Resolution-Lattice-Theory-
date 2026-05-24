import E213.Lib.Physics.Simplex.Counts

/-!
# Cohomology — K_{NT, det, NS} = K_{2, 1, 3} complete tripartite

Tripartite complete graph K_{NT, det, NS} = K_{2, 1, 3} with
triangle 2-cells (rainbow triangles, one vertex per part) filled.

Atomic structure (cross-link: `Mobius213.Px.TripartiteK213`):
  · |V| = NT + det + NS = 2 + 1 + 3 = 6 = NS · NT
  · |E| = NT·det + det·NS + NT·NS = 2 + 3 + 6 = 11
  · |△| = NT · det · NS = 6 = NS · NT

Vertex layout (Fin 6):
  · 0, 1     = T-part (NT = 2)
  · 2        = G (glue, det = 1)
  · 3, 4, 5  = S-part (NS = 3)

Edge layout (Fin 11):
  · 0, 1                 = (T_i, G)          [glue edges, a_i]
  · 2, 3, 4              = (G, S_j)          [glue edges, b_j]
  · 5, 6, 7              = (T_0, S_j)        [direct edges, c_{0j}]
  · 8, 9, 10             = (T_1, S_j)        [direct edges, c_{1j}]

Triangle layout (Fin 6):  rainbow △_{ij} = (T_i, G, S_j)
  · f = 0..2 : i = 0, j = f      edges {a_0,   b_j, c_{0j}}
  · f = 3..5 : i = 1, j = f - 3  edges {a_1,   b_j, c_{1j}}

Crucially: each direct edge c_{ij} (positions 5..10) appears in
exactly ONE triangle.  This pivot structure makes δ¹ surjective
(see `V213Betti`).

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Cohomology.Tripartite.V213

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-- Vertex cochains. -/
def CochV : Type := Fin 6 → Bool

/-- Edge cochains. -/
def CochE : Type := Fin 11 → Bool

/-- Triangle (2-face) cochains. -/
def CochF : Type := Fin 6 → Bool

/-- Source vertex of edge e. -/
def srcOf (e : Fin 11) : Fin 6 :=
  ⟨(if e.val = 0 then 0
    else if e.val = 1 then 1
    else if e.val ≤ 4 then 2
    else if e.val ≤ 7 then 0
    else 1) % 6,
   Nat.mod_lt _ (by decide)⟩

/-- Target vertex of edge e. -/
def tgtOf (e : Fin 11) : Fin 6 :=
  ⟨(if e.val ≤ 1 then 2
    else if e.val = 2 then 3
    else if e.val = 3 then 4
    else if e.val = 4 then 5
    else if e.val = 5 then 3
    else if e.val = 6 then 4
    else if e.val = 7 then 5
    else if e.val = 8 then 3
    else if e.val = 9 then 4
    else 5) % 6,
   Nat.mod_lt _ (by decide)⟩

/-- First edge of triangle f (the T-G glue edge a_i). -/
def faceEdge1 (f : Fin 6) : Fin 11 :=
  ⟨(if f.val ≤ 2 then 0 else 1) % 11,
   Nat.mod_lt _ (by decide)⟩

/-- Second edge of triangle f (the G-S glue edge b_j). -/
def faceEdge2 (f : Fin 6) : Fin 11 :=
  ⟨(if f.val % 3 = 0 then 2
    else if f.val % 3 = 1 then 3
    else 4) % 11,
   Nat.mod_lt _ (by decide)⟩

/-- Third edge of triangle f (the direct edge c_{ij}, pivot). -/
def faceEdge3 (f : Fin 6) : Fin 11 :=
  ⟨(if f.val ≤ 2 then 5 + f.val else 8 + (f.val - 3)) % 11,
   Nat.mod_lt _ (by decide)⟩

/-- Coboundary δ₀ : C⁰ → C¹.  (δσ)(e) = σ(src e) XOR σ(tgt e). -/
def delta0 (σ : CochV) : CochE :=
  fun e => xor (σ (srcOf e)) (σ (tgtOf e))

/-- Coboundary δ₁ : C¹ → C².
    (δα)(f) = α(faceEdge1 f) XOR α(faceEdge2 f) XOR α(faceEdge3 f). -/
def delta1 (α : CochE) : CochF :=
  fun f => xor (xor (α (faceEdge1 f)) (α (faceEdge2 f))) (α (faceEdge3 f))

end E213.Lib.Math.Cohomology.Tripartite.V213
