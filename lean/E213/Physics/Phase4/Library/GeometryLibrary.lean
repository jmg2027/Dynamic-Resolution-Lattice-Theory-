import E213.Physics.Simplex.Counts

/-!
# Geometry Library — 5-simplex Δ⁴ atomic catalog

## Δ⁴ face distribution

  vertex (0-face)  C(d,1) = 5
  edge   (1-face)  C(d,2) = 10
  triangle (2-face) C(d,3) = 10  ★ Hodge dual to edge
  tetrahedron      C(d,4) = 5    ★ Hodge dual to vertex
  4-cell           C(d,5) = 1

## Atomic integers

  C(d,2) = C(d,3) = 10 (Hodge symmetry)
  C(d,1) = C(d,4) = d
  C(d,0) = C(d,5) = 1

## Bipartite K_{NS,NT}^(c=2)

  vertices = NS + NT = d
  edges    = c · NS · NT = 12
  cycle    = E - V + 1 = 12 - 5 + 1 = 8 = NS²-1 ★
-/

namespace E213.Physics.Phase4.Library.GeometryLibrary

open E213.Physics.Simplex

/-- Δ⁴ vertex count = d. -/
theorem vertex_count : d = 5 := by decide

/-- Δ⁴ edge count = C(d,2) = 10. -/
theorem edge_count : d * (d - 1) / 2 = 10 := by decide

/-- Hodge symmetry: C(d,2) = C(d,3). -/
theorem hodge_2_3 : d * (d - 1) / 2 = d * (d - 1) * (d - 2) / 6 := by decide

/-- K_{3,2}^(c=2) cycle space = 8 atomic. -/
theorem cycle_space : 2 * NS * NT - d + 1 = 8 := by decide

end E213.Physics.Phase4.Library.GeometryLibrary
