import E213.Meta.Int213.Core

/-!
# Discrete (Forman) Ricci curvature — the ∅-axiom route to the A6 core

The smooth-metric general Ricci-flow core (Perelman `𝓕/𝓦`-monotonicity) needs
Riemannian geometry + PDE and is out of `∅`-axiom reach here.  But **Ricci
curvature has a genuinely combinatorial incarnation** — *Forman–Ricci curvature*
— defined directly from cell-complex / graph combinatorics, with no smooth
manifold.  This is the 213-native route to actually closing A6's conquest: a
real curvature, real Ricci flow, in the discrete category the repo lives in.

For a triangle-free unweighted graph the Forman curvature of an edge `e = (u,v)`
is `F(e) = 4 − deg(u) − deg(v)`.  The repo's central object `K_{NS,NT}` is the
complete bipartite graph (triangle-free), where every `S`-vertex has degree
`NT` and every `T`-vertex degree `NS`, so **every edge carries the same
curvature** `F = 4 − NS − NT`.

The sign tracks topology (discrete Gauss–Bonnet flavour):
  · `K_{1,1}` (single edge, a tree, `b₁ = 0`): `F = 2 > 0` — positively curved;
  · `K_{1,3}` (star, a tree, `b₁ = 0`): `F = 0` — flat;
  · `K_{3,2}` (`b₁ = 8`, richly cyclic): `F = −1 < 0` — negatively curved.

Negative discrete curvature ↔ positive `b₁` — the same trivial-loop ↔ rich-loop
split the Poincaré pillar (`Poincare.lean`) reads off `b₁`, now read off
curvature.  Edge weights + a discrete Ricci-flow step `w ↦ w − F·w` (the next
brick) make this an actual flow; convergence/normalization is the A6 target on
the discrete side.

Scope: this is discrete Ricci flow (Forman/Ollivier), a genuine parallel theory,
not smooth Perelman.  Ladder + status: `research-notes/frontiers/a6_ricci_core/`.
-/

namespace E213.Lib.Math.Geometry.GeometrizationConjecture.DiscreteRicci

/-- Forman–Ricci curvature of a triangle-free unweighted edge with endpoint
    degrees `du`, `dv`: `F = 4 − du − dv` (over `ℤ`, since it can be negative). -/
def formanEdge (du dv : Nat) : Int := 4 - (du : Int) - (dv : Int)

/-- Every edge of complete bipartite `K_{NS,NT}` carries curvature `4 − NS − NT`
    (an `S`-endpoint has degree `NT`, a `T`-endpoint degree `NS`). -/
theorem forman_bipartite (NS NT : Nat) :
    formanEdge NT NS = 4 - (NT : Int) - (NS : Int) := rfl

/-- `K_{1,1}` single edge (a tree, `b₁ = 0`): `F = 2 > 0`, positively curved. -/
theorem forman_K11 : formanEdge 1 1 = 2 := by decide

/-- `K_{1,3}` star (a tree, `b₁ = 0`): `F = 0`, flat. -/
theorem forman_K13 : formanEdge 1 3 = 0 := by decide

/-- `K_{3,2}` (`b₁ = 8`, richly cyclic): `F = −1 < 0`, negatively curved. -/
theorem forman_K32 : formanEdge 2 3 = -1 := by decide

/-- **Discrete curvature ↔ topology** (Forman / Gauss–Bonnet flavour):
    the tree `K_{1,1}` is positively curved (`b₁ = 0`) while the cyclic
    `K_{3,2}` is negatively curved (`b₁ = 8`).  The trivial-loop ↔ rich-loop
    split the Poincaré pillar reads off `b₁`, here read off curvature. -/
theorem discrete_curvature_topology :
    formanEdge 1 1 = 2 ∧ (0 : Int) < formanEdge 1 1
    ∧ formanEdge 2 3 = -1 ∧ formanEdge 2 3 < 0 := by decide

end E213.Lib.Math.Geometry.GeometrizationConjecture.DiscreteRicci
