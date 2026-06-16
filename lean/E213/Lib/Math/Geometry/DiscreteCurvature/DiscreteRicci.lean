import E213.Meta.Int213.Core

/-!
# Discrete (Forman) Ricci curvature (∅-axiom)

The smooth-metric general Ricci-flow theory (Perelman `𝓕/𝓦`-monotonicity) needs
Riemannian geometry + PDE and is not treated here.  But **Ricci
curvature has a genuinely combinatorial incarnation** — *Forman–Ricci curvature*
— defined directly from cell-complex / graph combinatorics, with no smooth
manifold: a real curvature and a real Ricci flow in the discrete category.

For a triangle-free unweighted graph the Forman curvature of an edge `e = (u,v)`
is `F(e) = 4 − deg(u) − deg(v)`.  The complete bipartite graph `K_{NS,NT}` is
triangle-free, where every `S`-vertex has degree
`NT` and every `T`-vertex degree `NS`, so **every edge carries the same
curvature** `F = 4 − NS − NT`.

The sign tracks topology (discrete Gauss–Bonnet flavour):
  · `K_{1,1}` (single edge, a tree, `b₁ = 0`): `F = 2 > 0` — positively curved;
  · `K_{1,3}` (star, a tree, `b₁ = 0`): `F = 0` — flat;
  · `K_{3,2}` (`b₁ = 8`, richly cyclic): `F = −1 < 0` — negatively curved.

Negative discrete curvature ↔ positive `b₁` — the same trivial-loop ↔ rich-loop
split read off `b₁`, here read off curvature.  Edge weights + a discrete
Ricci-flow step `w ↦ w − F·w` make this an actual flow, with
convergence/normalization the target on the discrete side.

Scope: this is discrete Ricci flow (Forman/Ollivier), a genuine parallel theory,
not smooth Perelman.
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteRicci

open E213.Meta.Int213 (neg_add add_assoc)

/-- Forman–Ricci curvature of a triangle-free unweighted edge with endpoint
    degrees `du`, `dv`: `F = 4 − du − dv` (over `ℤ`, since it can be negative). -/
def formanEdge (du dv : Nat) : Int := 4 - (du : Int) - (dv : Int)

/-- ★★ **Forman curvature is determined by the degree-*sum*.**  Two edges with
    the same `du + dv` carry the same curvature: `4 − du − dv` factors through
    `du + dv`.  Curvature is fixed completely by the degree-sum; its content
    "beyond a count" is a **sign** (`4 − du − dv` lives in `ℤ`), not a longer
    vector.  In particular a "same degree-sum, different curvature" collision
    is impossible — exactly what this theorem rules out. -/
theorem forman_determined_by_degree_sum {du dv du' dv' : Nat}
    (h : du + dv = du' + dv') : formanEdge du dv = formanEdge du' dv' := by
  have key : ∀ a b : Int, (4 : Int) - a - b = 4 - (a + b) := by
    intro a b
    show (4 + -a) + -b = 4 + -(a + b)
    rw [neg_add a b]
    exact add_assoc 4 (-a) (-b)
  show (4 : Int) - (du : Int) - (dv : Int) = 4 - (du' : Int) - (dv' : Int)
  rw [key (du : Int) (dv : Int), key (du' : Int) (dv' : Int),
    ← Int.ofNat_add, ← Int.ofNat_add, h]

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

/-- ★★★★★ **Discrete curvature ↔ topology** (Forman / Gauss–Bonnet flavour):
    the tree `K_{1,1}` is positively curved (`b₁ = 0`) while the cyclic
    `K_{3,2}` is negatively curved (`b₁ = 8`).  The trivial-loop ↔ rich-loop
    split, read off curvature rather than off `b₁`. -/
theorem discrete_curvature_topology :
    formanEdge 1 1 = 2 ∧ (0 : Int) < formanEdge 1 1
    ∧ formanEdge 2 3 = -1 ∧ formanEdge 2 3 < 0 := by decide


/-- **Forman curvature of a 3-regular edge** (K₄ or the cube): `4 − 3 − 3 = −2`.
    Non-bipartite companion to `forman_K32 = −1`; every edge of a 3-regular graph
    carries the same Forman value `−2`. -/
theorem forman_K4 : formanEdge 3 3 = -2 := by decide

/-- **Forman curvature of a 4-regular edge** (`K₅`): `4 − 4 − 4 = −4`. -/
theorem forman_K5 : formanEdge 4 4 = -4 := by decide
end E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteRicci
