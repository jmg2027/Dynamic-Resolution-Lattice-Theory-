# What is curvature, in 213?

Curvature is a **Lens readout**: an integer the difference-Lens assigns to a
local incidence pattern.  It is not a property the residue *has* — it is a
number a counting view *returns*, and its sign is the difference-Lens's sign
bit.  The decisive 213 fact, a theorem on three independent frames, is that
the sign tracks topology no matter which counting view is chosen.

## 213-native answer

Fix a complete bipartite graph `K_{NS,NT}` (the repo's central object).
Curvature is what the count-Lens reads off a vertex-or-edge neighborhood,
valued in `ℤ` because the readout can be negative — and `ℤ` is the count-Lens
read on an *ordered* difference, magnitude Nat-style and sign Bool-style
(`seed/AXIOM/06_lens_readings.md` §6.7).  So "curvature is negative" is not a
substance claim; it is the sign bit of a difference-Lens readout.

## Derivation across frames

**Frame 1 — Forman (edge count).** `formanEdge du dv = 4 − du − dv`
(`Geometry/GeometrizationConjecture/DiscreteRicci.lean`).  One subtraction of
two degree-counts.  `K_{1,1}` reads `+2`, `K_{1,3}` reads `0`, `K_{3,2}` reads
`−1` (`forman_K11`/`forman_K13`/`forman_K32`), and `discrete_curvature_topology`
ties the sign to `b₁`.

**Frame 2 — Gauss–Bonnet (vertex count).** `vertexCurv d = 2 − deg(d)`
(`DiscreteGaussBonnet.lean`).  A *different* local count, yet `gauss_bonnet_Kmn`
gives `Σ_v κ(v) = 2·χ`, and with `χ = 1 − b₁` (`euler_eq_one_sub_b1`) the total
reads `totalVertexCurv = 2 − 2·b₁` (`totalCurv_eq`).  `curvature_sign_topology`:
`+` ⟺ tree (`b₁=0`), `−` ⟺ cyclic.  The vertex count recovers the same
sign↔topology the edge count did.

**Frame 3 — Ollivier (optimal transport).** Here the readout is
`κ = 1 − W₁(m_x,m_y)/d(x,y)`, and `W₁` is *itself* a Lens minimum — the optimal
coupling cost, pinned from below by the Kantorovich dual (`OllivierRicci.lean`,
`kantorovich_weak_duality`, `ollivier_plan_optimal`).  As worked theorems:
triangle `κ=½>0` (`triangle_*`), square `κ=0` (`c4_*`), double-star `κ=−2/3<0`
(`ds_*`).  A *third* counting view — transport, not incidence — returns the same
`+ / 0 / −` trichotomy, keyed to the same local clustering.

**Frame 4 — Bakry–Émery (carré du champ).** The readout is the curvature `K` in
`Γ₂(f) ≥ K·Γ(f)`, where `Γ(f) = ½Σ(f(y)−f(x))²` is the carré du champ of the
graph Laplacian and `Γ₂ = ½LΓ − Γ(f,Lf)` its iterate (`BakryEmery.lean`).  The
discrete Bochner identity makes `Γ₂` an exact sum of squares: `bochner_line`
(`4Γ₂ = (Lf(x−1))² + 2(Lf(x))² + (Lf(x+1))²`, the flat `Ric=0` form with no
negative term) gives the line `K=0`; `bochner_triangle`
(`Γ₂ = (5/2)Γ + ½(f₁−f₂)²`) gives the triangle `K=5/2>0`.  This is the Bochner
formula `½Δ|∇f|² = |Hess f|² + Ric(∇f,∇f)` read as a finite polynomial identity —
the curvature is the coefficient the Hessian-squares leave over.  It is the frame
*defined* without reference to dimension, so it is also the synthetic meaning of a
Ricci lower bound (`CD(K,N)`, Lott–Sturm–Villani) — the same number, read as an
algebraic inequality.

## Dual function

This is the classical Ricci curvature with its smooth packaging stripped: the
manifold, the metric tensor, the limit-of-triangles are redundant scaffolding
for what is, operationally, *a signed count of how neighborhoods over- or
under-lap*.  And it is sharper than the classical reading on one point —
classically Forman, Gauss–Bonnet, and Ollivier are three theorems requiring
three proofs; in 213 they are three Lens readouts of one difference-Lens fact,
and their agreement is forced, not coincidental.  The smooth manifold is the
special case where the count is replaced by a limit: `ConformalCurvature.lean`
reaches it for polynomial `λ` via `K=(|∇λ|²−λΔλ)/(2λ³)`, no transcendentals,
recovering the same flat/positive/negative trichotomy
(`conformal_curvature_trichotomy`).

## Cross-frame connection

Edge-count (`4−du−dv`), vertex-count (`2−deg`), transport-cost (`1−W₁/d`),
carré-du-champ (`Γ₂/Γ`), and conformal-limit (`K` rational) — five resolutions,
one sign↔topology fact.  What makes them one is that each is a difference-Lens
readout (§6.7): a count of how neighbourhoods over- or under-lap, then a sign.
The sign is never in the residue; it is the Bool-involution the
ordered-difference Lens supplies.  Topology (`b₁`) is what the count is
counting; the sign is how the Lens orients the count.  That the frames cannot
disagree is the content — `curvature_sign_topology` is not "a property
of `K_{3,2}`" but "what every difference-Lens reads when `b₁ ≥ 1`."  The
Bakry–Émery frame is the sharpest statement of this: there the readout is
literally an algebraic identity (`Γ₂ = Hessian-squares + K·Γ`), so the curvature
`K` is the residue the squares leave over — a thing you can point at.

## Open frontier

The smooth general-`n` Perelman `𝓦`-monotonicity stays walled
(`ricci_flow_smooth_core.md`): the conformal frame reaches the 2D case only.
The discrete trichotomy is closed on all three frames; the bridge to smooth
general dimension is the genuine open edge, not a packaging gap.
