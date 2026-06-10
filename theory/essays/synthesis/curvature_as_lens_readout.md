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

The Bakry–Émery readout is now closed **parametrically**, across whole graph
families, not just sample graphs — the curvature is an explicit function of the
combinatorics:

- **Complete graph `K_m`** (`BakryEmery.lean` §3): `bochner_complete` gives
  `4Γ₂ = (m+2)·2Γ + Σ_jΣ_{j'}(b_{j'}−b_j)²`, so `K_m` is `CD((m+2)/2, ∞)`
  (`cd_complete_graph`), **sharp** — attained with equality on constant-neighbour
  configs (`lin_yau_curvature_complete`), so `(m+2)/2` is the *optimal* (Lin–Yau)
  curvature, growing without bound as the clique densifies.
- **Star `K_{1,b}`** (§4–§5): vertex-type-dependent — the centre is `CD((3−b)/2, ∞)`
  (`cd_star`), **negative for `b ≥ 4`** (`star_negatively_curved`: a hub is a tree,
  negatively curved), while a leaf is `CD((5−b)/2, ∞)` (`cd_star_leaf`).  The star is
  not vertex-transitive, so the readout depends on *which* vertex points.
- **General bipartite `K_{a,b}`** (`BakryEmeryBipartite.lean`): the two-shell Bochner
  form `gamma2 = (3a−b)·gammaC + 2X² + b·Q_y − 4XY` (`kab_bochner`), completed over the
  free second shell (`kab_shell_sos`), gives the `A`-vertex curvature
  `min(3a−b, b−a+4)/2` — `kab_cd_wide` (`b ≥ 2a−2`, pure SOS) and `kab_cd_narrow`
  (`b ≤ 2a−2`, via the discrete Cauchy–Schwarz `cauchy_schwarz_gridZ`).  The DRLT core
  `K_{3,2}` is `CD(3/2, ∞)` (`kab_K32_pos`).

And Ollivier is closed parametrically too: `K_m` has `κ = (m−2)/(m−1) > 0`
(`OllivierRicci` §7, `km_ollivier_optimal`), the clique increasingly positively
curved — the transport mirror of the Bakry–Émery `(m+2)/2`.

## Dual function

This is the classical Ricci curvature with its smooth packaging stripped: the
manifold, the metric tensor, the limit-of-triangles are redundant scaffolding
for what is, operationally, *a signed count of how neighborhoods over- or
under-lap*.  And it is sharper than the classical reading on one point —
classically Forman, Gauss–Bonnet, and Ollivier are three theorems requiring
three proofs; in 213 each is a difference-Lens readout, and each independently
distinguishes the tree from the cyclic neighbourhood (the qualitative `+/0/−`
trichotomy is frame-independent).  What is **not** forced — and an earlier draft
of this essay overclaimed it — is that the frames agree *pointwise* on a fixed
graph: see the correction below.  The smooth manifold is the
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
counting; the sign is how the Lens orients the count.

**What is shared, and what is not (the honest boundary).**  Each frame
*independently* resolves the same qualitative split — tree vs cyclic, `+` vs `−` —
and in that sense they are one difference-Lens fact read at different resolutions.
But they are **not** a pointwise numerical (or even sign) identity, and saying so
would be the import.  The decisive counterexample is the DRLT core `K_{3,2}` itself:
the edge-count Forman reads `4 − 3 − 2 = −1 < 0` (`forman_K32`), while the
carré-du-champ Bakry–Émery reads `CD(3/2) > 0` (`kab_K32_pos`) — **opposite signs on
the same graph**.  Both readouts are correct; they are *different counts*.  The crude
edge-count is degree-dominated (it subtracts two degrees, so any `d_u+d_v > 4` reads
negative), whereas the carré-du-champ counts how the *second* neighbourhood squares
cancel — a finer over/under-lap.  So the frames cohere on the trichotomy but the
finer frames (Bakry–Émery, Ollivier) see structure the crude Forman flattens; for
the DRLT lattice the Bakry–Émery `CD(3/2)` is the transport-consistent reading.  That
"each difference-Lens reads sign↔topology" is the content; "all difference-Lenses
read the *same number*" was an over-extension — the resolutions genuinely differ.

The Bakry–Émery frame is the sharpest single statement: there the readout is
literally an algebraic identity (`Γ₂ = Hessian-squares + K·Γ`), so the curvature `K`
is the residue the squares leave over — a thing you can point at, frame and graph
fixed.

## Open frontier

The smooth general-`n` Perelman `𝓦`-monotonicity stays walled
(the Ricci-flow smooth-core frontier, `research-notes/frontiers/`): the conformal frame reaches the 2D case only.  On the
discrete side the trichotomy is closed on **four** frames (Forman, Gauss–Bonnet,
Ollivier, Bakry–Émery) across the line, complete `K_m`, star `K_{1,b}`, and general
bipartite `K_{a,b}` — parametrically, not just on samples.  The genuine open edge is
the bridge to smooth general dimension, not a packaging gap.
