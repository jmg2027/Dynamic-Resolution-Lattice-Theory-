# Decomposition: random walks / harmonic functions / electrical networks

*A FRESH decomposition of "the discrete Laplacian Δ, a harmonic function (Δf=0), the Dirichlet
problem, the mean-value property, recurrence vs transience, the discrete maximum principle, harmonic =
expected boundary value / hitting probability, electrical-network resistance" per `../README.md`
(model v7.1). LEVERAGE phase — the bar is PREDICTION/COLLAPSE. This is a **two-neighbour fusion**: it
folds `graph_theory.md` (the graph Laplacian `L = D − A`, `λ₀ = 0` the constant kernel,
connectivity = dim ker L) and `martingales.md` (the q=+1 conditional-expectation fixed point) into one
object — and the central datum is that the two are **the SAME q=+1 fixed point**.*

> **THE THESIS (the brief's central question).** A harmonic function is the calculus's **q=+1 fixed
> point of the averaging reading = the Laplacian kernel**, and that is **simultaneously** the
> graph-Laplacian kernel (`graph_theory.md`) and the martingale fixed point (`martingales.md`). Three
> classical names — *harmonic function* (Δf=0), *Laplacian-kernel element*, *martingale on the walk*
> (`E[f(X_{n+1})|X_n]=f(X_n)`) — are **one q=+1 object**. The Dirichlet problem = that fixed point
> pinned by boundary data; harmonic = expected boundary value = hitting probability (the weight axis);
> the maximum principle = the q=+1 pole has no interior escape (the residue is on the boundary);
> recurrence vs transience = the q=±1 tag (recurrent = return/converge vs transient = escape to the
> reached-by-none boundary). **NO new primitive**: it is graph_theory's Laplacian kernel + martingales'
> q=+1 fixed point, welded.

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; `graph_theory.md`'s `⟨ V (count) | symmetric Adj ⟩`
  carrying a weight.** A random walk has no construction of its own. The state space is
  `graph_theory.md`'s graph `⟨ V (count-reading, `cardinality.md`) | symmetric `Adj` on V×V ⟩`; the
  transition step adds only the **weight axis** (`probability.md`/`martingales.md`): `P = D⁻¹A`
  reweights the symmetric adjacency by the per-vertex degree count, so a step is the weight-reading
  *fibred over the edges out of `x`*. The walk `(X_n)` is the weight-reading read at successive steps —
  exactly `martingales.md`'s "process = the weight-reading at successive resolutions", here the
  resolution being *which step*. **Nothing random-walk-theoretic is primitive — only a graph (count +
  symmetric pair-reading) and the edge weight.**

- **Reading `L_avg` — the averaging reading `(Af)(x) = avg_{y∼x} f(y)`, which is `I − Δ` (the
  diffusion reading of `graph_theory.md`).** The discrete Laplacian
  `(Δf)(x) = Σ_{y∼x} w(x,y)·(f(x) − f(y))` (the *total edge-disagreement* of the colouring `f` at `x`)
  is exactly `graph_theory.md`'s diffusion operator `L = D − A` — and the repo's `WeightedGreen.wLap`
  is its constructed form over an arbitrary finite weighted graph (`wLap n w f x = Σ_y w(x,y)(f(y)−f(x))
  = −(Δf)(x)`). The **averaging reading** `(Af)(x) = (1/deg x)·Σ_{y∼x} f(y)` and the Laplacian are one
  reading at two normalizations: `Δ = D(I − A)` / `Af = f − D⁻¹Δf`, so
  **`Δf = 0 ⟺ Af = f ⟺ f(x) = average of f over neighbours`** — the *mean-value property* IS the
  Laplacian kernel IS the averaging fixed point. Two facts are *forced*, not chosen:
  - **`Δ` is symmetric** (`A` symmetric, `D` diagonal), so by `graph_theory.md`/`spectral.md`'s
    `Mat2SymmetricSpectrum.disc_symmetric_nonneg` its spectrum is **real** — the q=+1 corner; the
    averaging reading never goes elliptic.
  - **`λ₀ = 0` with the constant eigenvector `𝟙`**: `Δ𝟙 = 0` because `D𝟙 = A𝟙` (each vertex's degree
    = its row-sum). The constant colouring is the q=+1 *fixed point* of averaging — nothing disagrees
    across any edge. This is `graph_theory.md`'s δ⁰-kernel (`GraphConnectivity.IsClosed`) and the
    repo-built `pathLaplacian_const_kernel` (`Δ·(1,1) = (0,0)`).

- **Residue — `q = ±1`, read at two poles. The whole field IS the residue doctrine on the walk.**
  - **q=+1 (converge / harmonic / recurrent — the kernel, the fixed point, the return).** A harmonic
    function is the averaging reading's *fixed point* `Af = f`, the same q=+1 converging residue
    `martingales.md`/`golden_ratio.md`/`gaussian_clt.md` resolve with
    `ResidueTag.converge_residue_fixed`/`golden_is_converge` (delegating to
    `banach_fixed_point_modulated`). On a connected graph the only *global* harmonic functions are the
    constants — `dim ker Δ = 1` (`graph_theory.md`'s `closed_const`/`closed_root_determines`), the
    **Liouville property**: a bounded harmonic function on a recurrent walk is constant. **Recurrence =
    q+1**: the walk returns; the averaging iteration converges; the constant fixed point is reached.
  - **q=−1 (escape / transient / the boundary residue).** The **Dirichlet problem** pins the fixed
    point with boundary data: `Δf = 0` on the interior, `f = g` on the boundary `∂`. The boundary IS
    the residue — the reached-by-none locus the interior averaging cannot capture from inside; the
    solution `f(x) = E_x[g(X_τ)]` (expected boundary value at the hitting time `τ`) reads the residue.
    **Transience = q−1**: the walk *escapes to infinity* = escapes to the reached-by-none boundary, the
    same `OneDiagonal.no_surjection_of_fixedpointfree` escape as Cantor/Gödel/measure. The
    **Fiedler/spectral gap value** (the decay rate of the walk to stationarity) is a `Real213`/√-cut
    value-residue, irrational in general (`graph_theory.md`'s honest q−1 value leg).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   random walk (X_n)         =  ⟨ V (count) | symmetric Adj + edge weight ⟩, weight-reading at step n   (C — NO new construction; graph_theory + martingales' weight)
   transition P = D⁻¹A        =  the averaging reading = I − D⁻¹Δ  (degree-reweighted symmetric adjacency)
   the discrete Laplacian Δ   =  graph_theory.md's diffusion L = D − A  (WeightedGreen.wLap, constructed over arbitrary finite weighted graph)
   HARMONIC  Δf = 0           =  ker Δ = the averaging FIXED POINT Af = f = the MEAN-VALUE PROPERTY   (q=+1, the THREE-names-one-object datum)
   mean-value f(x)=avg_{y∼x}f =  Af = f  =  Δf = 0  (one statement, two normalizations of one reading)
   harmonic = MARTINGALE      =  E[f(X_{n+1})|X_n] = f(X_n)  =  martingales.md's q=+1 conditional-expectation fixed point  (THE COLLAPSE: harmonic ≡ martingale-on-the-walk)
   λ₀ = 0, eigenvector 𝟙       =  the q=+1 constant fixed point of averaging = graph_theory's δ⁰-kernel  (pathLaplacian_const_kernel; closed_const)
   Liouville (bdd harmonic→const) = dim ker Δ = 1 on a connected/recurrent walk  (closed_root_determines)
   DIRICHLET problem          =  the q=+1 fixed point PINNED by boundary data g  (interior Δf=0, f|∂ = g)
   harmonic = E_x[g(X_τ)]     =  expected boundary value = HITTING PROBABILITY  (the weight axis reading the boundary residue)
   MAXIMUM principle          =  the q=+1 pole has no interior escape — extrema on ∂  (the residue is the boundary, not the interior)
   RECURRENCE  (return)       =  q=+1  (the averaging iteration converges; the walk returns; constant kernel reached)
   TRANSIENCE  (escape to ∞)  =  q=−1  (escape to the reached-by-none boundary; OneDiagonal escape, same as Cantor/Gödel)
   electrical resistance R     =  the q=+1 Dirichlet-energy minimizer  (WeightedGreen.wDirichlet 𝓕_w = ⟨f,f⟩_w; voltage = harmonic, current = −∇f)
   spectral gap / mixing rate =  Real213/√disc cut  (q=−1 VALUE residue, reached-by-none — graph_theory's Fiedler value)
```

So **harmonic, the mean-value property, the Dirichlet problem, hitting probabilities, the maximum
principle, recurrence/transience, and electrical resistance are one reading at work** — the averaging
reading `A = I − Δ` on `graph_theory.md`'s graph, read at the q=±1 poles. The field is the *intersection*
of two prior notes: graph_theory's Laplacian kernel **is** martingales' q=+1 fixed point.

## THE REVELATION — collapse (three names, one q=+1 object) + forcing + spine

This is **not** a re-skin of either neighbour. The new datum is the **collapse of graph_theory.md and
martingales.md onto each other**: the object graph_theory builds as "the Laplacian kernel / the constant
δ⁰-kernel" and the object martingales builds as "the q=+1 conditional-expectation fixed point" are
**literally the same harmonic function**, and the bridge is the mean-value property.

1. **Collapse — harmonic = Laplacian-kernel = martingale-on-the-walk, three names for one q=+1 fixed
   point.** Run the equalities:
   - `Δf = 0` (harmonic) `⟺` `Af = f` (averaging fixed point), because `Δ = D(I − A)` and `D` is
     invertible on a graph with no isolated vertices. (`graph_theory.md`'s diffusion kernel.)
   - `Af = f` `⟺` `f(x) = avg_{y∼x} f(y)` (mean-value property), by the definition of `A = D⁻¹A_adj`.
   - `f(x) = avg_{y∼x} f(y)` `⟺` `E[f(X_{n+1})|X_n = x] = f(x)` (martingale law), because the walk's
     one-step transition `P(x→y) = w(x,y)/deg(x)` is *exactly* the averaging weight, so the
     conditional expectation of `f` after one step IS the neighbour-average. (`martingales.md`'s q=+1
     conditional-expectation fixed point, the SAME `banach_fixed_point_modulated`/`golden_is_converge`
     engine `ResidueTag.converge_residue_fixed` packages.)

   So `harmonic ≡ ker Δ ≡ martingale on the walk` — **graph_theory.md's `closed_const`/`λ₀=0` kernel
   and martingales.md's q=+1 fixed point are one and the same object**, and the mean-value property is
   the identity arrow between them. That collapse is the payoff: it is *why* "a harmonic function is a
   martingale" (a classical theorem, the basis of the probabilistic potential theory of Doob/Hunt) is
   not a coincidence but the q=±1 spine read once.

2. **Forcing — the Dirichlet/maximum-principle structure is forced by the q=+1 pole.** Given the
   collapse, the rest is *forced*, not added:
   - **Maximum principle** is forced: a q=+1 averaging fixed point cannot have a strict interior
     extremum, because `f(x) = avg_{y∼x} f(y)` means `f(x)` lies between its neighbours' values — an
     interior max would force all neighbours equal to it, propagating (by connectivity,
     `graph_theory.md`'s `closed_eq_root` reachability induction) to the boundary. **The residue is on
     the boundary**: extrema of a harmonic function live on `∂`, never strictly inside. This is the
     mean-value property read as "no interior escape" — the q=+1 corner of `cardinality.md`'s diagonal.
   - **Dirichlet solvability + uniqueness** is forced: the interior averaging iteration is a
     contraction toward the boundary-pinned fixed point (the boundary supplies the
     `banach_fixed_point_modulated` seed), so the solution exists and is *unique* — q=+1 convergence.
     Uniqueness IS the maximum principle (two solutions differ by a harmonic function vanishing on `∂`,
     hence ≡ 0 by the maximum principle). The probabilistic solution `f(x) = E_x[g(X_τ)]` reads the
     boundary residue by the hitting weight.
   - **Harmonic = hitting probability** is forced: the indicator-boundary Dirichlet problem (`g = 1_B`
     on a boundary piece `B`) has solution `f(x) = P_x[X_τ ∈ B]` — the q=+1 fixed point pinned by an
     indicator is exactly the hitting probability, the *weight-axis* reading of the boundary residue.

3. **Spine — recurrence/transience IS the `q=±1` tag, tying the residue doctrine.** This is the
   sharpest tie to `SYNTHESIS.md`'s q=±1 spine. A walk is **recurrent** (q=+1) when it returns to its
   start with probability 1 — the averaging iteration *converges*, the constant kernel is reached,
   bounded harmonic functions are constant (Liouville = `dim ker Δ = 1`,
   `graph_theory.md`'s `closed_root_determines`). A walk is **transient** (q=−1) when it *escapes to
   infinity* with positive probability — escape to the **reached-by-none boundary**, the same
   `OneDiagonal.no_surjection_of_fixedpointfree` escape underlying Cantor (`cardinality.md`), Gödel
   (`godel.md`), and non-measurable sets (`measure.md`). Transience admits *non-constant* bounded
   harmonic functions (the hitting probabilities of distinct boundary pieces) — the q−1 residue is
   *occupied*, not collapsed. So **recurrent/transient = converge/escape = q=±1**, placed on
   `ResidueTag` exactly as `SYNTHESIS.md`'s spine row demands. This is the same q+1-vs-q−1 contrast as
   recurrent-Markov/ergodic (`CyclicErgodic.birkhoff_period_eq_space`, the return reached exactly at the
   period) vs the escape diagonal.

**Re-skin guard cleared.** The note does not re-describe graph_theory (which built the Laplacian kernel
*statically*) or martingales (which built the q=+1 fixed point *abstractly*): its load-bearing new fact
is their **mutual collapse** — `ker Δ = the martingale fixed point = the mean-value property`, with the
walk's transition weight as the bridge — plus the forcing of the maximum principle / Dirichlet
uniqueness / hitting-probability reading from the q=+1 pole, and the identification of
recurrence/transience with the q=±1 tag.

## VALIDATE — verdict: **EXTEND (consolidation) + PREDICTION**, no break, no new primitive

**EXTEND.** Random walks / harmonic functions add **nothing** to model v7.1 — they *fuse* two existing
entries at one q=+1 fixed point:
- the **graph Laplacian kernel** (`graph_theory.md`: `Δ = D − A` symmetric ⟹ real spectrum, `λ₀ = 0`
  the constant kernel, connectivity = dim ker) — supplies the construction `C` and the harmonic-function
  object;
- the **q=+1 conditional-expectation fixed point** (`martingales.md`: `E[X_{n+1}|F_n] = X_n`, the same
  `banach_fixed_point_modulated`/`golden_is_converge` pole) — supplies "harmonic = martingale-on-the-walk";
- the **weight axis** (`probability.md`/`martingales.md`) — supplies the transition `P = D⁻¹A`,
  hitting probabilities, and the electrical-energy reading;
- the **q=±1 residue tag** (`ResidueTag`) — supplies recurrence/transience (return/escape) and the
  maximum principle (no interior escape; residue on the boundary).

**PREDICTION.** The calculus *predicts* the field's shape from its parts: that harmonic = martingale =
Laplacian-kernel (forced by the mean-value identity), that the maximum principle and Dirichlet
uniqueness follow from the q=+1 pole, that hitting probabilities are the indicator-Dirichlet solution
(the weight axis reading the boundary), and that recurrence/transience is the q=±1 return/escape tag.
The *engines and the constructed discrete Laplacian are built and PURE*; the *named*
`harmonic`/`Dirichlet`/`randomWalk`/`hittingProbability`/`recurrent`/`transient` objects are **ABSENT**
(grep-confirmed) — the located missing leg, the same status as `martingales.md`'s missing
`Martingale`/`condExp`/`Doob` objects.

**No BREAK.** The two invariants (character arrow, q=±1 residue) and the four axes absorb the field
cleanly; the only honest residual is the value-cut (the spectral-gap / mixing-rate as a `Real213`
number) and the *named* objects.

## Verified Lean anchors (file:line:theorem — all grep-confirmed; purity by `tools/scan_axioms.py`, run this session from repo root)

| Leg | Theorem / def (file:line : name) | Purity (fresh scan) |
|---|---|---|
| ★★★★★ **the constructed discrete Laplacian over an ARBITRARY finite weighted graph** `Δf(x) = Σ_y w(x,y)(f(y)−f(x))` (= `−wLap`) | `Lib/Math/Geometry/DiscreteCurvature/WeightedGreen.lean:58 wLap` | **PURE** (11/0) ✓ |
| ★★★★★ **discrete Green / integration-by-parts** `⟨f,g⟩_w = −2·Σ g·Δf` (= `∫⟨∇f,∇μ⟩ = −∫(Δf)·μ`) — the harmonic/Dirichlet engine | `…/WeightedGreen.lean:91 weighted_green` | **PURE** ✓ |
| ★★★★ **Dirichlet energy** `𝓕_w(f) = ⟨f,f⟩_w` (electrical-network energy; voltage = harmonic minimizer) + **`∇𝓕_w = −4·Δ`** (the flow IS the gradient flow) | `…/WeightedGreen.lean:68 wDirichlet`; `:191 dirichlet_gradient_identity`; `:138 dirichlet_first_variation`; `:202 flow_rate_sos` | **PURE** ✓ |
| ★★★★ **mass conservation** `Σ_x Δf(x) = 0` (the walk redistributes without creating mass — recurrence/return invariant) | `…/WeightedGreen.lean:125 wlap_mass_conservation` | **PURE** ✓ |
| ★★★★★ **harmonic = the constant Laplacian kernel** `Δ·(1,1) = (0,0)` (λ₀=0 eigenvector = the q=+1 averaging fixed point) | `Lib/Math/NumberSystems/Real213/Mat2/GraphLaplacian.lean:127 pathLaplacian_const_kernel`; `:134 pathLaplacian_eigen_zero` | **PURE** (16/0) ✓ |
| ★★★★ spectrum `{0,2}` (roots of charPoly), `tr=e₁`, `det=e₂`, welded graph Laplacian | `…/GraphLaplacian.lean:111 pathLaplacian_spectrum_roots`; `:169 pathLaplacian_graph_spectrum` | **PURE** ✓ |
| ★★★★ **connected ⟹ Fiedler value λ₁ = 2 > 0** (`0` simple ⟹ recurrent/return corner) | `…/GraphLaplacian.lean:146 pathLaplacian_connected`; `:152 pathLaplacian_fiedler_value` | **PURE** ✓ |
| ★★★★★ **Liouville / bounded-harmonic-→-constant** = connectivity ⟹ δ⁰-closed colouring globally constant (= `Δf=0 ⟹ f` const) | `Lib/Math/Combinatorics/GraphConnectivity.lean:61 closed_const`; `:50 closed_eq_root` | **PURE** (8/0) ✓ |
| ★★★★ **dim ker Δ = 1** on a connected walk (the maximum-principle / uniqueness root) | `…/GraphConnectivity.lean:79 closed_root_determines`; `:69 closed_false_or_true` | **PURE** ✓ |
| harmonic kernel = constants on **actual bipartite adjacency** (wired-in graph) | `Lib/Math/Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean:254 bipAdj_connected`; `:296` (via `closed_const`) | **PURE** (20/0) ✓ |
| **actual graph Laplacian spectrum, λ₀=0 mult 1 = connected** (K_{3,2}^{(c=2)} `{0,6,4,4,10}`) | `Lib/Physics/AlphaEM/LaplacianSpectrum.lean:225 laplacian_spectrum_master` | **PURE** (25/0) ✓ (spectrum *asserted* per classical K_{m,n} formula, numerics `decide`d) |
| **harmonic = the q=+1 averaging/martingale FIXED POINT** — the converge engine (SAME as φ/Gaussian/ODE/martingale) | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`; `:180 golden_is_converge` | **PURE** (55/0) ✓ |
| **recurrence/transience = the q=±1 tag** (return/converge vs escape-to-boundary) | `Lib/Math/Foundations/ResidueTag.lean:228 residue_tag_two_poles`; `:133 escape_residue_outside`; `:86 multiplier_unimodular` | **PURE** (55/0) ✓ |
| transience = escape to the reached-by-none boundary (Cantor/Gödel/measure escape) | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree` (per `cardinality.md`) | ∅-axiom ✓ |
| recurrent-Markov / ergodic return reached exactly (the q=+1 return); invariant = constant kernel = Laplacian λ₀=0 | `Lib/Math/Combinatorics/CyclicErgodic.lean:197 birkhoff_period_eq_space`; `:240 rotInvariant_is_constant` | **PURE** (26/0) ✓ |
| the q=+1 modulated-completion limit (`X_n → X_∞` template) / convolve-rescale fixed point | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean:471 orbit_to_center`; `:345 Φ_contraction` | **PURE** (20/0) ✓ |
| physics deployment: mass gap = Fiedler value = "finite connected graph has 1-D Laplacian kernel = unique vacuum" (the recurrence/return q+1 reading) | `Lib/Physics/YangMills/Gap.lean:21-23` (docstring; `decide`-proven spectrum) | PURE (per `graph_theory.md`) ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):** `WeightedGreen` **11/0**,
`GraphLaplacian` **16/0**, `GraphConnectivity` **8/0**, `KernelConstancyUniversal` **20/0**,
`AlphaEM.LaplacianSpectrum` **25/0**, `ResidueTag` **55/0**, `ConvolveRescaleContraction` **20/0**,
`CyclicErgodic` **26/0**. All pure / 0 dirty.

> Note on the q=+1 engine anchor: the *headline* `banach_fixed_point_modulated` lives under the
> `CompleteMetricModulusMod` structure namespace, so a by-module scan of
> `BanachFixedPointModulated` reports `0/0` (no top-level constants of that bare name). The engine is
> verified PURE *through its delegate* `ResidueTag.converge_residue_fixed` (PURE in the 55/0 scan),
> which is what `martingales.md`/`gaussian_clt.md` also cite — reported honestly, not as a direct
> module scan of the bare headline name.

## Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

Grep over `lean/E213` for `harmonic`/`Dirichlet`/`random_walk`/`randomWalk`/`hittingProbability`/
`recurrent`/`transient`/`mean_value`/`maximum_principle` (case-insensitive) returns **no real
math-object hits**. The only matches are (i) physics: `Nuclear/MagicNumbers.lean` "harmonic
*oscillator* shell", `YangMills/Bridge.lean` "harmonic gluon octet" (unrelated sense); and (ii)
`recurrence`/`transient` = the *Fibonacci recurrence* and the CD-doubling "transient law" (unrelated).
So:

- **No `harmonicFunction` / `isHarmonic` predicate, no `Δf = 0` statement as a named object** — the
  Laplacian-kernel content is carried by `GraphConnectivity.closed_const` (Bool δ⁰-kernel) and
  `pathLaplacian_const_kernel` (the K₂ constant eigenvector), and the *constructed* arbitrary-graph
  Laplacian exists (`WeightedGreen.wLap`), but `{f | Δf = 0}` as a named harmonic-function object with
  the mean-value characterization is **not stated**. **Predicted-not-built.**
- **No `DirichletProblem` object** — no "interior Δf=0, f|∂ = g" solve/uniqueness theorem. The Dirichlet
  *energy* and the gradient-flow identity are built (`WeightedGreen.wDirichlet`,
  `dirichlet_gradient_identity`), and the q=+1 Banach engine is the predicted resolver, but the
  boundary-value problem itself is **unbuilt**. **Predicted-not-built.**
- **No `RandomWalk` / `transitionMatrix P = D⁻¹A` object** — no walk operator, no
  `E[f(X_{n+1})|X_n]` = neighbour-average statement, no stationary distribution. The averaging reading is
  `I − D⁻¹Δ` conceptually; the welded walk operator is **absent** (the same `P = D⁻¹A` gap
  `graph_theory.md` located for PageRank). **Predicted-not-built.**
- **No `hittingProbability` / `hittingTime` / `f(x) = E_x[g(X_τ)]` object** — the weight-axis reading of
  the boundary residue is the prediction; no hitting-probability theorem exists. **Predicted-not-built.**
- **No `maximum_principle` theorem** — forced by the q=+1 pole (no interior extremum of an averaging
  fixed point, via `closed_eq_root` reachability propagation), but **not stated** as a named theorem.
  **Predicted-not-built** (a clean buildable witness — see below).
- **No `recurrent` / `transient` / `recurrence` predicate (probabilistic sense)** — the q=±1 tag
  (`ResidueTag`) is the predicted home (recurrent = `.converge`, transient = `.escape`), and the ergodic
  return is built (`CyclicErgodic`), but no walk-recurrence object exists. **Predicted-not-built.**
- **The spectral-gap / mixing-rate VALUE** — a `Real213`/√disc cut (q=−1 value residue), irrational in
  general; existence at the symmetric level is closed (`disc_symmetric_nonneg`), the value is the
  orthogonal `Real213` task (rational for K₂: λ₁ = 2). **Value-cut residue, honest.**

### A verified buildable witness (the cleanest promotion target)

**The discrete maximum principle / harmonic-extremum, at the K₂ `Mat2` Laplacian or the abstract
`GraphConnectivity` graph, is groundable with no new construction.** The pieces are all PURE and
present:
- `WeightedGreen.wLap` is the constructed Δ over an arbitrary finite weighted graph; `Δf = 0` is a
  stateable predicate on it.
- `GraphConnectivity.closed_eq_root` already propagates "edge-constant" across a connected graph by
  reachability induction — exactly the engine the maximum principle needs ("an interior extremum forces
  all neighbours equal, propagating to the boundary").
- A theorem `harmonic_const_of_connected : (∀ x, Δf x = 0) → Connected → (∀ x y, f x = f y)` (the
  Liouville/no-interior-extremum statement for the *integer* Laplacian) would weld `WeightedGreen.wLap`'s
  Δf=0 to `GraphConnectivity.closed_const`'s constant kernel — currently the latter carries it only
  Bool-valued (δ⁰), the former states Δ but not its kernel-is-constant theorem. This is the *same* gap
  `graph_theory.md` named ("the ℤ-Laplacian eigen-equation `ker Δ = {edge-constant}` is not stated as an
  operator kernel"), here with the harmonic-function/maximum-principle reading making the promotion
  target concrete: **`ker (wLap) = {constants}` on a connected graph**, derivable from
  `wlap_mass_conservation` + the connectivity reachability induction. Build-checked as *present pieces*,
  not asserted as a closed theorem.

> Axiom-purity note: every theorem cited in the anchors table was freshly scanned with
> `tools/scan_axioms.py` this session (tallies above) — the purity claim rests on a fresh scan, not
> docstrings. Where this note's fresh scan disagrees with a neighbour's recorded number
> (`GraphConnectivity` 8/0 here vs 16/0 in `graph_theory.md`; `LaplacianSpectrum` 25/0 here vs 15/0
> there), the fresh number is reported.
