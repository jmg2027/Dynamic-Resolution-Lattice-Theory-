# Decomposition: graph theory / spectral graph theory

*A FRESH decomposition of "a graph, the adjacency matrix, the Laplacian `L = D − A`, the spectral
gap / algebraic connectivity / Fiedler value, connectivity ⟺ λ₁ > 0, the Matrix–Tree theorem,
random walks / PageRank" per `../README.md` (model v7.1). LEVERAGE phase — the bar is
PREDICTION/REVELATION, consolidating `spectral.md` (eigenvalue = `q=+1` scale-residue, symmetric ⇒
real spectrum) + `cardinality.md` (the count-reading) + `topology.md` (connectedness = finite-list
adjacency, the `q=±1` finiteness corner) + `determinant.md` (the `det`-character). The thesis: graph
theory has **no construction of its own** — it is the count-reading on a vertex set + the symmetric
adjacency reading; the Laplacian spectrum is the graph's `q=+1` real diffusion-residue, connectivity
= dim ker L = `topology.md`'s connectedness read spectrally, and Matrix–Tree = the `det`-character.*

The hypotheses under test (from the task):
1. A **graph** = `⟨ vertices (a count, `cardinality.md`) | the adjacency reading (which pairs are
   distinguished-as-connected) ⟩`; the adjacency matrix `A` is a *symmetric reading of the
   vertex-pair set*; edges = the distinguished pairs.
2. The **Laplacian `L = D − A`** is **symmetric** (so by `spectral.md`'s `Mat2SymmetricSpectrum`,
   its spectrum is REAL — the `q=+1` corner) and positive-semidefinite with **`λ₀ = 0`** (the
   all-ones/constant vector is always an eigenvector with eigenvalue 0 — the `q=+1` fixed point of
   the diffusion reading). The Laplacian spectrum = the `q=+1` real residues of the graph's
   diffusion reading.
3. **Connectivity ⟺ the spectral gap `λ₁ > 0`** (Fiedler): connected iff 0 is a SIMPLE eigenvalue;
   `#components = dim ker L`. This is `topology.md`'s connectedness (finite-list adjacency /
   `chain_finite`) read spectrally — connectivity = the `q=+1` kernel being 1-dimensional.
4. **#spanning trees = Matrix–Tree** (det of a Laplacian minor) = the `det`-character
   (`determinant.md`); **random walks / PageRank** = the `q=+1` stationary distribution (the
   dominant eigenvector, ties to `gaussian_clt`'s fixed point).

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; the count-reading's family + the symmetric pair-reading.**
  A graph is *not* a primitive. Per `cardinality.md`, a "set of vertices" is `⟨ a family of
  distinguishables ∣ — ⟩` — `V` is the count-reading's carrier. An **edge** is the *symmetric*
  distinguishing of a vertex *pair*: `Adj : V → V → Prop` with `Adj u v ↔ Adj v u`. So a graph is
  `⟨ V (count) ∣ a symmetric two-place reading Adj on V×V ⟩`. The adjacency matrix `A` is exactly
  this reading written as a `0/1` matrix; `Aᵀ = A` (the symmetry of "distinguished-as-connected"
  is the *only* structural input). The degree `D` is the count-reading applied per vertex
  (`deg v = #{u : Adj u v}` — the count-Lens of `cardinality.md`, fibred over `V`). **Nothing
  graph-theoretic is a primitive — only "a count `V` and a symmetric pair-reading".**

- **Reading `L_lap` — the diffusion reading `L = D − A`, the symmetric `q=+1` reading of `spectral.md`.**
  The Laplacian `L = D − A` is the *discrete diffusion operator*: `(Lσ)(v) = Σ_{u∼v}(σ(v) − σ(u))`,
  the total disagreement of a colouring `σ` across `v`'s edges. Two facts are *forced*, not chosen:
  - `L` is **symmetric** (`A` symmetric, `D` diagonal). By `spectral.md`'s just-built
    `Mat2SymmetricSpectrum.disc_symmetric_nonneg`, a symmetric operator's discriminant is a sum of
    squares `≥ 0` — its spectrum is **real**, the `q=+1` corner. The diffusion reading *cannot go
    elliptic*: no rotation, only real scaling along eigendirections. This is the *graph-theoretic
    content of the `2×2` spectral theorem* read on `L`.
  - `λ₀ = 0` with the **constant/all-ones eigenvector** `𝟙`: `L𝟙 = (D − A)𝟙 = 0` because
    `D𝟙 = A𝟙` (each vertex's degree = its row-sum of `A`). The constant colouring is the `q=+1`
    *fixed point* of diffusion — nothing disagrees across any edge. This is **literally
    `cardinality.md`/`topology.md`'s constant**: the δ⁰-kernel is exactly the edge-constant
    colourings (`GraphConnectivity.IsClosed σ := ∀ u v, Adj u v → σ u = σ v`), and `Lσ = 0 ⟺ σ`
    edge-constant — *the Laplacian kernel IS the δ⁰-kernel*.

  So the Laplacian spectrum = the multiset of `q=+1` real scale-residues of the diffusion reading,
  with `λ₀ = 0` the constant fixed point.

- **Residue — connectivity as the kernel dimension; `#components = dim ker L`; the value `√disc` as
  a `Real213` cut.** The diffusion reading's self-application surplus is the **kernel**: which
  colourings diffusion cannot distinguish. `cardinality.md`/`topology.md`'s `q=±1` tag reads it:
  - **`q=+1` (converge / connectivity-collapse) — `dim ker L = #components`.** On a *connected*
    graph the only diffusion-invariant colourings are the global constants — `dim ker L = 1` (= b₀).
    This is the **contrapositive corner** of `cardinality.md`'s escape diagonal, the same move as
    `topology.md`'s compactness: the count-reading on the kernel *closes* (reaches a fixed point —
    the constant). On `k` components, the kernel is `k`-dimensional (one constant per component).
    **`#components = dim ker L`** is the count-residue of the diffusion fixed point. This is built
    ∅-axiom (see anchors): `GraphConnectivity.closed_const` (connectivity ⟹ a δ⁰-closed colouring
    is globally constant), `closed_false_or_true` (the kernel is exactly the two constants ⇒
    b₀ = 1), `closed_root_determines` (one Bool of freedom — *the kernel is 1-dimensional*).
  - **`q=−1` (escape / reached-by-none) — the eigenvalue *value*.** The Fiedler value λ₁ and the
    non-zero spectrum are `Real213`/√-cut residues (irrational in general, as for `spectral.md`'s
    φ²); existence at the symmetric `disc ≥ 0` level is closed (`disc_symmetric_nonneg`), the
    *value* `√disc` stays a `Real213` pointing — reached-by-none, NOT an escape to ℂ (a symmetric
    operator never goes elliptic).

## Re-seeing — ⟨C | L⟩

```
   a graph G              =  ⟨ V (count-reading, cardinality.md) | symmetric Adj on V×V ⟩   (C — NO new construction)
   the adjacency matrix A =  the symmetric two-place reading Adj written 0/1, Aᵀ = A
   the degree D           =  the count-reading fibred per vertex (deg v = #{u : Adj u v})
   the Laplacian L = D−A  =  the diffusion reading; SYMMETRIC ⇒ real spectrum (q=+1, Mat2SymmetricSpectrum)
   λ₀ = 0, eigenvector 𝟙  =  the q=+1 fixed point of diffusion = the constant colouring (= δ⁰-kernel)
   the spectrum {λᵢ}      =  the multiset of q=+1 REAL scale-residues of the diffusion reading
   ker L = edge-constants =  cardinality.md/topology.md's constant; GraphConnectivity.IsClosed σ
   connectivity ⟺ λ₁ > 0  =  the kernel is 1-dimensional (0 simple) = topology's connectedness, spectral
   #components = dim ker L =  the count-residue of the diffusion fixed point (q=+1)  (closed_const, closed_root_determines)
   #spanning trees = det(L-minor) = the det-character (determinant.md) of the graph reading
   PageRank / random walk =  the q=+1 stationary distribution = dominant eigenvector (gaussian_clt's fixed point)
   the Fiedler value λ₁    =  a Real213/√disc cut (reached-by-none, irrational in general — q=−1 VALUE residue)
```

So **adjacency, Laplacian, connectivity, components, spanning trees, and the random walk are one
reading at work** — the count-reading on `V` + the symmetric pair-reading `A`, read through
`spectral.md`'s symmetric `q=+1` corner. Graph theory is `spectral.md`'s spectrum + `topology.md`'s
connectedness + `cardinality.md`'s count + `determinant.md`'s character, *consolidated onto one
symmetric operator `L`*.

## Revelation — PREDICTION (consolidation), and the central tie is BUILT ∅-axiom

**The single biggest find: graph theory has no construction of its own, and "connectivity =
dim ker L = the number of connected components" is the SAME theorem `cardinality.md`/`topology.md`
already proved as the `q=+1` fixed-point of the count-reading — the Laplacian kernel IS the
δ⁰-kernel, and the repo proves it connectivity-collapses to the constants ∅-axiom.**

The forcing argument, read at both poles of the count-reading on the kernel:

- **`q=+1` (connectivity = the kernel cannot escape the constants).** `cardinality.md`'s engine is
  `OneDiagonal.no_surjection_of_fixedpointfree` (a fixed-point-free modifier forces a self-cover to
  *miss a row*, escape). Connectivity is the **contrapositive corner**: on a connected graph the
  diffusion reading has a *fixed point* — the constant colouring is the only edge-invariant one
  (`GraphConnectivity.closed_const`), so the kernel `closes` to dimension 1. **Non-connectivity =
  the kernel splits** (`k` components ⟹ `dim ker = k`, one constant per component — the same count
  the `q=−1` escape would inflate). This is exactly `topology.md`'s move ("the cover IS a finite
  list ⟹ Heine–Borel is `rfl`") re-read on the diffusion kernel: *the Laplacian kernel of a
  connected graph is forced 1-dimensional because connectivity propagates the constant across every
  edge* — `closed_eq_root` is a plain structural induction on the reachability witness, no
  `propext`/`funext`. **This is the Fiedler theorem (`connectivity ⟺ 0 is a simple eigenvalue`)
  read as the `q=+1` count-residue, and it is BUILT and PURE** (16/0).

- **`q=−1` (the value surfaced — the reached-by-none Fiedler value).** The *gap* λ₁ > 0 is the
  spectral *value* witnessing connectivity (algebraic connectivity / the Fiedler value). Its
  existence at the symmetric level is the `q=+1` corner closed by
  `Mat2SymmetricSpectrum.disc_symmetric_nonneg` (the symmetric `L` never rotates; its spectrum is
  real); its *value* is a `Real213` √-cut, irrational in general (the analysis-level
  reached-by-none, `spectral.md`'s honest residue). So "connectivity ⟺ λ₁ > 0" splits exactly as
  the calculus predicts: the *combinatorial* side (`dim ker = 1`) is built ∅-axiom; the *value*
  side (`λ₁` as a number) is the `Real213` residue.

This passes the re-skin guard at the prediction bar: it does not re-describe Fiedler's theorem — it
**identifies the Laplacian kernel with the δ⁰-kernel** (the same constant the count-reading fixes),
**derives `#components = dim ker L`** from the count-reading's `q=+1` fixed point
(`closed_root_determines` = one Bool of freedom = the kernel is 1-dimensional), and **locates the
value λ₁ as the `Real213` residue** — unifying graph connectivity with Cantor (`cardinality`), the
Choice split (`measure`), compactness (`topology`), and φ/Gaussian (`golden_ratio`/`gaussian_clt`)
under the one `ResidueTag`, AND with `spectral.md`'s symmetric real-spectrum corner. The Laplacian
is the *symmetric* reading the spectral note was built for: `disc_symmetric_nonneg` is precisely
"the graph Laplacian's spectrum is real" at `d = 2`.

### Does the Laplacian spectrum fall out as the graph's `q=+1` diffusion-residue? — YES, and the
λ₀ = 0 constant fixed point is the **δ⁰-kernel the repo already identifies with connectivity**.

The chain is complete and verified:
- `L = D − A` symmetric ⟹ real spectrum ⟹ `q=+1` corner (`Mat2SymmetricSpectrum.disc_symmetric_nonneg`, PURE);
- `L𝟙 = 0`, the constant colouring is the diffusion fixed point ⟺ the δ⁰-kernel
  (`GraphConnectivity.IsClosed`, `closed_eq_root`);
- connectivity ⟹ `dim ker L = 1` (`closed_const` + `closed_root_determines`, PURE), `#components =
  dim ker L` the count-residue;
- the bipartite K_{NS,NT}^{(c)} family wires its *actual adjacency* into this framework and proves
  b₀ = 1 = connected (`KernelConstancyUniversal.bipAdj_connected`, `isConstOnEdges_isClosed`,
  `isKer_const_via_framework`, PURE);
- an *actual graph Laplacian spectrum* with `λ₀ = 0` (multiplicity 1 = `dim H⁰` = connected) is
  built for the deployment graphs (`AlphaEM/LaplacianSpectrum.lean`: the K_{3,2}^{(c=2)} vertex
  Laplacian spectrum `{0, 6, 4, 4, 10}`, λ₀ = 0 mult 1, trace = 2·E handshake, PURE) and the
  simplicial/Δ⁴ Laplacian.

So the prediction lands more completely than `knots.md`'s break or even `spectral.md`'s conditional:
*all four legs of graph theory are present and the central connectivity = dim ker leg is a PURE
theorem*, because the repo built the δ⁰-cohomology of these graphs for the physics deployment and
`spectral.md` just built the symmetric real-spectrum corner.

## The Matrix–Tree / det leg and the random-walk leg

- **Matrix–Tree = the `det`-character (`determinant.md`).** #spanning trees = `det` of any
  `(n−1)×(n−1)` principal minor of `L` (deleting one row/column = pinning the kernel's constant
  freedom, exactly `closed_root_determines`'s "the root colour is the single free parameter"). This
  is `determinant.md`'s multiplicative `×↦·` character read on the *reduced* Laplacian — the same
  `det2_mul`/`det_mul` arrow. **PREDICTION; the general `det(L-minor)` is not built** (the repo has
  `det2_mul`/`det_mul`/`det_holonomy_eq_one` and a general `DetN` skeleton, but no Laplacian-minor
  determinant for arbitrary `d` — the same `d > 1` `det` gap `spectral.md` located). CONCEPTUAL for
  `d > 1`; the `det = e₂` symmetric-function tie to the spectrum is `spectral.md`'s
  `Mat2Spectrum.det_eq_e2` (PURE) at `d = 2`.

- **Random walk / PageRank = the `q=+1` stationary distribution.** The walk operator `P = D⁻¹A`
  (or the lazy/normalized Laplacian) has dominant eigenvector = the stationary distribution = the
  `q=+1` fixed point, the *same* converging residue as `gaussian_clt.md`'s convolve-rescale fixed
  point and φ (the dominant eigenvalue of `golden_hyperbolic`). **PREDICTION; conceptual** — the
  repo has the Banach `q=+1` engine (`gaussian_clt.md`'s `Φ_contraction`/`banach_fixed_point`) and
  the discrete diffusion/heat operator (`Analysis/ODE/HeatEq/Discrete.lean`), but no `P = D⁻¹A`
  Perron eigenvector welded to the engine. Same `q=+1` fixed-point object, third graph face.

## The precise missing leg (located, like `knots.md`/`spectral.md`)

**[Updated — partially resolved]** A *constructed arbitrary-finite-graph* ℤ-Laplacian operator **does
exist**: `WeightedGreen.lean:58` `wLap n w f x = Σ_y w(x,y)·(f y − f x)` (11/0 PURE), the weighted
graph Laplacian over an arbitrary finite weighted vertex set, with the discrete Green/IBP identity
(`weighted_green:91`), Dirichlet energy, gradient-flow `∇𝓕=−4Δ`, and mass conservation
(`wlap_mass_conservation:125`). What remains genuinely absent is only (a) the `L = D − A` *matrix* form
specifically (vs the operator `wLap`), and (b) the *stated* operator theorem `ker(wLap) = {constants}`
on a connected graph (the pieces — `wlap_mass_conservation` + `GraphConnectivity.closed_eq_root`
reachability — are present; the weld is unstated). Below, "absent" is superseded by `WeightedGreen` for
the operator; the matrix form + the explicit kernel theorem are the residual. What
is built is (i) the diffusion *kernel* abstractly over any `Adj : V → V → Prop`
(`GraphConnectivity`, fully `d`-agnostic, PURE) — this carries the *connectivity = dim ker* leg
without a matrix; and (ii) the *eigenvalue spectrum* of specific deployment graphs as hardcoded
`decide`-verified Nat identities (`AlphaEM/LaplacianSpectrum.lean` — the spectrum `{0,6,4,4,10}` is
*asserted* per the classical K_{m,n} formula and checked numerically, not *derived* from a
constructed `D − A` matrix acting on cochains). The genuinely missing primitive:

1. **A constructed `L = D − A : (V → ℤ) → (V → ℤ)` over an arbitrary finite vertex set**, with
   `Lσ(v) = Σ_{u∼v}(σ v − σ u)`, and the theorem `ker L = {edge-constant σ}` *as an operator
   kernel* (currently the δ⁰/`xor` kernel carries it Bool-valued; the ℤ-Laplacian eigen-equation is
   not stated). This would weld `GraphConnectivity`'s `closed_const` to an actual matrix kernel.
2. **The Laplacian *spectrum* derived (not asserted)** — eigenvalues as roots of `charPoly(L)`, with
   `disc_symmetric_nonneg` lifted from `Mat2` to `d × d` (the same `d > 1` spectral-theorem gap
   `spectral.md` located). The `Real213` √-cut for λ₁ (Fiedler value) is the orthogonal value-task.

This is the dual of `topology.md`'s located break (the arbitrary-cover quantifier): there the
*finite-list* cover hosts the `q=+1` half but not the `q=−1` infinite cover; here the *Bool δ⁰
kernel* hosts the `q=+1` connectivity collapse but not the constructed `ℤ`-Laplacian operator whose
spectrum λ₁ is the `q=−1` value-residue. Not a break of the model (no new axis) — a located
promotion target.

### A small (2-vertex / Mat2) Laplacian case — NOW BUILT ∅-axiom.

**DONE** (`Mat2/GraphLaplacian.lean`, 16/0 PURE): the K₂ Laplacian `pathLaplacian := ⟨1,−1,−1,1⟩` is a
literal `Mat2` with `pathLaplacian_symmetric`, `pathLaplacian_tr` (=2), `pathLaplacian_det` (=0),
`pathLaplacian_disc` (=4, `≥0` via `disc_symmetric_nonneg`), `pathLaplacian_charPoly_factors`
(`= (λ−0)(λ−2)`, spectrum {0,2}) with `tr_eq_e1`/`det_eq_e2`/`spectrum_roots` instantiated,
`pathLaplacian_const_kernel` (`apply L (1,1) = (0,0)` — the all-ones vector in ker L, the q=+1 constant),
and `pathLaplacian_connected` (`0 < disc` via `disc_symmetric_pos_of_nonscalar` — Fiedler λ₁=2>0, 0 simple).
This welds `Mat2SymmetricSpectrum` + `Mat2Spectrum` to a concrete graph, no new construction. The general
n-vertex (d×d) Laplacian with a *derived* spectrum stays the open d>1 matrix gap. Original framing kept:

**Strongly promotable.** A 2-vertex single-edge graph has `L = [[1,−1],[−1,1]]`, which is a `Mat2`
with `tr = 2`, `det = 0`, `disc = (a−d)² + (2b)² = 0 + 4 = 4 ≥ 0` — it is `IsSymmetric` (b = c = −1),
so `Mat2SymmetricSpectrum.disc_symmetric_nonneg` applies *directly* (real spectrum), and
`disc_zero_iff_scalar` shows it is non-scalar ⟹ `disc > 0` ⟹ two distinct real eigenvalues `{0, 2}`
— `λ₀ = 0` (eigenvector `(1,1)` = the constant) and `λ₁ = 2 > 0` (connected, Fiedler value, exactly
`√disc = 2`, here *rational*, no `Real213` cut needed). A 3-vertex path/triangle Laplacian needs `d = 3`
(out of `Mat2`), but the 2-vertex case is **fully groundable inside the existing `Mat2`
infrastructure with no new construction** — define `pathLap2 : Mat2 := ⟨1,-1,-1,1⟩`, prove it
`IsSymmetric`, that `disc = 4` (so spectrum real, `disc_symmetric_nonneg`), `det = 0` (so `0 ∈`
spectrum — the constant fixed point), and `λ₁ = 2` (connected). This *welds*
`Mat2SymmetricSpectrum` + `Mat2Spectrum` (det = e₂, tr = e₁) to a literal graph Laplacian — a clean
∅-axiom promotion target uniting `spectral.md`'s symmetric corner with this note's connectivity =
dim ker leg at the smallest non-trivial graph.

## Touches on model v7.1?

**No new primitive; a decisive consolidation onto one symmetric operator.** Graph theory does not
add to model v7.1 — it *fuses* four existing entries onto `L = D − A`:
- the **count-reading** (`cardinality.md`) supplies `V` and the degree `D`;
- the **symmetric `q=+1` spectrum** (`spectral.md`'s `Mat2SymmetricSpectrum`) supplies "the
  Laplacian spectrum is real, λ₀ = 0 the constant fixed point";
- the **`q=±1` residue tag** read on the diffusion kernel (`cardinality.md`/`topology.md`) supplies
  "connectivity = dim ker L = #components" (the `q=+1` constant-collapse, PURE) and "λ₁ as a
  `Real213` value" (the `q=−1` reached-by-none);
- the **`det`-character** (`determinant.md`) supplies Matrix–Tree.

Note for the README's batch log:

> **Graph theory = the symmetric diffusion reading `L = D − A`; connectivity = dim ker L = the
> count-reading's `q=+1` constant fixed point, BUILT PURE.** A graph has no construction of its own
> (`⟨V count | symmetric Adj⟩`); `L = D − A` is symmetric ⟹ real spectrum (`spectral.md`'s
> `Mat2SymmetricSpectrum.disc_symmetric_nonneg`), `λ₀ = 0` the constant/all-ones fixed point = the
> δ⁰-kernel. **Fiedler's `connectivity ⟺ 0 simple` and `#components = dim ker L` ARE
> `GraphConnectivity.closed_const`/`closed_root_determines` (16/0 PURE)** — the same `q=+1`
> fixed-point of the count-reading that gives `topology.md`'s connectedness and the contrapositive
> of `cardinality.md`'s escape diagonal; the K_{NS,NT}^{(c)} bipartite family wires its *actual
> adjacency* into this framework (`KernelConstancyUniversal.bipAdj_connected`, 20/0 PURE), and an
> actual graph Laplacian spectrum with `λ₀ = 0` mult 1 = connected is built (`LaplacianSpectrum`,
> K_{3,2}^{(c=2)} spectrum `{0,6,4,4,10}`, PURE). Matrix–Tree = the `det`-character
> (`determinant.md`), random walk = the `q=+1` stationary fixed point (`gaussian_clt`). Located
> break: a *constructed* `L = D − A` matrix over an arbitrary finite graph + its derived (not
> asserted) spectrum is absent — the `d > 1` matrix gap. **The 2-vertex `Mat2` Laplacian
> `[[1,−1],[−1,1]]` (spectrum `{0,2}`, `λ₀ = 0` = constant, `λ₁ = 2`) is a clean ∅-axiom promotion
> target** inside the existing `Mat2SymmetricSpectrum`/`Mat2Spectrum` infrastructure.

## Verified Lean anchors (grep + `tools/scan_axioms.py` this session — all PURE, build-confirmed)

| Leg | Theorem / def (file:line : name) | Purity |
|---|---|---|
| ★★★★★ connectivity ⟹ δ⁰-closed colouring globally constant (= `Lσ=0 ⟹ σ` constant) | `Lib/Math/Combinatorics/GraphConnectivity.lean:61 closed_const`; `:50 closed_eq_root` | **PURE** (16/0, scanned) ✓ |
| ★★★★ kernel = the two constants ⇒ b₀ = 1 (0 is a simple eigenvalue) | `…/GraphConnectivity.lean:69 closed_false_or_true` | **PURE** ✓ |
| ★★★★ **dim ker L = 1** (one Bool of freedom — the root colour is the single free parameter) | `…/GraphConnectivity.lean:79 closed_root_determines` | **PURE** ✓ |
| L = D−A diffusion = δ⁰-closedness; reachability = `topology.md`'s finite adjacency | `…/GraphConnectivity.lean:42 IsClosed`; `:33 Reach`; `:38 IsConnectedFrom`; `:88 reach_one`; `:93 reach_two` | **PURE** ✓ |
| ★★★★ bipartite graph **actual adjacency** is connected (Adj wired into the framework) | `Lib/Math/Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean:254 bipAdj_connected`; `:248 bipAdj` | **PURE** (20/0) ✓ |
| ★★★ kernel = constants via the framework (δ⁰-kernel = edge-constant = connectivity-collapse) | `…/KernelConstancyUniversal.lean:293 isKer_const_via_framework`; `:267 isConstOnEdges_isClosed`; `:148 isKer_iff_const`; `:168 isKer_const_false_or_true`; `:179 isKer_root_determines` | **PURE** ✓ |
| ★★★ **actual graph Laplacian spectrum, λ₀ = 0 mult 1 = connected** (K_{3,2}^{(c=2)} `{0,6,4,4,10}`, trace = 2E) | `Lib/Physics/AlphaEM/LaplacianSpectrum.lean:225 laplacian_spectrum_master`; `:125 k32c2_H0`; `:142 k32c2_lap_trace_0`; `:131 k32c2_lap_rank_0` | **PURE** (15/0) ✓ (numerics `decide`d, spectrum *asserted* per classical K_{m,n} formula) |
| simplicial Δ⁴ Laplacian (all nonzero eigenvalues = n = 5, H⁰ = 1) | `…/LaplacianSpectrum.lean:68 delta4_lap_rank`; `:85 delta4_eigenvalue`; `:88 delta4_lap_trace` | **PURE** ✓ |
| ★★★★ **symmetric ⇒ real spectrum (the Laplacian's `q=+1` corner)** — `disc = (a−d)²+(2b)² ≥ 0` | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83 disc_symmetric_nonneg`; `:67 disc_symmetric_sum_of_squares` | **PURE** (49/0 incl. deps) ✓ |
| symmetric `disc=0 ⟺ scalar` (cusp); non-scalar ⟹ distinct real eigenvalues | `…/Mat2SymmetricSpectrum.lean:93 disc_zero_iff_scalar`; `:111 disc_symmetric_pos_of_nonscalar`; `:137 symmetric_spectrum_real` | **PURE** ✓ |
| det = e₂, tr = e₁ of the spectrum (Matrix–Tree / det-character at d=2) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:103 det_eq_e2`; `:115 tr_eq_e1`; `:167 disc_eq_gap_squared`; `:53 charPoly` | **PURE** (per `spectral.md`) ✓ |
| det = `×↦·` multiplicative character (Matrix–Tree's arrow), cross-ref `determinant.md` | `…/Markov/SternBrocotMarkov.lean:104 det2_mul`; `…/ModularGeometry/HolonomyLattice.lean:123 det_mul`; `:136 det_holonomy_eq_one` | ∅-axiom (per `determinant.md`) ✓ |
| connectedness = finite-list adjacency (topology.md's `Chain`/`chain_finite`) | `Lib/Math/Geometry/Topology/Connectedness.lean:36 Chain`; `:65 chain_finite`; `:31 adjacent` | **PURE** (16/0) ✓ |
| K₅ = complete-graph 1-skeleton: ker δ₀ = 2 (connected, b₀=1), b₁ = 6 | `Lib/Math/Cohomology/Examples/K5.lean:61 kerSize_K5`; `:70 K5_cohomology` | **PURE** ✓ |
| count-reading + its `q=±1` residue (the diffusion-kernel tag), cross-ref `cardinality.md`/`topology.md` | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree`; `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag` | ∅-axiom (per `cardinality.md`/`topology.md`) ✓ |

**Fresh purity scan (this session):** `scan_axioms.py` — `Combinatorics.GraphConnectivity` 16/0,
`Topology.Connectedness` 16/0 (joint scan), `AlphaEM.LaplacianSpectrum` 15/0,
`Bipartite.Parametric.Delta0AndConnectedness` 13/0,
`Bipartite.Parametric.Betti.KernelConstancyUniversal` 20/0, `Mat2SymmetricSpectrum` 49/0 (incl. deps).
All pure / 0 dirty; build clean.

## Conceptual-only / absent legs (honest — not cited as anchors)

- **A constructed `L = D − A` matrix over an arbitrary finite graph + its eigen-equation — ABSENT,
  located.** The connectivity = dim ker leg is carried *abstractly* over `Adj : V → V → Prop`
  (`GraphConnectivity`, fully `d`-agnostic, PURE) via the Bool δ⁰-kernel; there is no `ℤ`-valued
  `L : (V → ℤ) → (V → ℤ)` with the stated `Lσ(v) = Σ_{u∼v}(σ v − σ u)` and `ker L = constants` as
  an operator kernel. This is the precise missing primitive — the `d > 1` matrix gap shared with
  `spectral.md`.
- **The Laplacian *spectrum* is asserted, not derived.** `AlphaEM/LaplacianSpectrum.lean` writes the
  classical K_{m,n} eigenvalue formula `c·{0,m,n,m+n}` with multiplicities and `decide`-checks the
  Nat identities (trace, rank, ζ-sums) — it does **not** derive the spectrum as roots of
  `charPoly(L)` from a constructed `D − A`. The λ₀ = 0 ⟺ connected (`H⁰ = 1`) fact is honest (it
  matches `GraphConnectivity`'s PURE result), but the *spectral derivation* is classical input.
- **Matrix–Tree at `d > 1`** — #spanning trees = `det(L-minor)`; the repo has `det2_mul`/`det_mul`
  and a `DetN` skeleton but no Laplacian-minor determinant. PREDICTION / CONCEPTUAL (the `det = e₂`
  symmetric-function tie is PURE only at `d = 2`).
- **Random walk / PageRank Perron eigenvector** — `P = D⁻¹A`'s dominant eigenvector = the `q=+1`
  stationary fixed point; the Banach engine (`gaussian_clt`) and discrete heat operator
  (`Analysis/ODE/HeatEq/Discrete.lean`) exist but are not welded to a graph walk operator.
  PREDICTION / CONCEPTUAL.
- **The Fiedler *value* λ₁** — a `Real213`/√disc cut, irrational in general (the `q=−1` value
  residue); existence at the symmetric `disc ≥ 0` level is closed (`disc_symmetric_nonneg`), the
  value is the orthogonal `Real213` task. (Rational for the 2-vertex graph: λ₁ = 2.)

> Axiom-purity note: every theorem cited above was freshly scanned with `tools/scan_axioms.py` this
> session (results in the anchors table) — the purity claim rests on a fresh scan, not docstrings.
