# Decomposition: percolation theory

*A FRESH decomposition of "bond/site percolation, the open subgraph at edge-probability `p`, the
critical probability `p_c`, the phase transition, the infinite cluster, the order parameter
`θ(p) = P_p(0 ↔ ∞)`, Kesten's `p_c = 1/2` for ℤ², the FKG inequality, RSW / crossing probabilities,
criticality" per `../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants + the q=±1 spine).
LEVERAGE phase. This is a **two-neighbour extension**: it adds a *critical-transition* reading on top
of `graph_theory.md` (connectivity = dim ker L, the q=+1 constant kernel,
`GraphConnectivity.closed_const`/`bipAdj_connected`) and reuses `random_walks.md`'s q=±1 spine
(recurrence/transience = converge/escape) — the NEW datum being that `p_c` is the **q=±1 phase-transition
point** of the connectivity reading, with `θ(p)` = the residue size.*

> **THE THESIS (the brief's central question).** Percolation is the calculus's **q=±1
> phase-transition tag on graph connectivity** — `p_c` is the critical point where the connectivity
> reading flips pole. Graph connectivity (`graph_theory.md`) is the dim-ker reading: connected ⟺ the
> Laplacian/δ⁰ kernel is the constants (`GraphConnectivity.closed_const`). Percolation reads
> connectivity *as a function of an edge-probability `p`*: below `p_c` the open subgraph is **q=+1**
> (all clusters finite — the connectivity reading localizes/converges); above `p_c` an infinite
> cluster appears = the **q=−1 escape** (the connected component "escapes" to infinity — the *same*
> reached-by-none escape as transience in `random_walks.md`). `p_c` IS the q=±1 pole-transition point
> (`θ(p_c⁻)=0` vs `θ(p_c⁺)>0`); the order parameter `θ(p)` = the **residue size**. Kesten's
> `p_c = 1/2` (ℤ² self-duality) = the q=±1 **self-dual fixed point** (the duality involution, the
> `multiplier_unimodular` `±1` flip — `p_c` is where the graph equals its dual). FKG = the q=+1
> monotone/positivity on the weight axis. **NO new primitive**: it is `graph_theory`'s connectivity
> with a q=±1 critical-transition tag and `θ` as the residue.

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; `graph_theory.md`'s `⟨ V (count) | symmetric Adj ⟩`
  carrying a weight `p` per edge.** Percolation has no construction of its own. The lattice is
  `graph_theory.md`'s graph `⟨ V (count-reading, `cardinality.md`) | symmetric `Adj` on V×V ⟩` (for
  ℤ² the square lattice, but `C` is lattice-agnostic). Percolation adds only the **weight axis**
  (`probability.md`/`random_walks.md`): each edge (bond) or vertex (site) is independently *open* with
  weight `p`, so the open subgraph `G_p ⊆ G` is the symmetric `Adj` *sub-selected by an
  independent-`p` weight on each edge*. A configuration `ω ∈ {open, closed}^{edges}` is the count-reading's
  carrier `2^E` weighted by `p^{#open}(1−p)^{#closed}` — exactly `probability.md`'s `P = ratio ∘ count`
  with the multiplicative independence character `×↦·` across edges. **Nothing percolation-theoretic is
  primitive — only a graph (count + symmetric pair-reading) and an independent edge weight `p`.**

- **Reading `L_conn(p)` — `graph_theory.md`'s connectivity reading (dim ker L), now a FUNCTION of `p`.**
  The reading is `graph_theory.md`'s connectivity-of-the-open-subgraph, dialed by `p`:
  `L_conn(p) = ` "is the component of the origin in `G_p` finite or infinite?" (equivalently, the dim of
  the δ⁰-kernel restricted to the open subgraph — one constant per *open cluster*). Two facts carry over
  *forced*, not chosen:
  - connectivity on a *fixed* open subgraph is `graph_theory.md`'s dim-ker reading: a cluster = a
    connected component = a δ⁰-closed colouring class (`GraphConnectivity.IsClosed`); on a connected
    component the only edge-constant colourings are the constants (`closed_const`,
    `closed_root_determines` — dim ker = 1 per component). The *number of clusters* = `dim ker` of the
    open subgraph's Laplacian (`#components = dim ker L`, `graph_theory.md`).
  - reading this *as `p` varies* is the new move: `θ(p) = P_p(|cluster(0)| = ∞)` is the probability the
    origin's component escapes to infinity — the connectivity reading composed with the weight reading
    (`probability.md`'s `ratio ∘ count`), read on the kernel's *size* rather than its existence.

  So `L_conn(p)` is `graph_theory.md`'s connectivity reading with the resolution/weight dial set to `p`;
  the percolation phenomenon is what this reading does *as `p` crosses a critical value*.

- **Residue — `q = ±1`, and the WHOLE field is the residue read across the transition.**
  - **q=+1 (subcritical / converge / all clusters finite — `θ(p)=0`).** For `p < p_c` every open
    cluster is finite almost surely: the connectivity reading *localizes* — the component of the origin
    has a fixed point (it closes at a finite radius). The kernel-of-the-open-subgraph stays
    finite-dimensional-per-region; nothing escapes. This is the **contrapositive corner** of
    `cardinality.md`'s escape diagonal, *exactly* `random_walks.md`'s recurrent/converge pole and
    `topology.md`'s finiteness-collapse: the count-reading on the cluster *closes* to a finite value.
    `θ(p)=0` = the residue is empty (`q=+1`).
  - **q=−1 (supercritical / escape / the infinite cluster — `θ(p)>0`).** For `p > p_c` an infinite
    open cluster exists with positive probability: the connectivity reading *escapes to infinity* — the
    component of the origin is reached-by-none-finite-radius, the same
    `OneDiagonal.no_surjection_of_fixedpointfree` escape underlying transience (`random_walks.md`),
    Cantor (`cardinality.md`), Gödel (`godel.md`), and non-measurable sets (`measure.md`). The
    "infinite cluster" is the **q=−1 escape residue** of the connectivity reading; `θ(p)>0` = the
    residue is *occupied* (`q=−1`), and `θ(p)` measures **how large** it is — the order parameter IS the
    residue size.
  - **the transition point `p_c` itself** is where the reading flips pole: `θ(p_c⁻)=0` (q=+1) vs
    `θ(p_c⁺)>0` (q=−1). `p_c` is the q=±1 pole-transition point — the `multiplier_unimodular` `±1`
    boundary read as a function of `p`. The *value* `p_c` (and `θ` away from the trivial regime) is a
    `Real213`-cut residue (irrational in general — the q=−1 value residue, as for `graph_theory.md`'s
    Fiedler value).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   percolation on a lattice  =  ⟨ V (count) | symmetric Adj + independent edge weight p ⟩   (C — NO new construction; graph_theory + an edge weight)
   open subgraph G_p          =  Adj sub-selected by the independent-p weight (probability.md's P = ratio ∘ count, independence = ×↦· across edges)
   a cluster / open component  =  graph_theory.md's connected component = δ⁰-closed colouring class (GraphConnectivity.IsClosed)
   #clusters                  =  dim ker L of the open subgraph (graph_theory.md's #components = dim ker)
   connectivity reading L(p)   =  graph_theory.md's connectivity, dialed by p (the dim-ker reading as a function of p)
   θ(p) = P_p(0 ↔ ∞)          =  the RESIDUE SIZE: connectivity-reading ∘ weight-reading, on the kernel's size  (the order parameter)
   SUBCRITICAL p < p_c         =  q=+1: all clusters finite, the connectivity reading localizes/converges  (θ=0, empty residue; = random_walks recurrent)
   INFINITE CLUSTER p > p_c    =  q=−1 ESCAPE: the component reaches no finite radius  (θ>0, occupied residue; = random_walks transient = Cantor/Gödel escape)
   p_c (critical probability)  =  the q=±1 POLE-TRANSITION point (θ(p_c⁻)=0 vs θ(p_c⁺)>0); the ±1 flip read in p
   the phase transition        =  the connectivity reading flipping pole at p_c  (multiplier_unimodular's ±1 boundary)
   Kesten p_c = 1/2 (ℤ²)       =  the q=±1 SELF-DUAL FIXED POINT: ℤ² self-dual, p_c = where G equals its dual  (the duality involution, ±1)
   FKG inequality             =  q=+1 monotone/positivity on the weight axis (increasing events positively correlated)  [PROSE — no anchor]
   RSW / crossing probability  =  the bounded q=+1/q=−1 crossing reading at criticality  [PROSE — no anchor]
   the VALUE p_c, θ(p)         =  Real213-cut residue (irrational in general — q=−1 value residue, reached-by-none)
```

So **the open subgraph, clusters, the order parameter, the phase transition, the infinite cluster, and
criticality are one reading at work** — `graph_theory.md`'s connectivity reading on `C`, weighted by `p`
and read across the q=±1 transition. Percolation is `graph_theory.md`'s connectivity + `random_walks.md`'s
q=±1 spine + `probability.md`'s weight axis, with the NEW *critical-transition* reading.

## THE REVELATION — collapse + forcing + spine (HONESTLY THIN on Lean grounding)

This is **not** a re-skin of `graph_theory.md` (which built connectivity = dim ker *statically*, at a
fixed graph) or `random_walks.md` (which read recurrence/transience as q=±1 on a *fixed* walk). The new
datum is the **critical-transition reading**: connectivity becomes a *function of `p`*, and `p_c` is the
point where that function flips q=±1 pole.

1. **Collapse — the infinite cluster IS `random_walks.md`'s transient escape, one q=−1 residue.** The
   supercritical infinite open cluster and the transient walk's escape-to-infinity are the **same q=−1
   escape residue**: a connectivity reading whose component is reached by no finite radius, the
   `OneDiagonal.no_surjection_of_fixedpointfree` engine `ResidueTag.escape_residue_outside` packages
   (the same diagonal as Cantor/Gödel/measure). Subcritical "all clusters finite" is the q=+1
   converge/recurrent pole (`ResidueTag.converge_residue_fixed`). So "infinite cluster appears" and
   "the walk turns transient" are one q=±1 flip, read on the same connectivity object — the collapse
   `graph_theory.md` and `random_walks.md` make available, now indexed by `p`.

2. **Forcing — the order parameter `θ` is forced to BE the residue size, and the transition is forced
   to be sharp at one pole-flip.** Given the collapse, the rest is *forced*, not added:
   - `θ(p) = P_p(0 ↔ ∞)` is *forced* to be the residue measure: it is exactly the weight-axis
     (`probability.md`) reading of "is the origin's component the q=−1 escape residue?". `θ = 0 ⟺ q=+1`
     (empty residue, all-finite), `θ > 0 ⟺ q=−1` (occupied residue) — `θ` is not an arbitrary
     observable, it is the residue's size on the weight axis. (This is the *prediction*; the
     monotonicity `θ` non-decreasing in `p` is the q=+1 weight-positivity, which would need FKG —
     **prose, no anchor**.)
   - the existence of a *single* `p_c` (a sharp threshold, not a band) is *forced* by the q=±1 structure
     having exactly two poles: the connectivity reading is q=+1 or q=−1, never a third value
     (`multiplier_unimodular`: `|q| = 1`, the only unimodular integers are `±1`), so the transition is a
     single pole-flip point. (The *sharpness* of the threshold — Menshikov/Aizenman–Barsky — is the
     deep classical content; the calculus *predicts the dichotomy* but does not derive sharpness —
     prose.)

3. **Spine — `p_c` is the q=±1 transition point; Kesten `p_c = 1/2` is the self-dual fixed point.** This
   is the sharpest tie to `SYNTHESIS.md`'s q=±1 spine and the genuinely new datum over both neighbours.
   Where `random_walks.md` reads recurrence/transience as q=±1 *at a fixed graph*, percolation reads the
   q=±1 pole as a *function of `p`*, and `p_c` is the **critical point of that function** — the boundary
   between the converge and escape regimes. Kesten's `p_c = 1/2` for bond percolation on ℤ² is the
   **self-dual fixed point** of this transition: ℤ² is self-dual (its dual lattice is ℤ² again), and the
   self-duality involution maps `p ↦ 1 − p` (open edges ↔ closed dual edges); the fixed point of this
   involution is `p = 1/2`, which is *forced* to be `p_c` precisely because at the self-dual point the
   open subgraph and its dual are stochastically identical — the q=±1 flip can only happen where the
   reading equals its own dual. This is the `multiplier_unimodular` involution (the `±1` flip,
   `q ↦ −q`) read on the *weight* axis: `p_c = 1/2` is the weight-axis analogue of "the involution's
   fixed point", the same self-dual q=±1 boundary structure as Fourier self-duality (`SYNTHESIS.md`) and
   the modular reflection `s ↔ k−s`. **HONEST: this is an analogy at the structural level — the repo has
   `multiplier_unimodular` (the `±1` involution, PURE) but NO percolation duality theorem, no
   `p ↦ 1−p` map, no `p_c = 1/2` derivation.**

**Re-skin guard — cleared, but at the PREDICTION/analogy bar, not the collapse bar.** The note does not
re-describe `graph_theory.md` or `random_walks.md`: its load-bearing new fact is the *critical-transition
reading* — connectivity as a function of `p` whose q=±1 pole flips at `p_c`, with `θ` forced to be the
residue size and `p_c = 1/2` identified with the self-dual involution fixed point. But — stated plainly —
this new datum is **mostly analogy with thin Lean grounding**: the *static* connectivity = dim-ker leg is
PURE and built (`GraphConnectivity`, `bipAdj_connected`), and the q=±1 residue tag is PURE
(`ResidueTag`), but the *transition itself* — the `p`-dependence, `θ(p)`, `p_c`, duality, FKG, RSW — is
entirely unbuilt. This is a genuinely **weaker** decomposition than the two neighbours, whose central
theorems were PURE; here the central new claim (`p_c` = the q=±1 pole-transition point) has no Lean
witness.

## VALIDATE — verdict: **PREDICTION (thin), no break, no new primitive**

**PREDICTION.** The calculus *predicts* percolation's shape from its parts: connectivity = dim-ker
(`graph_theory.md`), the infinite cluster = the q=−1 escape (`random_walks.md`'s transience, the same
`OneDiagonal` diagonal), `θ(p)` = the residue size on the weight axis, `p_c` = the single q=±1
pole-transition point (forced by `multiplier_unimodular`'s two-pole structure), and `p_c = 1/2` for ℤ² =
the self-dual involution fixed point. The *static connectivity engine and the q=±1 tag are built and
PURE*; the *`p`-dependent transition objects* —
`percolation`/`criticalProbability`/`infiniteCluster`/`θ`/`FKG`/`Kesten`/`crossing` — are **ABSENT**
(grep-confirmed below).

**No new primitive.** Percolation adds nothing to model v7.1 — it *fuses three existing entries and adds
a `p`-indexing*:
- the **connectivity = dim-ker reading** (`graph_theory.md`: `closed_const`, `bipAdj_connected`, the δ⁰
  kernel) — supplies clusters, components, the connectivity object;
- the **q=±1 residue tag** (`ResidueTag`, `random_walks.md`'s recurrence/transience) — supplies
  subcritical=converge / supercritical=escape / infinite-cluster = the q=−1 residue;
- the **weight axis** (`probability.md`: `P = ratio ∘ count`, independence = `×↦·`) — supplies the
  independent edge weight `p` and `θ(p)`;
- the only *new* element is reading the q=±1 pole **as a function of `p`** (the critical-transition
  reading) — this is the resolution/weight dial of an existing reading, not a new primitive.

**No BREAK.** The two invariants (character arrow, q=±1 residue) and the four axes absorb the field
cleanly; the honest residuals are (i) the value-cut (`p_c`, `θ(p)` as `Real213` numbers) and (ii) the
*named* `p`-dependent objects, all unbuilt.

**HONEST GROUNDING ASSESSMENT.** This is the **thinnest** of the connectivity-cluster decompositions.
`graph_theory.md` had its central leg (connectivity = dim ker) PURE; `random_walks.md` had the
constructed Laplacian, the constant kernel, and the q=±1 tag PURE. Percolation's central new claim — that
`p_c` is the q=±1 pole-transition point of the connectivity reading — has **no direct Lean witness**: it
is a structural prediction resting on (a) the PURE static connectivity machinery, (b) the PURE q=±1 tag,
and (c) an *analogy* (the self-dual involution ↔ `multiplier_unimodular`) that is suggestive but not a
percolation theorem. The probabilistic core (independent product measure on `2^E`, the 0-1 law for
existence of an infinite cluster, FKG, RSW, sharpness, Kesten's self-duality argument) is **entirely
unbuilt** — percolation is heavily measure-/probability-theoretic, sitting on the `Real213`/value-cut and
the (partly Choice-flavoured, `measure.md`) infinite-product-measure residue. The decomposition is
**real but predominantly analogy**; the verdict is PREDICTION, and it is weaker than its neighbours.

## Verified Lean anchors (file:line:theorem — all grep-confirmed; purity by `tools/scan_axioms.py`, run this session from repo root)

These anchor the *reused* legs (static connectivity, the q=±1 tag, the weight axis). They do **not**
anchor the percolation-specific transition, which is unbuilt.

| Leg (reused, not percolation-specific) | Theorem / def (file:line : name) | Purity (fresh scan) |
|---|---|---|
| ★★★ connectivity ⟹ δ⁰-closed colouring globally constant (cluster = component; dim ker = 1 per component) | `Lib/Math/Combinatorics/GraphConnectivity.lean:61 closed_const`; `:50 closed_eq_root` | **PURE** (8/0) ✓ |
| ★★★ kernel = the two constants ⇒ b₀ = 1 (0 simple); **dim ker = 1** (one Bool of freedom per component) | `…/GraphConnectivity.lean:69 closed_false_or_true`; `:79 closed_root_determines` | **PURE** (8/0) ✓ |
| cluster reachability = `graph_theory.md`'s finite-adjacency reading | `…/GraphConnectivity.lean:33 Reach`; `:38 IsConnectedFrom`; `:42 IsClosed`; `:88 reach_one`; `:93 reach_two` | **PURE** ✓ |
| ★★★ an **actual lattice/bipartite adjacency** is connected (Adj wired into the connectivity framework) | `Lib/Math/Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean:254 bipAdj_connected`; `:248 bipAdj`; `:293 isKer_const_via_framework`; `:268 isConstOnEdges_isClosed` | **PURE** (20/0) ✓ |
| ★★★★ **the q=±1 residue tag** (subcritical=converge / supercritical=escape); `±1` two-pole flip = the transition's only-two-values forcing | `Lib/Math/Foundations/ResidueTag.lean:228 residue_tag_two_poles`; `:86 multiplier_unimodular`; `:81 multiplier` | **PURE** (55/0) ✓ |
| ★★★★ **infinite cluster = the q=−1 ESCAPE residue** (= transience, Cantor/Gödel/measure escape) | `…/ResidueTag.lean:133 escape_residue_outside`; `:144 cantor_is_escape` ← `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree` | **PURE** (55/0 / 11/0) ✓ |
| ★★★ **subcritical = the q=+1 CONVERGE residue** (all clusters finite, the localizing fixed point) | `…/ResidueTag.lean:160 converge_residue_fixed`; `:180 golden_is_converge` | **PURE** (55/0) ✓ |
| ★★ the residue itself (the escape's foundational engine; the infinite cluster as reached-by-none) | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`; `:71 self_covering_closure` | **PURE** (7/0) ✓ |
| ★★ the weight axis: independence = `×↦·` (the independent-edge-`p` product), `θ` = weight-reading of the residue | `Lib/Math/Probability/Limit/ConvolveProfile.lean:190 mass_conv` | **PURE** (20/0) ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py E213.… ` from repo root):**
`GraphConnectivity` **8/0**, `KernelConstancyUniversal` **20/0**, `ResidueTag` **55/0**,
`OneDiagonal` **11/0**, `FlatOntologyClosure` **7/0**, `ConvolveProfile` **20/0**. All pure / 0 dirty.

## Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

Grep over `lean/E213` (case-insensitive) for
`percolation`/`criticalProbability`/`infiniteCluster`/`p_c`/`crossing`/`Kesten`/`FKG`/`cluster`/
`phase.transition`/`self.?dual`/`positive.assoc`/`harris`/`increasing event` returns **no real
percolation math-object hits**. The matches are all substring/false-positive noise: `P_c` is the
*curvature operator* `P_c u = c·u + Lu` in `DiscreteCurvature/DiscreteLichnerowicz.lean` (unrelated);
"Griffiths–**Harris**" in `Hodge/HodgeRiemannJ.lean` is a textbook citation, not the Harris/FKG
inequality; `cluster`/`critical`/`phase` elsewhere are unrelated (deployment graphs, phase angles, etc.).
So:

- **No `percolation` / `Percolation` object** — no open-subgraph-at-`p` construction. The open subgraph
  is conceptually `graph_theory.md`'s `Adj` weighted by an independent `p`; no such weighted-selection
  object is built. **Predicted-not-built.**
- **No `criticalProbability` / `p_c` object, no `phaseTransition` theorem** — `p_c` is the predicted
  q=±1 pole-transition point (forced as a *single* point by `multiplier_unimodular`'s two-pole
  structure), but no `p`-indexed connectivity function, no threshold theorem, no `θ(p_c⁻)=0 vs θ(p_c⁺)>0`
  statement exists. **Predicted-not-built.**
- **No `infiniteCluster` / `θ(p)` / `orderParameter` object** — the infinite cluster is the predicted
  q=−1 escape residue (`escape_residue_outside`/`object1_not_surjective`), and `θ` the residue size on
  the weight axis (`mass_conv`'s `×↦·` independence), but no `θ(p) = P_p(0 ↔ ∞)` object or
  infinite-cluster-existence theorem is built. **Predicted-not-built.**
- **No FKG / Harris / positive-association theorem** — the predicted q=+1 monotone/positivity on the
  weight axis (increasing events positively correlated, `θ` monotone in `p`). **ENTIRELY PROSE — no
  anchor, not even an analogue.** The monotone hits in `Probability/Limit/{DyadicCompletion,CLTGeneric}`
  are the *running-max modulus* and CLT monotonicity, unrelated to positive association. The cleanest
  honest statement: FKG has **no grounding whatsoever** in the repo; the q=+1-positivity reading is a
  conjecture. **Predicted-not-built (prose only).**
- **No Kesten `p_c = 1/2` / self-duality / `p ↦ 1−p` object** — the predicted self-dual q=±1 fixed point
  (ℤ² self-dual, the involution's fixed point). The repo has `multiplier_unimodular` (the `±1`
  involution, PURE) and assorted `self_dual`/`involution` structure in *other* fields (Frobenius
  `fp2dFrob_involution`, `FenchelMoreau`, etc.), but **no percolation duality, no `p ↦ 1−p` map, no
  lattice-self-duality, no `p_c = 1/2` derivation.** The `multiplier_unimodular ↔ self-dual fixed point`
  tie is an **analogy at the structural level only**. **Predicted-not-built (analogy only).**
- **No RSW / crossing-probability object** — the predicted bounded crossing reading at criticality.
  **Predicted-not-built (prose only).**
- **The VALUES `p_c`, `θ(p)`** — `Real213`-cut residues (irrational/transcendental in general — the
  q=−1 value residue, as for `graph_theory.md`'s Fiedler value). `p_c = 1/2` for ℤ² bond is the rare
  rational case (the self-dual point), but it is not derived. **Value-cut residue, honest.**
- **The independent product measure on `2^E`** — percolation's measure-theoretic core (an infinite
  product measure, 0-1 law for infinite-cluster existence) sits on `measure.md`'s weight axis and, for
  the infinite lattice, partly on its Choice/`q=−1` residual. **Unbuilt; the deeper analytic absence.**

### A (weak) buildable witness — honestly marginal

Unlike `random_walks.md` (which had a clean maximum-principle promotion target from present PURE pieces),
percolation has **no clean small buildable witness for the central claim**: the transition is inherently
about an infinite lattice and a product measure neither of which is built. The *only* honestly-buildable
fragment is a **finite, deterministic toy**: on a *fixed* finite open subgraph one can already read
"number of clusters = `dim ker`" via `GraphConnectivity.closed_root_determines` + `bipAdj_connected`
(both PURE) — i.e. the q=+1 *static* connectivity at one configuration `ω`. A `decide`-checked toy
"as edges are added, `#components` (= dim ker) is non-increasing, and at full density it reaches 1
(connected)" on a small fixed graph would be the monotone-connectivity skeleton of the transition — but
this is the *deterministic* monotonicity of `dim ker` under edge-addition, **not** the probabilistic
`θ(p)` transition, and would NOT ground FKG, `p_c`, the infinite cluster, or Kesten. I flag it as the
*only* present-pieces fragment, and explicitly **do not** claim it grounds the thesis. The central datum
(`p_c` = the q=±1 pole-transition point) remains a prediction with no Lean witness.

> Axiom-purity note: every theorem cited in the anchors table was freshly scanned with
> `tools/scan_axioms.py` this session (tallies above) — the purity claim rests on a fresh scan, not
> docstrings. The percolation-specific objects (`p_c`, `θ`, infinite cluster, FKG, Kesten, RSW) are
> grep-confirmed ABSENT and are not cited as anchors; the central new claim is a PREDICTION resting on
> reused static-connectivity + q=±1-tag machinery plus an explicitly-flagged self-duality analogy.
