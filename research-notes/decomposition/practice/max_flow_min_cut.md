# Decomposition: network flows / max-flow–min-cut (a flow network, conservation at internal nodes, the max-flow–min-cut theorem, Ford–Fulkerson augmenting paths, the integrality theorem, LP-duality of flow/cut, Menger's theorem)

*213-decomposition of network flows, per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕
Residue(L,C)`). The bar is **leverage / consolidation, not re-skin**. Hypothesis under test:
max-flow–min-cut is the calculus's **LP duality (`kantorovich`) on a graph, with the flow = a
conserved Noether current and the cut = the `q=±1` boundary `∂`**. It fuses three corpus invariants
on the network — `optimal_transport.md`'s weight-axis LP duality (`kantorovich_weak_duality` /
`ollivier_plan_optimal`), `noether.md`'s discrete conserved current (`NoetherCurrent.continuity_eq`,
`∂·j = 0` except at source/sink), and `homology.md`/`graph_theory.md`'s boundary/coboundary `∂` (the
`q=±1` cut, the coboundary of the source-set indicator). It consolidates `graph_theory.md` (the graph
has no construction of its own — `⟨V count | symmetric Adj⟩`), `convex_duality.md`/`optimal_transport.md`
(the `f**=clo` LP duality), and `ResidueTag.lean` (the `q=±1` tag).*

This entry is **honest about absence at the named-object layer**: there is **no** `maxFlow`, `minCut`,
`flow`, `network`, `FlowNetwork`, `Menger`, `FordFulkerson`, `augmentingPath`, `residualGraph`, or
`capacity`-as-flow object in `lean/E213/` — grep-confirmed (the only `capacity` hits are
information-channel capacity and nuclear-shell capacity; the only `Menger` hits are *Cayley–Menger*
geometry; the only `flow` hits are `RicciFlow`/`GradientFlow`/`MonovariantFlow`, unrelated). What **is**
built and PURE are the three structural legs the thesis claims the flow problem *is made of*: the
Kantorovich LP weak/strong duality, the discrete Noether current `∂·j`, and the boundary/coboundary `∂`
— plus the closest combinatorial cousin, **Hall's matching by augmenting recursion** (the
Ford–Fulkerson iteration shape, with `HallCond` = the obstruction the construction never hits).

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; `graph_theory.md`'s `⟨V count | symmetric Adj⟩` made
  *directed* and *weighted*.** A flow network is not a primitive. Per `graph_theory.md` a graph is
  `⟨ V (the count-reading's carrier, `cardinality.md`) ∣ a pair-reading `Adj` on V×V ⟩`; a network adds
  two read-off sub-structures `C` already carries (`README` model v3/v7):
  - a **direction / swap-bit** on each edge (`integers.md`/`homology.md`'s `q=±1` orientation: an edge
    `e = (u→v)` carries a sign — flow *out of* `u` is `+`, *into* is `−`), and
  - a **weight** on each edge (`probability.md`/`measure.md`/`optimal_transport.md`'s weight axis: the
    *capacity* `c(e)` is the value-slot, exactly the cost/mass slot the transport plan reads).
  A **flow** `f : E → ℤ` is then a *directed, weighted readout* obeying `0 ≤ f(e) ≤ c(e)`; two
  distinguished vertices `s` (source), `t` (sink) pin the boundary. So a network is
  `⟨ V (count) ∣ a directed (q=±1) capacity-weighted pair-reading, with two marked boundary vertices ⟩`
  — three existing read-off axes (count + direction + weight) on the *same* `Adj`, no new primitive.

- **Reading `L` — two readings of the one weighted/directed construction, bound by LP duality.**
  1. The **primal (flow) reading** is the weight-axis value-flow on edges *plus a conservation
     constraint*: at every internal vertex `v ≠ s,t`, in = out — `Σ_{e into v} f(e) = Σ_{e out of v}
     f(e)`. This is **literally `noether.md`'s discrete continuity equation `∂·j = 0`**: the flow is a
     *divergence-free conserved current*, conserved everywhere except at the source (a `+` divergence,
     the charge injected) and the sink (a `−` divergence). The **flow value** `|f| = ` net out-flow at
     `s` = the value-weighted count of the current crossing the source boundary — the weight-axis
     functional, exactly `transportCost`'s shape `Σ d·π` read on the flow.
  2. The **dual (cut) reading** is the **`∂` boundary** of a *source/sink-separating set*: a cut is a
     bipartition `(S, T)` with `s ∈ S`, `t ∈ T`; its **capacity** is `Σ_{e: S→T} c(e)`, the weight of
     the edges crossing the boundary. The cut **IS** `homology.md`/`graph_theory.md`'s coboundary: the
     cut-set `{e : S→T}` is `δ(𝟙_S)` — the coboundary `δ` (the `∂` run on the `0`-cochain that is the
     indicator of the source-set), the `q=±1`-oriented boundary operator (`Delta/Core.delta`,
     `dsq_zero_universal_delta4`). The cut capacity is the weight-axis functional read on `δ(𝟙_S)`.

- **Residue — the duality gap `min-cut − max-flow ≥ 0`, tagged `q = ±1`.** Weak duality forces the gap:
  *every* flow value `≤` *every* cut capacity (the conserved current must squeeze through the boundary,
  bounded by its capacity — the adjoint inequality `dualValue ≤ transportCost`,
  `kantorovich_weak_duality`). **`q = +1`** = the gap *vanishes*: a flow and a cut **meet** (max-flow =
  min-cut), the LP optimum is tight, the residual graph disconnects `s` from `t` — the converging /
  settle pole, the same residue-collapse as `ollivier_plan_optimal`'s zero gap and `galois.md`'s
  closure-exact. **`q = −1`** = the residue *as the augmenting move*: while a gap survives there is still
  an augmenting path in the residual graph (the flow can escape upward); Ford–Fulkerson iterates the
  `q=−1` augmentation until none remains, reaching the `q=+1` fixed point. The **integrality theorem**
  (integer capacities ⟹ integer max-flow) is the *count reading* of this residue (each augmentation
  bumps the flow by a positive integer bottleneck, `cardinality.md`'s count-Lens, the same
  integer-bump as Hall's augmenting recursion). **Menger** (max # edge-disjoint `s`–`t` paths = min cut)
  is the **count version** of the same theorem — capacities all `= 1`, the value-weighted count
  degenerating to a plain count of disjoint paths.

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   a flow network          =  ⟨ V (count) ∣ directed (q=±1) capacity-weighted Adj, marked s,t ⟩   (C — NO new construction)
   the capacity c(e)        =  the weight axis (optimal_transport's cost/mass slot)               (transportCost's d-slot)
   a flow f(e), 0≤f≤c       =  a directed weight-axis readout on edges (the conserved current)
   conservation in=out at v≠s,t = noether's discrete continuity eq ∂·j = 0                        (NoetherCurrent.continuity_eq)
   flow is divergence-free except at s,t = density conserved off the boundary                     (density_conserved_of_det_one)
   the flow value |f|       =  net out-flow at s = the weight-axis functional across the boundary  (transportCost shape)
   a cut (S,T), s∈S, t∈T    =  a source/sink-separating set (the boundary's two sides)
   the cut-set {e: S→T}     =  the COBOUNDARY δ(𝟙_S) = homology's ∂ on the source-indicator        (Delta/Core.delta, dsq_zero)
   cut capacity Σ c(S→T)    =  the weight-axis functional read on δ(𝟙_S) (the q=±1 boundary)
   weak duality |f| ≤ cap(S,T) =  the adjoint inequality dualValue ≤ transportCost                (kantorovich_weak_duality)
   max-flow = min-cut       =  the q=+1 tight LP optimum, zero gap (they meet)                     (ollivier_plan_optimal)
   the duality gap (nonzero) =  Residue(L,C), q=−1 (an augmenting path still exists)               (ResidueTag escape)
   Ford–Fulkerson augment   =  iterate the q=−1 augmentation to the q=+1 fixed point (no aug path)  (Hall augmenting recursion shape)
   residual graph disconnects = the q=+1 settle: min cut reached, no s–t path                      (GraphConnectivity / closed_const)
   integrality theorem      =  the count reading of the residue (integer bottleneck bumps)         (cardinality count-Lens)
   Menger (edge-disjoint paths) = the count version (all capacities = 1)                           (Hall matching count)
```

So flow, cut, conservation, duality, augmentation, integrality, and Menger are **one `(C,L)`** — the
weight-axis LP on `graph_theory.md`'s graph, with the flow = `noether.md`'s conserved current and the
cut = `homology.md`'s boundary `∂`. The map lands at the **same place `optimal_transport.md` lands**:
`kantorovich_weak_duality` is the weak-duality leg, `ollivier_plan_optimal` the zero-gap strong-duality
leg. The **NEW datum** (passing the re-skin guard against `optimal_transport.md`): OT reads its LP on a
*coupling of two measures* with marginals; max-flow–min-cut reads the **same LP on a *graph***, where the
primal constraint is `noether.md`'s **`∂·j = 0` conservation** (not OT's marginal constraint) and the
dual object is `homology.md`'s **coboundary `δ(𝟙_S)`** (not OT's Lipschitz potential). The duality, the
conservation, and the boundary all fuse on the network — three corpus invariants meeting on one object,
where OT used only the first.

## LEVERAGE — does max-flow–min-cut fall out as LP-duality + Noether-current + boundary-∂?

**Verdict: EXTEND by consolidation — the three structural legs are already ∅-axiom; one PARTIAL: the
named flow/cut/Menger objects are ABSENT (predicted-not-built, grep-confirmed).** Five legs, graded
honestly.

**(A) The cut = the boundary `∂` / coboundary `δ(𝟙_S)` — GROUNDED ∅-axiom.** The coboundary operator
`δ` is built (`Cohomology/Delta/Core.lean:54 delta`) with `δ²=0` *forced by the `q=±1` orientation bit*
(`Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4`, PURE — opposite-order face removals
carry opposite signs that cancel pairwise, exactly `homology.md`'s mechanism). A cut is `δ` applied to
the source-set indicator `𝟙_S` (a `0`-cochain): the cut-set is the support of `δ(𝟙_S)`, the
`q=±1`-oriented edges crossing the boundary. The δ⁰-machinery that decides *which* `0`-cochains are
boundary-flat is `graph_theory.md`'s `GraphConnectivity` (`IsClosed σ := ∀ u v, Adj u v → σ u = σ v` =
`δσ = 0`); a cut is exactly a **non-flat** `0`-cochain, the complement of `closed_const`'s connected
constant. This is the boundary leg, PURE.

**(B) The flow = a conserved Noether current `∂·j = 0` except at source/sink — GROUNDED ∅-axiom.**
`noether.md`'s `NoetherCurrent` builds an actual `density`, `current`, and `dtDensity`, and proves the
**discrete continuity equation** `dtDensity g w = current g w` (`continuity_eq`, the 213-native
`∂_t ρ + ∂_x j = 0`), with `density_conserved_of_det_one` = *conserved (divergence-free) wherever the
generator is Aut-invariant* and `noether_local`: `(∀ w, current g w = 0) ↔ det g = 1` — the iff "no
divergence ⟺ symmetry". A flow is precisely this current read on the network: divergence-free at every
internal vertex (the Aut-invariant interior, `current = 0`), with the *source/sink* the two vertices
where the generator is *not* unit (the `±` injected divergence — `noether_global`'s telescoped charge
crossing the boundary). The conservation constraint of the flow problem **is** `continuity_eq`; the flow
value is the boundary charge `noether_global` reads. NoetherCurrent scans **14/0 PURE**.

**(C) Max-flow ≤ min-cut (weak duality) and max-flow = min-cut (strong, zero gap) = the Kantorovich LP
duality — GROUNDED ∅-axiom.** `optimal_transport.md`'s LP legs are *the same* duality. `kantorovich_weak_duality`
(`OllivierRicci.lean:52`, PURE) proves `dualValue ≤ transportCost` (the adjoint inequality, worked via
the marginals + Fubini sum-swap + termwise bound) — this **is** "every flow value ≤ every cut capacity":
the conserved current bounded by the boundary it must cross. `ollivier_plan_optimal` (`:106`, PURE):
when a plan and a potential **meet** (gap = 0), the plan is cost-optimal among all sharing its marginals
— **this is "a flow and a cut meet ⟹ max-flow = min-cut"**, the `q=+1` tight LP optimum, the same
residue-collapse-to-closure (`closed_iff_fixed`) as `galois.md`/`convex_duality.md`. `ollivier_bracket`
(`:91`, PURE) is the gap as a squeeze bracket — the duality gap = the residue lives in it. OllivierRicci
scans **60/0 PURE**. The flow LP is the OT LP *on a graph*; weak+strong duality are the corpus's own
committed ∅-axiom theorems.

**(D) Ford–Fulkerson augmenting paths = iteration to the `q=+1` fixed point — GROUNDED by the
augmenting-recursion SHAPE (`HallMarriage`), the flow-specific iteration ABSENT.** Hall's matching is
built **by an augmenting recursion, never asserted by LP-duality** (the file's own docstring), with
`HallCond` = "the obstruction the construction never hits" — `computeNeighbor`/`scanAvoid` scan for an
augmenting choice; if found, augment; the matching value is *computed*, not an abstract `∃`
(`hall_matching_two`, the first non-vacuous-injectivity case, builds `M 0 ≠ M 1` by exactly the
"find a neighbor of `1` distinct from `r0`, else Hall forces one for `0`" augmenting step). This is the
**literal Ford–Fulkerson iteration shape** (König's theorem ties bipartite matching to min vertex-cover
= max-flow on the unit-capacity bipartite network); `HallMarriage` scans **36/0 PURE**. The `q=±1`
reading: each augmentation is a `q=−1` escape move (the residual still admits a path); termination = the
`q=+1` fixed point (`ResidueTag.residue_tag_two_poles`, 55/0, the converge pole; the residual graph
disconnects = `GraphConnectivity.closed_const`'s connected/disconnected boundary). *Conceptual leg:* a
flow-specific `augment`/`residualGraph`/`fordFulkerson` over a capacitated network is **absent** — the
augmenting-recursion *engine* is certified (Hall), only the flow instance is unwritten.

**(E) Integrality theorem + Menger = the count reading — PREDICTED, the count-Lens grounded, the flow
object conceptual.** Integrality (integer capacities ⟹ integer max-flow) is `cardinality.md`'s
count-reading on the residue: each augmentation bumps the flow by a positive *integer* bottleneck (the
same integer-bump `HallMarriage`'s `countB`/`cardS` reads — `countB_pos_of_exists`, a satisfying index
makes the count positive). Menger (max # edge-disjoint `s`–`t` paths = min cut) is the **count version**:
all capacities `= 1`, the value-weighted flow degenerating to a plain count of disjoint paths — the same
count-Lens, the matching/König count `HallMarriage` already hosts (`hall_matching_two`'s injective
`M`). *Conceptual leg:* there is no `Menger` object (grep: only Cayley–Menger geometry); the count
*structure* is present (`countB`, the matching), the named theorem is absent.

**Net.** Not a re-skin of `optimal_transport.md`: the NEW structural claim is that max-flow–min-cut is the
**same Kantorovich LP duality read on `graph_theory.md`'s graph**, where the primal constraint is
`noether.md`'s conserved current `∂·j = 0` (not OT's marginals) and the dual object is `homology.md`'s
coboundary `δ(𝟙_S)` (not OT's Lipschitz potential) — three invariants fusing on the network. Three
load-bearing legs (boundary `∂`, conserved current, LP duality) are committed ∅-axiom; the
augmenting-recursion engine is certified by Hall. The honest residual is the **named flow/cut/Menger
object layer**, predicted-absent and grep-confirmed.

## Revelation

**Max-flow–min-cut is ONE `(C,L)` — the weight-axis LP duality on a graph — and it is the FIRST entry
where THREE corpus invariants fuse on one object: the LP duality (`optimal_transport.md`), the conserved
Noether current (`noether.md`, `∂·j=0`), and the boundary `∂` (`homology.md`/`graph_theory.md`).** This
is **collapse + forcing + residue-surfaced**, three at once:

1. **Collapse — max-flow–min-cut IS the Kantorovich LP duality, the OT LP read on a graph.** "Every flow
   ≤ every cut" is not a flow-specific theorem — it is `kantorovich_weak_duality`'s adjoint inequality
   `dualValue ≤ transportCost` with the marginal constraint replaced by `∂·j=0` and the Lipschitz
   potential replaced by `δ(𝟙_S)`. "Max-flow = min-cut" is `ollivier_plan_optimal`'s zero-gap optimum.
   `optimal_transport.md` named the LP-duality on a *coupling*; max-flow–min-cut is the **same `f**=clo`
   tight-optimum on a *network*** — the LP-duality family now spans the graph.

2. **Forcing — the flow is FORCED to be a conserved current, the cut FORCED to be a boundary.** The
   primal constraint "in = out at internal vertices" is not an arbitrary rule: it is *forced* to be
   `noether.md`'s `continuity_eq` (`∂·j=0`), because a flow is a directed weight-axis readout and a
   divergence-free directed readout *is* a conserved current (`noether_local`: no divergence ⟺
   symmetry-invariant interior). Dually the cut is *forced* to be `δ(𝟙_S)`: a source/sink-separating set
   is exactly a non-flat `0`-cochain, and its crossing-edges are `δ` of its indicator (`dsq_zero` forcing
   the `q=±1` orientation). Conservation and boundary are *forced*, not chosen.

3. **Residue surfaced — the duality gap is the `q=±1` augmenting residue, Ford–Fulkerson the iteration to
   the `q=+1` fixed point.** The gap `min-cut − max-flow` stops being "a quantity to drive to zero" and
   becomes the **residue at its two poles**: `q=−1` = an augmenting path still exists in the residual
   graph (the flow can escape upward); `q=+1` = the residual disconnects `s` from `t`, the gap collapses,
   max-flow = min-cut (`ollivier_plan_optimal`'s closure-exact; `GraphConnectivity.closed_const`'s
   connected/disconnected line; `ResidueTag.residue_tag_two_poles`). Ford–Fulkerson = iterate `q=−1` →
   `q=+1`, the **same augmenting-recursion shape as Hall's matching** (`hall_matching_two`). Integrality
   = the count reading of each integer bump; Menger = the unit-capacity count version.

**THE FUSION:** max-flow–min-cut is the meeting of **three** corpus invariants on one network — the
**LP duality** (`optimal_transport.md`/`convex_duality.md`, `kantorovich_weak_duality`), the **conserved
current** (`noether.md`, `continuity_eq`/`∂·j=0`), and the **boundary `∂`** (`homology.md`/`graph_theory.md`,
`delta`/`dsq_zero`/`closed_const`) — bound by the **`q=±1` residue** (the gap, the augmenting move). The
spine row for SYNTHESIS §3: **max-flow = min-cut (zero gap, residual disconnects, `q=+1`)** sits with
optimal transport's tight duality and graph connectivity's `λ₀=0` constant-kernel in the `q=+1` converge
column; **an augmenting path still exists (`q=−1`)** sits in the escape column.

| pillar | 213 reading | prior entry / object | Lean status |
|---|---|---|---|
| flow network | `⟨V count ∣ directed (q=±1) capacity-weighted Adj, marked s,t⟩` | `graph_theory.md` (no own C) | C grounded; named `network` **absent** |
| capacity `c(e)` | the weight axis (cost/mass slot) | `optimal_transport.md` weight | **built** (`transportCost` d-slot) |
| flow `f`, conservation in=out | the conserved Noether current `∂·j=0` (off s,t) | `noether.md` | **built** (`continuity_eq`, `density_conserved_of_det_one`) |
| flow value `|f|` | the boundary charge / weight-axis functional | `noether.md` `noether_global` | **built** (telescoped charge) |
| cut `(S,T)`, cut-set | the coboundary `δ(𝟙_S)` = the boundary `∂` | `homology.md`/`graph_theory.md` | **built** (`delta`, `dsq_zero`, `closed_const`) |
| cut capacity | the weight-axis functional on `δ(𝟙_S)` | `optimal_transport.md` weight | **built** (cost-on-boundary shape) |
| weak duality `\|f\| ≤ cap` | the adjoint inequality `dualValue ≤ transportCost` | `optimal_transport.md` | **built** (`kantorovich_weak_duality`) |
| max-flow = min-cut (zero gap) | closure exact = residue collapse, `q=+1` | `optimal_transport.md`/`galois.md` | **built** (`ollivier_plan_optimal`, `ollivier_bracket`) |
| Ford–Fulkerson augment | iterate `q=−1` → `q=+1` fixed point (augmenting recursion) | `HallMarriage` augmenting recursion | **shape built** (Hall); flow `augment` **absent** |
| integrality | the count reading (integer bottleneck bumps) | `cardinality.md` count-Lens | count **built** (`countB`); flow object conceptual |
| Menger (edge-disjoint = min cut) | the count version (unit capacities) | matching/König count | count **built** (matching); `Menger` **absent** |
| duality gap (nonzero) | the `q=±1` residue (augmenting path exists) | `ResidueTag` | **built** as residue concept |

So **YES** — max-flow–min-cut falls out as the Kantorovich LP duality on `graph_theory.md`'s graph
(`kantorovich_weak_duality`/`ollivier_plan_optimal`), with the flow = `noether.md`'s conserved current
(`continuity_eq`, `∂·j=0` off `s,t`) and the cut = `homology.md`'s boundary (`delta`/`dsq_zero`,
`δ(𝟙_S)`), the gap the `q=±1` residue and Ford–Fulkerson the augmenting iteration (Hall's recursion
shape). **One object read across the LP duality, the conserved current, and the boundary — no new axis.**

## Note for the technique — does max-flow–min-cut force a new construct?

**Verdict: EXTEND by consolidation — no new primitive; the first THREE-invariant fusion.** Every slot the
flow problem uses already exists: the **graph** (`graph_theory.md`, `⟨V count ∣ Adj⟩` with the direction
and weight read-off axes `C` already carries); the **LP `f**=clo` duality** (`optimal_transport.md`/
`convex_duality.md`, `kantorovich_weak_duality`); the **conserved current** (`noether.md`,
`continuity_eq`/`∂·j=0`); the **boundary `∂`** (`homology.md`, `delta`/`dsq_zero`); the **augmenting
recursion** (`HallMarriage`); the **`q=±1` residue tag** (`ResidueTag`, the gap). The one sharpening: this
is the entry where the LP duality, the conserved current, and the boundary all read the **same object** —
OT used only the duality+weight; max-flow–min-cut shows the *primal constraint* of the LP can be a
**conservation law** (`∂·j=0`) and the *dual object* a **coboundary** (`δ(𝟙_S)`), tying the LP family to
the Noether/homology cluster. The model holds; the front widens by fusion, not by a new axis.

## Verified Lean anchors (file:line:theorem — all grep-verified; purity by `tools/scan_axioms.py` from repo root)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| **cut = boundary `∂` / coboundary `δ`**; `δ²=0` forced by the `q=±1` orientation | `Lib/Math/Cohomology/Delta/Core.lean : delta` (`:54`); `Lib/Math/Cohomology/Delta/V4Capstone.lean : dsq_zero_universal_delta4` (`:41`) | ∅-axiom ✓ (V4Capstone 5/0) |
| **cut = non-flat 0-cochain** (`δσ=0` ⟺ connected-constant; the cut is its complement) | `Lib/Math/Combinatorics/GraphConnectivity.lean : IsClosed` (`:42`), `closed_eq_root` (`:50`), `closed_const` (`:61`), `closed_false_or_true` (`:69`), `closed_root_determines` (`:79`) | ∅-axiom ✓ (8/0 this scan) |
| **cut on the actual bipartite adjacency** (the network's `Adj` wired in; connected ⟹ cut splits it) | `Lib/Math/Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean : bipAdj` (`:248`), `bipAdj_connected` (`:254`), `isConstOnEdges_isClosed` (`:267`), `isKer_const_via_framework` (`:293`) | ∅-axiom ✓ (20/0) |
| **flow = conserved Noether current**; `∂·j=0` continuity; conserved off the boundary; the iff | `Lib/Math/NumberSystems/Real213/ModularGeometry/NoetherCurrent.lean : continuity_eq` (`:97`), `density_conserved_of_det_one` (`:117`), `noether_local` (`:149`), `noether_global` (`:178`); defs `density` (`:72`), `current` (`:81`), `dtDensity` (`:76`) | ∅-axiom ✓ (14/0) |
| **weak duality** `\|f\| ≤ cut capacity` = the adjoint inequality (`dualValue ≤ transportCost`) | `Lib/Math/Geometry/DiscreteCurvature/OllivierRicci.lean : kantorovich_weak_duality` (`:52`); defs `transportCost` (`:36`), `dualValue` (`:40`), `rowMarg` (`:30`), `colMarg` (`:33`) | ∅-axiom ✓ (60/0) |
| **strong duality / zero gap** (a flow and a cut meet ⟹ max-flow = min-cut) = closure exact | `OllivierRicci.lean : ollivier_plan_optimal` (`:106`), `ollivier_bracket` (`:91`, the gap bracket) | ∅-axiom ✓ (same module) |
| **Ford–Fulkerson augmenting-recursion SHAPE** (matching computed by augment; `HallCond` = the obstruction never hit) | `Lib/Math/Combinatorics/HallMarriage.lean : hall_matching_two` (`:618`), `computeNeighbor` (`:400`), `scanAvoid` (`:412`), `scanAvoid_spec` (`:421`); count-Lens `countB` (`:34`), `countB_pos_of_exists` (`:189`) | ∅-axiom ✓ (36/0) |
| **the `q=±1` residue tag** (the duality gap: tight `q=+1` / augmenting-path-exists `q=−1`) | `Lib/Math/Foundations/ResidueTag.lean : residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`), `golden_is_converge` (`:180`), `escape_residue_outside` (`:133`), `converge_residue_fixed` (`:160`) | ∅-axiom ✓ (55/0) |
| cross-frame: graph has no own C (`⟨V count ∣ symmetric Adj⟩`); LP duality on a graph | `graph_theory.md`; `optimal_transport.md` (`kantorovich_weak_duality`, `ollivier_plan_optimal`); `noether.md` (`continuity_eq`); `homology.md` (`dsq_zero`) | prior, ∅-axiom ✓ |

> Axiom-purity note: scanned via `tools/scan_axioms.py` from repo root this session — `NoetherCurrent`
> **14/0**, `OllivierRicci` **60/0**, `HallMarriage` **36/0**, `ResidueTag` **55/0**,
> `Cohomology.Delta.V4Capstone` **5/0**, `Combinatorics.GraphConnectivity` **8/0**,
> `Cohomology.Bipartite.Parametric.Betti.KernelConstancyUniversal` **20/0**. All pure / 0 dirty.
> (`graph_theory.md` reports `GraphConnectivity` 16/0 from a joint dependency scan; the standalone
> module scan this session is 8/0 — reported as scanned, not as the docstring count.)

## Dropped / flagged (honest — predicted-not-built, grep-confirmed)

- **The named flow/cut/Menger object layer — ABSENT.** Grep over `lean/E213/` for
  `maxFlow|minCut|max_flow|min_cut|flow|network|FlowNetwork|Menger|FordFulkerson|fordFulkerson|
  augmentingPath|residualGraph|capacity` returns **no** flow-network object. The only hits are:
  *channel/nuclear capacity* (`Probability/Information/Channel.lean`, `Physics/Nuclear/MagicNumbers.lean`
  — information capacity, unrelated); *Cayley–Menger* geometry (`Geometry/LatticeArea.lean` — the
  distance determinant, not Menger's path theorem); and `RicciFlow`/`GradientFlow`/`MonovariantFlow`
  (Ricci/gradient flows, unrelated to network flow). As predicted in the brief, the named layer is
  not built; the *structure* it inhabits (the LP duality, the conserved current, the boundary `∂`, the
  augmenting recursion) is.
- **A flow-specific `augment`/`residualGraph`/`fordFulkerson` over a capacitated directed network —
  ABSENT, the engine certified.** The augmenting-recursion *engine* is built (`HallMarriage`,
  `computeNeighbor`/`scanAvoid`, the matching computed not asserted), and bipartite matching = max-flow
  on a unit-capacity network (König), but the general capacitated `augment` step welded to a residual
  graph is unwritten — the same "engine built, named instance open" shape as `optimal_transport.md`'s
  missing `Wasserstein`/`Monge`.
- **The cut as `δ(𝟙_S)` is a *conceptual weld*, not a single theorem.** `delta`/`dsq_zero` (the `∂`) and
  `GraphConnectivity.closed_const` (the δ⁰-flat/cut line) are both PURE, but a *stated* theorem
  "cut-capacity `= Σ` weight over `support(δ 𝟙_S)`" on a capacitated network is not written — the pieces
  are present, the weld is unstated (parallel to `graph_theory.md`'s unstated `ker(wLap)={constants}`
  operator theorem).
- **Max-flow = min-cut as a *stated* network theorem — ABSENT; only the LP shadow is built.** The
  `kantorovich_weak_duality`/`ollivier_plan_optimal` LP duality is the OT-coupling instance, not a
  `maxFlow f = minCut (S,T)` statement over `f : E → ℤ` with conservation. The duality *core* is a
  committed ∅-axiom theorem; the flow-network *instantiation* of it is the named open target.

## Verified buildable witness (the calculus names it precisely)

**Open Lean target — the smallest weld that promotes this entry's flow leg from cross-frame to a closed
flow derivation:** on a tiny fixed directed network (`s → a`, `s → b`, `a → t`, `b → t`, integer
capacities), define `flow : E → ℤ` with the conservation predicate `consv v := Σ_{in} f = Σ_{out} f`
(instantiating `NoetherCurrent.continuity_eq`'s `∂·j=0` per internal vertex), `cut (S) := Σ_{e:S→T} c e`
(instantiating `Delta/Core.delta` on `𝟙_S`), and prove `flowValue f ≤ cut S` by `kantorovich_weak_duality`'s
adjoint pattern (the conserved current's boundary charge bounded by the crossing capacity), then exhibit a
meeting flow/cut pair (`flowValue = cut`) and invoke `ollivier_plan_optimal`'s zero-gap shape to pin
`maxFlow = minCut` on this instance — the **flow-network instance of the Kantorovich LP**, parallel to
`OllivierRicci`'s `triPi`/`c4Pi` worked transport optima (`dualValue = transportCost = 1, 2, 5`). A second
target: the **Menger count instance** at unit capacities, reusing `HallMarriage`'s `countB`/matching to
count edge-disjoint `s`–`t` paths = the min cut — the count version, the matching/König bridge made a
flow theorem. Both are `decide`-checkable small instances; **not asserted here** — flagged as the
buildable witnesses, not claimed built.

## Verdict: EXTEND by consolidation (LP duality × Noether current × boundary `∂`), one PARTIAL — the first three-invariant fusion

Max-flow–min-cut **extends and consolidates** — it adds no axis and does not break the model. The three
load-bearing legs are grounded ∅-axiom and the corpus already had them: the **Kantorovich LP duality**
(`kantorovich_weak_duality` / `ollivier_plan_optimal`, 60/0), the **discrete conserved current**
(`NoetherCurrent.continuity_eq` / `∂·j=0`, 14/0), and the **boundary `∂`** (`delta` / `dsq_zero` /
`closed_const`, V4Capstone 5/0 + GraphConnectivity 8/0), with the **augmenting recursion** certified by
Hall (`hall_matching_two`, 36/0) and the **gap** tagged by `ResidueTag` (55/0). The NEW datum — passing
the re-skin guard against `optimal_transport.md` — is that max-flow–min-cut is the **same Kantorovich LP
duality read on `graph_theory.md`'s graph**, with the primal constraint being `noether.md`'s **conserved
current `∂·j=0`** (not OT's marginals) and the dual object being `homology.md`'s **coboundary `δ(𝟙_S)`**
(not OT's Lipschitz potential) — **the first entry where the LP duality, the conserved current, and the
boundary all fuse on one object**. The one PARTIAL is the **named flow/cut/Menger object layer**
(`maxFlow`/`minCut`/`flow`/`network`/`Menger`/`FordFulkerson`/`augment`/`residualGraph`) — **absent**,
predicted-not-built and grep-confirmed, located precisely: the structure they inhabit is present and
certified, only the named instances are unwritten.
