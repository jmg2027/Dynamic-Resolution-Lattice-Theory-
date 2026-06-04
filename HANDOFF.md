# Session Handoff — 2026-06-04 (G121 M2 universal close)

## Branch
`claude/g121-geometric-knot-OIMkV` — pushed.
`cd lean && lake build` ✓ (full package).  New + touched modules
∅-axiom verified via `tools/scan_axioms.py`.

## What Was Done This Session

### G121 knot M2 — universal δ⁰-kernel = constants (structural close)

M2 ("chart-Lens visible count = chartBase − 1") was an **abstract
close for K_{3,2}^{(c=2)} only**: `KChartLens` carried
`selfPointingAxes` as a user-supplied value, grounded by a `decide`
on the single deployment (`V32Betti`).  The fully universal
`∀ NS NT c` version was flagged open in three files
("requires graph-walk connectedness induction").

Now closed **universally and ∅-axiom** at the structural level:

- **NEW** `lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/KernelConstancyUniversal.lean`
  (14 PURE / 0 DIRTY).  For every connected K_{NS,NT}^{(c)}
  (NS ≥ 1, NT ≥ 1, c ≥ 1):
    · `isKer_iff_const` — δ⁰-kernel cochain ⟺ globally constant
    · `isKer_const_false_or_true` — kernel = exactly the 2 constants
    · `isKer_root_determines` — root colour = single free parameter
      (`dim ker δ⁰ = 1`, b₀ = 1)
    · `visible_plus_one` — `(NS+NT) − 1` additively
    · ★★★★★ `universal_kernel_close` — the bundle.
  Uses a **product-indexed coboundary** `delta0Tri`
  (edges `Fin NS × Fin NT × Fin c`, no integer-decode division) and
  additive T-index recovery via `Nat.le.dest`, so the connectedness
  proof carries zero `propext`.  Pointwise statements throughout
  (no `funext` → no `Quot.sound`).

- **Consumer** `Geometry/GeometrizationConjecture/KChartLensAbstract.lean`:
  `forcedKChartLens` (selfPointingAxes = 1, chartVisibleAxes =
  `(NS+NT).pred`, forced by connectedness — no supplied value) +
  ★★★★★★ `m2_universal_forced_partition` +
  `forcedKChartLens_chartVisible_eq_ansatz` (forced value = ansatz
  `chartVisibleAxes NS NT = (NS+NT)−1`, by `rfl`).

- `Ansatz.selfPointingAxes` docstring updated: the `1` is now the
  *derived* kernel dimension, not a committed value.

### Graph-connectedness induction infrastructure (the cited missing piece)
The parametric cohomology had flagged "graph-connectedness induction
infrastructure" as absent.  Now built:
- **NEW** `lean/E213/Lib/Math/Combinatorics/GraphConnectivity.lean`
  (8 PURE).  Abstract reachability `Reach Adj root` (inductive
  predicate) over any `Adj : V → V → Prop` + `closed_const`,
  `closed_false_or_true`, `closed_root_determines`: a δ⁰-closed Bool
  colouring on a connected graph is globally constant (b₀ = 1).
  Structural induction on the inductive predicate ⇒ ∅-axiom.
- Instantiated in `KernelConstancyUniversal` (`bipAdj`,
  `bipAdj_connected` — K_{NS,NT}^{(c)} connected for NS,NT≥1 —,
  `isKer_const_via_framework`), isolating the only graph-specific
  fact (connectedness) from the domain-agnostic framework.

### Headline synthesis (M1 ∘ M2)
`KChartLensAbstract.dM_four_via_M1_forced_and_M2_universal_kernel`
(PURE): M1 (forced chartBase = 5 = d_213) ∘ M2 (forced deployment's
δ⁰-kernel = 2 constants ⇒ selfPointingAxes = dim ker δ⁰ = 1, derived)
⇒ d_M = chartBase − 1 = 4.  First theorem where d_M = 4 routes through
the derived kernel dimension, not the definitional `selfPointingAxes`.

### "Why only d=4": criticality is forcing (M1), not kernel (M2)
`KChartLensAbstract.every_dimension_realized` +
`criticality_is_forcing_not_kernel` (PURE): now that M2 is
dimension-uniform (δ⁰-kernel = 2 constants for *every* connected K — the
star K_{d,1}^{(c=1)} realizes every d_M = d), d_M = 4 criticality is
shown to come purely from M1 forcing, not the kernel.  The "− 1"
self-pointing mechanism is universal; the "4" is the forced base minus
that universal 1.  This is the sharp 213 answer to the chapter's opening
"왜 4차원에서만" question.

### Why the old enumeration route was blocked (recorded)
Counting flat cochain indices universally forces core Lean's
`Nat.div` / `Nat.mod` lemmas to decode `Fin (c·NS·NT)` → `(s,t,m)`;
**all** of them carry `propext` (probe-verified), and
`Nat.add_sub_cancel'` / `Nat.sub_lt_left_of_lt_add` likewise.  So the
universal-flat statement is axiom-dirty by Lean-core construction —
a purity artifact, not a math gap.  The product-form route avoids it.

## G121 knot status (after this session)

| Knot | Status |
|---|---|
| M1 (why d_213 = 5) | two-route close (atomicity a₀=2 + Möbius c=2); irreducible at a₀=2 = Raw Clause 1 |
| M2 (chart count = d−1) | **UNIVERSAL CLOSE (structural)** — δ⁰-kernel = constants (dim 1) for all connected K, ∅-axiom |
| M3 (NT-axis split) | **open frontier** — derive *which* T-axis is time vs self-pointing, and why the split is T-side not S-side (the live knot) |
| M4 (KK firewall) | doc-level stereotype warnings |

The headline `d_M = d_213 − 1` now holds **universally**:
`chartVisibleAxes = chartBase − 1` for every connected K, the "−1"
being the universally 1-dimensional self-pointing kernel.

## Native ∅-axiom primitives built this arc (foundations the repo lacked)

The G121 work repeatedly hit Mathlib-free Lean-core walls — core
`Nat.div`/`Nat.mod`, `List` mem/nodup/length, and function `funext` all
carry `propext`, and there is no `Fintype`/`Finset.card`.  Three reusable
native primitives now route around them:

- `Lib/Math/NumberTheory/EuclideanDivision.lean` (4 PURE) — `n = d·q + r`,
  `r < d` existence + uniqueness by upward induction (no core `Nat.div`).
- `Lib/Math/Combinatorics/GraphConnectivity.lean` (8 PURE) — abstract
  reachability induction → δ⁰-closed colouring constant on a connected
  graph (b₀ = 1 for any adjacency).
- `Lib/Math/Combinatorics/BoolEnum.lean` (12 PURE) — finite Bool-cardinality
  enumeration: `allBoolLists n` (the `2^n` length-`n` Bool lists) +
  `length = 2^n` + completeness + nodup, with a reusable pure `List`
  mem/nodup toolkit.  Cochains as `List Bool` ⇒ no `funext`, count by
  `List.length` ⇒ no `Fintype`, structural enumeration ⇒ no division.

### Cardinality-framework roadmap (the hard track)
  - **Stage 1 — DONE** (`BoolEnum`): enumeration + `length = 2^n` +
    completeness + nodup + pure `List` toolkit.
  - **Stage 2 — DONE** (`BoolEnum` counting): `bcount` toolkit +
    `bcount_const = 2` — the **division-free universal count-Lens form of
    `b₀ = 1`** (constant-list count = `|ker δ⁰|`, via
    `KernelConstancyUniversal.isKer_iff_const`).  Clean induction route
    (value-fixed predicates under cons), no pigeonhole needed.
  - **Stage 3 — DONE** (`BettiOneUniversal.lean`, 2 PURE): **universal
    first Betti number** `b₁ = E − V + 1` (= `1/α₃ = NS² − 1` universal).
    Assembled from the ∅-axiom counts `|C⁰| = 2^V`, `|ker δ⁰| = 2`,
    `|im δ⁰| = 2^(V−1)` (= `bcount_headFalse`, the head-`false` canonical
    representatives) + rank-nullity / first-iso arithmetic
    (`Pow213.pow_add_two`).  `betti_one_K32`: `b₁ = 8 = NS² − 1` for the
    forced deployment.

    Caveat CLOSED to its mathematical essence: `|im δ⁰| = 2^(V−1)` is an
    actually-counted image cardinality, fully ∅-axiom.
    `PathCoboundary.im_count_inj_complement` (PURE) proves the GENERAL
    fact — any `β`-valued map on length-`V` colourings that is
    complement-invariant and injective on head-`false` colourings has
    exactly `2^(V−1)` distinct values (head-`false` reps map inj +
    surj onto the image; no `funext`/`Fintype`/`Nat.div`).  This is
    rank–nullity `|im| = |C⁰|/|ker| = 2^V/2` realised combinatorially.
    Its two hypotheses are the only graph input and BOTH are proven for
    the complete-bipartite δ⁰: complement-invariance always; head-`false`
    injectivity = `ker = constants` = `isKer_iff_const`.
    `im_pathDelta_card` is the path-graph instance.  Reusable infra:
    `ListCount` (nodup cardinality + `nodup_map_of_inj`), `BoolEnum`
    complement/transversal + `filter_length_eq_bcount`.

    FULLY WIRED: `KEdgeCochain.im_edgeCochain_card` (14 PURE)
    instantiates `im_count_inj_complement` at the genuine list-valued
    complete-bipartite coboundary `edgeCochain NS NT σ = [σ[s]⊕σ[NS+t]]`,
    with both hypotheses proven directly on lists
    (`edgeCochain_complement`; `edgeCochain_inj_headFalse` via the
    connectivity reconstruction).  So `|im δ⁰_K| = 2^(V−1)` for K_{NS,NT}'s
    OWN coboundary (`im_edgeCochain_K32` = `2^4`) — no funext / Fintype /
    Nat.div / cited bridge.  `b₁ = E − V + 1` is now end-to-end ∅-axiom
    (`|im|` is c-independent; the c=1 edge set suffices for the count, the
    full E enters only |C¹| = 2^E).  Own pure `rangeL`/`flatMap`/`getD`
    List toolkit built en route.

## Open Problems (Priority Order)

1. **M3 (NT-axis split)** — the lone knot needing a genuine
   derivation.  M2 proves *one* axis is self-pointing (the 1-dim
   kernel); M3 asks which of the N_T axes is time vs self-pointing
   and why the donation is T-side (cardinality 2), not S-side.
   Candidate handles: c=2 binary cover acts on T-side; K_{3,2}
   bipartite asymmetry.  Note: the originator deprioritized M3 as
   "downstream of physics interpretation" — confirm before pushing.
2. **M2 operator-flat bridge (optional)** — a division-free
   `Fin (c·NS·NT) ≃ Fin NS × Fin NT × Fin c` re-indexing would
   transport the structural kernel result to the flat
   `CochSpaces.delta0`, giving the universal-flat statement
   ∅-axiom.  Not a math obstruction; the structural content is
   closed.

## File Map
```
lean/E213/Lib/Math/Combinatorics/GraphConnectivity.lean                           ← NEW (8 PURE): abstract graph-connectedness induction
lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/KernelConstancyUniversal.lean  ← NEW (20 PURE): universal δ⁰-kernel = constants + framework instantiation
lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/INDEX.md                       ← +KernelConstancyUniversal row + universal-closure section
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/KChartLensAbstract.lean       ← +forcedKChartLens, m2_universal_forced_partition (import KernelConstancyUniversal)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/Ansatz.lean                   ← selfPointingAxes docstring (derived)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/INDEX.md                      ← M2 status → UNIVERSAL CLOSE
theory/math/cohomology/bipartite.md                                               ← universal-kernel narrative section
research-notes/frontiers/G121_dim4_self_pointing_axis.md                          ← Part 4: M2 universal close
```

## Three-tier state
- **Promotions this session**: none new (M2 narrative lives in the
  existing `theory/math/cohomology/bipartite.md` chapter).
- **Active scratchpad**: `research-notes/frontiers/G121_dim4_self_pointing_axis.md`
  (Part 4 added).  Sink rule holds.
