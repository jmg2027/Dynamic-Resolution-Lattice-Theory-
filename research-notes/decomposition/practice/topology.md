# Decomposition: topology (open sets, compactness, the Heine–Borel / finite-subcover phenomenon)

*A FRESH decomposition of point-set topology per `../README.md` (model v7.1). Continues
`continuity.md` (the resolution dial promoted to a discipline) and `cardinality.md`/`measure.md`
(the count-reading's `q=±1` residue tag). The target: does the calculus PREDICT **compactness** as
the **finiteness-collapse of the resolution structure** — the `q=+1` corner dual to `cardinality.md`'s
`q=−1` diagonal escape? Answer: YES at the phenomenon level (`ExtremeValue`'s reached-by-none `Msup`),
and the prediction simultaneously LOCATES the precise missing leg — an arbitrary-cover quantifier the
finite-`List` cover object structurally cannot express.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **dyadic refinement tree** (same `C` as `continuity.md` /
  `integration.md` / `measure.md`): a "point" is not a primitive, it is a *bracket-pointing*
  (`DyadicBracket`, carrying `numA, numB, expE`) that narrows as the exponent grows; a point is the
  residue of a refinement sequence, never held. A "space" is the construction of these nested
  brackets. Nothing topological is a primitive — only "a narrowing region".

- **Reading `L` — the resolution dial of `continuity.md`, now read on *subsets* and on *covers*.**
  Topology is `continuity.md`'s resolution-comparison reading (`close k`: do two pointings agree up
  to `1/2^k`?) applied not to a map but to a *region* and to a *family of regions*:
  - An **open set** = the dial's **refinement-stable fibre**: a region you can keep refining and
    never leave. 213 builds it as `DyadicOpen := List DyadicBracket` (`DyadicOpen.lean:28`) — a
    *finite* union of brackets, finite **by construction** (`dyadic_open_finite`, `:64`); size
    additive under union (`size_union`, `:54`). "Open from inside with a resolution-margin" is exactly
    "a bracket the refinement tree keeps you inside". (The `continuity.md` hypothesis "open-ness =
    resolvable from inside" is confirmed *at the object level*; the preimage law that would weld it to
    continuity is the standing missing leg — see Residue and the verdict.)
  - **Continuity** = the dial **commuting with refinement** = preimage-of-open-is-open
    (`continuity.md`): `ContinuousWithModulus … ∀ m x y, MD.close (ω m) x y → MV.close m (f x) (f y)`
    (`UniformLimitContinuous.lean:98`), the modulus `ω : Nat → Nat` the whole content
    (`IsContinuousModulus`, `Continuity.lean:28`). (Lean agent concurrently certifying
    `continuous_iff_preimage_dyadicopen` — grep confirms it is **not yet in `lean/E213`**; cited as
    in-progress, not built here.)
  - **A cover** = a *family* of opens whose union is the region; **compactness** = the demand that
    *every* such family admits a **finite** subfamily — the count-reading (`cardinality.md`) forcing a
    finite resolution on the cover.

- **Residue — the crux, and it splits at exactly the `q=±1` poles of `cardinality.md`/`measure.md`.**
  Read the **count-reading on the cover-family** (how many opens are needed to keep the region
  resolved?). Its self-application surplus carries the tag:
  - **`q=+1` (converge / finiteness-collapse) — COMPACTNESS.** On the dyadic substrate a cover *is*
    a finite `List DyadicBracket` (`DyadicOpen`), so the "finite subcover" demand is discharged before
    it is asked: the cover already has finite length (`heineBorel`, `Compactness.lean:42`;
    `compact_bounded_by_length`, `:66`). The `q=−1` escape — *an infinite cover with no finite
    reduction* — **cannot arise**, exactly as `measure.md`'s non-measurable set cannot arise on a
    finite `List`. Compactness = the corner where the count-reading on the cover **closes** (a fixed
    point: the cover is its own finite subcover). This is the literal dual of `cardinality.md`'s
    diagonal: there the count-reading's self-cover is forced fixed-point-*free*; here it is forced
    fixed-point-*ful* (the finite list reaches itself).
  - **`q=−1` (escape / reached-by-none) — the LIMIT POINT, and non-compactness.** The region's
    supremum / accumulation point is reached by no finite depth, only narrowed by the modulus — the
    `Real213` cut `ModContOnGrid.Msup` (`ExtremeValue.lean:300`), the analysis-level
    `object1_not_surjective`. Where the finiteness-collapse *fails* (the maximizer is not attained at any
    finite resolution), the residue is the `q=−1` escape — the reached-by-none `Msup` (the module narrates
    this in its §5 "the forcing point", `ExtremeValue.lean:335`, a prose header).

## Re-seeing — ⟨C | L⟩

```
   point / space      =  ⟨ dyadic refinement tree | — ⟩                         (C, before any reading)
   open set U          =  ⟨ region | L_res's refinement-stable fibre ⟩ = List DyadicBracket (FINITE by C)
                          "x ∈ U with a resolution-margin (a close-m ball inside U)" = a bracket holds x in
   continuity of f     =  the CONDITION ⟨C|L_res⟩ commutes with refinement = preimage-of-open-is-open
                          MD.close (ω m) x y → MV.close m (f x)(f y)   (operand = ω : Nat→Nat, never the limit)
   open COVER of K     =  a FAMILY of opens whose union ⊇ K            (count-reading on the family)
   COMPACTNESS         =  Residue(count-on-cover, C) at q=+1  =  the cover IS a finite List → finite-subcover is rfl
                          (the count-reading on the cover CLOSES — fixed-point-ful, finiteness-collapse)
   non-compactness     =  Residue(count-on-cover, C) at q=−1  =  an infinite cover with no finite reduction
   limit / accum. point=  Residue(L_res) at q=−1  =  the Real213 cut = reached-by-none Msup = object1_not_surjective
   connectedness       =  finite-list adjacency (Chain)               (chain_finite — finitely bounded by C)
```

So **open, continuous, compact, connected, and the limit point are one reading at work** — the
resolution dial of `continuity.md`, here read on subsets (open = stable fibre), on maps (continuous =
commutes), on cover-families (compact = the count closes), and on accumulation (limit = the count
escapes). Topology is `continuity.md`'s "calculus of which readings survive the dial", with the
compactness axis added: *whether the count-reading on the cover closes (`q=+1`) or escapes (`q=−1`)*.

## Revelation — PREDICTION (finiteness-collapse), with the missing leg located precisely

**The single biggest find: compactness IS the `q=+1` finiteness-collapse corner of the resolution
structure, the exact dual of `cardinality.md`'s `q=−1` diagonal escape — the SAME residue tag that
`measure.md` used to derive the repo's Choice-free stance now derives the repo's *trivial* Heine–Borel.**

The forcing argument is one sentence read at both poles of the count-reading on the cover:

- **`q=+1` (compactness = the diagonal cannot escape).** `cardinality.md`'s engine is
  `OneDiagonal.no_surjection_of_fixedpointfree` (`OneDiagonal.lean:51`, PURE): a *fixed-point-free*
  modifier forces a self-cover to **miss a row** (escape). Compactness is the **contrapositive
  corner**: on a finite `List`, the count-reading on the cover has a **fixed point** — the cover is
  its own finite subcover (`heineBorel`, `Compactness.lean:42`) — so the escape diagonal **has no
  operand**. This is the same move as `measure.md`: "Vitali / Banach–Tarski cannot arise" because the
  `q=−1` uncountable self-cover is never built; here "no infinite cover with no finite subcover" because
  the cover object IS a finite `List` (`DyadicOpen.lean:28`). **Non-compactness = the `q=−1` escape
  residue; compactness = its structural absence** — tagged identically to Cantor/Gödel/measure's
  Choice split via `ResidueTag` (`ResidueTag.lean:73`, `escape_residue_outside :133`,
  `converge_residue_fixed`, `residue_tag_two_poles`, 55/0 PURE). The repo's "Heine–Borel is `rfl`"
  is therefore **not a convenience of the encoding — it is the predicted `q=+1` corner content**,
  derived (not stipulated) from the residue tag, exactly as `measure.md` derived "no Choice".

- **`q=−1` (the residue surfaced — the reached-by-none maximizer; §5 "the forcing point").** The
  genuine compactness *phenomenon* — "a continuous function on a compact interval attains its max" — is
  built honestly as the `q=±1` split itself (all in the `ModContOnGrid` namespace): `ModContOnGrid.evt_sup`
  (`ExtremeValue.lean:362`, 23/0 PURE) proves the sup VALUE is (i) a computable cut (`Msup`, `:300`, a
  `CauchyCutSeq.limit` — a Real213 cut, reached by no finite grid), (ii) **located/approached** to every
  scale (`ModContOnGrid.sup_approached`, `:318`), and `ModContOnGrid.gridMax_attained` (`:275`) gives the
  dual: the max **attained at every FINITE resolution** — the `q=+1` finiteness-collapse. So the true
  maximizer is the limit `Msup` reached by NONE (the analysis-level `object1_not_surjective`); the
  module's §5 narrates this as "the forcing point" (`ExtremeValue.lean:335`, a *prose* section header, not
  a theorem name). Compactness's content is literally: **finite-resolution attainment (`q=+1`,
  `gridMax_attained`) + maximizer reached-by-none (`q=−1`, `Msup`/`evt_sup`)** — the count-reading closing
  on each finite grid, escaping at the limit. This is the `reached_by_none` residue
  (`theory/essays/foundations/reached_by_none.md`) read on the argmax.

This passes the re-skin guard at the prediction bar: it does not re-describe Heine–Borel — it **derives
its triviality** from the residue tag (the `q=+1` corner), and **derives where it stops being trivial**
(the maximizer, `q=−1`, the reached-by-none `Msup`), unifying compactness with Cantor (`cardinality`), the
Choice split (`measure`), Gödel (`godel`), and φ/Gaussian/ODE (`golden_ratio`/`gaussian_clt`/`differential_equations`)
under the one `ResidueTag`. The resolution axis (`continuity.md`) and the residue tag
(`cardinality.md`/`measure.md`) are **consolidated**: topology is the resolution dial read on subsets,
and its compactness axis is the count-reading's `q=±1` pole on the cover.

### The precise missing leg (located, like `knots.md`/`measure.md`)

**The arbitrary-cover quantifier is structurally absent — and its absence is the SAME shape as
`measure.md`'s missing countable-cover `q=−1` half.** `Compactness.lean` does **not** state the
classical predicate `∀ (cover : Family of opens), (⋃ cover ⊇ K) → ∃ finite subcover`. It states only
that a *given* `DyadicOpen` (already a finite `List`) has finite size (`heineBorel`,
`compact_bounded_by_length`) — i.e. it asserts the `q=+1` conclusion on an object that is finite **by
construction**, never quantifying over *infinite* families. The genuine theorem would need:
1. a cover **family** type that *can* be infinite (a `Nat → DyadicOpen` indexed family, or a predicate
   on opens), so the finite-subcover claim is non-vacuous — the finite-`List` `DyadicOpen` cannot host
   the `q=−1` half (an infinite cover) any more than `measure.md`'s finite `List` could host the
   countable-cover infimum; and
2. **real bracket containment** (`db ⊆ U` via `cutLe` boundaries), not the current pointwise
   `IsCover := db ∈ cover` (`Compactness.lean:33`, whose own docstring defers true containment to
   `Continuity.lean`).
This is the dual of `measure.md`'s located break (the omitted `q=−1` countable-cover infimum) and the
sibling of the standing `continuous_iff_preimage_dyadicopen` gap (`continuity.md`): the calculus
PREDICTS the compactness phenomenon and 213 BUILDS its `q=+1` finite-resolution content
(`ExtremeValue`), but the **arbitrary-cover quantifier** that would make Heine–Borel a non-trivial
theorem (rather than a `rfl` on a by-construction-finite object) is the genuinely missing primitive —
an *infinite cover-family construction*, which the finite-`List` setting cannot express. It is not a
break of the model (no new axis); it is the located `q=−1` half the repo deliberately does not build,
named here for the first time on the topology axis.

## Note for the technique

**No new primitive; a decisive consolidation of two existing invariants onto one axis.** Topology does
not add to model v7.1 — it *fuses* its two load-bearing invariants:
- the **resolution dial** (`continuity.md`'s organizing axis) supplies open / continuous / connected
  (the dial's stable fibre / commutation / adjacency), and
- the **`q=±1` residue tag** (`cardinality.md`/`measure.md`/`ResidueTag.lean`) supplies compactness
  (the count-reading on the cover closing at `q=+1`) and the limit point (escaping at `q=−1`).

The lesson: **compactness is the count-reading's `q=+1` pole read on a cover-family**, the exact dual
of cardinality's `q=−1` diagonal — so the repo's "trivial Heine–Borel" and "no non-measurable set" and
"Cantor's diagonal" are *one residue-tag phenomenon* at its two signs, now spanning cardinality,
measure, provability, curvature, AND topology. Interior unchanged; the consolidation is the payoff.

---

## Verified Lean anchors (grep/Read-verified file:line; purity freshly scanned via `tools/scan_axioms.py`, build clean)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| open set = finite bracket union (no σ-algebra/Choice) | `Lib/Math/Geometry/Topology/DyadicOpen.lean:28 DyadicOpen`; `:54 size_union`; `:64 dyadic_open_finite` | ∅-axiom PURE ✓ (10/0) |
| **compactness = finiteness-collapse (the cover IS a finite List)** | `Lib/Math/Geometry/Topology/Compactness.lean:42 heineBorel`; `:52 singleton_covers`; `:58 empty_no_cover`; `:66 compact_bounded_by_length` | ∅-axiom PURE ✓ (7/0) |
| continuity = a `Nat→Nat` modulus (no ε/δ) | `Lib/Math/Geometry/Topology/Continuity.lean:28 IsContinuousModulus`; `:56 composeContinuous`; `:64 compose_modulus_eq` | ∅-axiom PURE ✓ (5/0) |
| continuity commutes-with-refinement (proved theorem) | `Lib/Math/Analysis/UniformLimitContinuous.lean:98 ContinuousWithModulus`; `:136 uniform_limit_continuous`; `:51 MetricModulus`; `:287 closeN` | ∅-axiom PURE ✓ (20/0) |
| connectedness = finite-list adjacency | `Lib/Math/Geometry/Topology/Connectedness.lean:36 Chain`; `:54 chain_self_iff_degenerate`; `:65 chain_finite` | ∅-axiom PURE ✓ (8/0) |
| **the q=±1 split made literal: finite-resolution attainment + maximizer reached-by-none** | `Lib/Math/Analysis/ExtremeValue.lean:275 ModContOnGrid.gridMax_attained`; `:318 ModContOnGrid.sup_approached`; `:362 ModContOnGrid.evt_sup`; `:300 ModContOnGrid.Msup` (the reached-by-none cut). NB `:335 max_reached_by_none` is a *prose* §5 header, not a theorem | ∅-axiom PURE ✓ (23/0) |
| `q=−1` escape engine (the dual of compactness) | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree`; `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective` | ∅-axiom PURE ✓ |
| the residue tag (`q=±1`), both poles | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`; `:133 escape_residue_outside`; `converge_residue_fixed`; `residue_tag_two_poles` | ∅-axiom PURE ✓ (55/0) |
| 4-way modulus unification (one dial, four domains) | `Lib/Math/Geometry/Topology/ModulusStructure.lean:55 IsModulusStructure`; `:185 four_way_modulus_framework`; `:139 three_way_modulus_framework` | cited (prior, `continuity.md`) ✓ |

**Fresh purity scan (this session):** `scan_axioms.py` —
`Topology.DyadicOpen` 10/0, `Topology.Compactness` 7/0, `Topology.Connectedness` 8/0,
`Topology.Continuity` 5/0, `Analysis.ExtremeValue` 23/0, `Foundations.ResidueTag` 55/0,
`OneDiagonal.no_surjection_of_fixedpointfree` PURE, `FlatOntologyClosure.object1_not_surjective` PURE,
`UniformLimitContinuous.uniform_limit_continuous` PURE. All pure / 0 dirty; build clean.

## Conceptual-only / absent legs (honest)

- **Arbitrary-cover quantifier / non-trivial Heine–Borel — ABSENT, located.** `Compactness.lean`
  asserts the `q=+1` conclusion on a by-construction-finite `DyadicOpen`; it does **not** quantify
  over infinite cover-families (no `Nat → DyadicOpen` family + union ⊇ K + finite-subcover statement).
  Its `IsCover := db ∈ cover` (`:33`) is pointwise membership, not true `cutLe` containment (the
  docstring itself defers containment to `Continuity.lean`). This is the precise missing primitive —
  an *infinite cover-family construction* the finite-`List` setting cannot express — the dual of
  `measure.md`'s omitted `q=−1` countable-cover half. **The compactness phenomenon is built
  (`ExtremeValue`); the cover *theorem* is not.**
- **`continuous_iff_preimage_dyadicopen` — NOT in `lean/E213`** (grep: 0 hits). The weld of
  "open = stable fibre" to "continuous = commutes" remains the standing in-progress target
  (`continuity.md`); a concurrent Lean agent is certifying it. Not built here.
- **open / compact / limit *as* fibre / `q=+1` corner / `q=−1` residue *of the same dial*** — this
  identification is the decomposition's reading. Lean certifies each object separately
  (`DyadicOpen`, `Compactness`, `ExtremeValue`'s split, `ResidueTag`); the single theorem welding them
  into "one resolution reading at its two poles" is conceptual framing on verified PURE objects.

> Axiom-purity note: every theorem cited above was freshly scanned with `tools/scan_axioms.py` this
> session (results in the anchors table) — the purity claim rests on a fresh scan, not docstrings.
