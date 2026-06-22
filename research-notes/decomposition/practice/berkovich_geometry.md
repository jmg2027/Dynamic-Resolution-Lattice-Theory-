# Decomposition: Berkovich / rigid analytic geometry — the valuation reading made a space

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`) and
`../SYNTHESIS.md` (two invariants — the character arrow `×↦·`, the `q=±1` residue tag — over the
resolution axis with `base`). Continues `padic.md` (the `base`-resolution = `vp` as a metric),
`prime_factorization.md` (`vp_mul`: the valuation = the additive log of a multiplicative seminorm),
`continued_fractions.md` (the Stern–Brocot / mediant modulus tree), and `stone_duality.md` (the
spectrum = the points-from-readings reconstruction, with the maximality reading a calibrated exterior).
The thesis under test: **a Berkovich point IS a multiplicative seminorm = the `×↦·` character /
valuation made a point; the Berkovich spectrum M(A) = the SPACE of these readings ("object = its
readings"); the Berkovich line's tree (type 1–4 points) = the Stern–Brocot / modulus refinement tree;
contractibility = the tree being a tree = the `q=+1` no-loops converging pointing.** No new primitive —
it is the valuation/character reading made a space, with the modulus tree as its structure.*

## The decomposition

- **Construction `C`** — the **same approximant-sequence-with-modulus as `padic.md`**, now read not for
  *which* completion but for *which seminorm*. A point of Berkovich space is a way of measuring size on a
  Banach ring `A`; on `A = K[T]` (the Berkovich affine line) the size of a polynomial is fixed by a
  **multiplicative seminorm** `|·| : A → ℝ≥0` with `|fg| = |f||g|`, `|f+g| ≤ max(|f|,|g|)`. The
  generative act is exactly the ×-construction of `prime_factorization.md` read through a *size*: a
  seminorm is the multiplicative ×↦· character carried to a non-negative readout. The branching of the
  line is the **mediant / Stern–Brocot subdivision** of `continued_fractions.md` (the `(p,q)` directed
  count-pair fold) — a disk of radius `r` around `a` refines into sub-disks the way a unimodular symbol
  splits at its mediant. So `C` is one thing: a refinement tree of nested disks (= narrowing
  approximant brackets, each tagged by a multiplicative size-reading), plus a modulus.

- **Reading `L_seminorm` (= the `×↦·` character into ℝ≥0, at residue resolution)** — project the ring to
  one **multiplicative seminorm**. This is the calculus's central arrow `Invariant A`: a
  construction-preserving reading whose readout is itself a number-construction (here a size in ℝ≥0)
  carrying the multiplicative law. The Berkovich axiom `|fg|=|f||f|` is *verbatim* the `×↦·` character —
  the same arrow as `vp_mul` (`prime_factorization.md`), `det2_mul`, `legendre_mul`. Its additive log is
  a **valuation** `v = −log|·|` with `v(fg)=v(f)+v(g)` — exactly `padic.md`'s `vp` read as a distance
  (`Zp.valEq_mul`, valuations add under product; `Zp.valEq_add_of_lt`, the ultrametric `max`). So a
  Berkovich point on the line is the `vp`/seminorm of `prime_factorization.md`+`padic.md` *promoted from
  a coordinate to a point*. The reading carries the resolution `base` slot of `padic.md`: which
  radius/valuation measures "close" — the disk radius `r` is the `base`-dial.

- **Residue, tagged `q=±1`** — two strata, the same split as `stone_duality.md`:
  - **Type-1 points (classical / rigid points)** = the `q=+1` **reached** values: a seminorm of the form
    `f ↦ |f(a)|` for an honest point `a` of the variety — the convergent that *lands*, the rigid point.
    These are `continued_fractions.md`'s convergents `pₙ/qₙ` (the modulus that is hit) and `padic.md`'s
    finite-depth truncations.
  - **Type-2/3/4 points (generic / limit points)** = the **residue reached-by-none**: a sup over a disk
    (type 2/3, the "generic point of a disk", radius rational/irrational) or a nested-disk limit with
    empty intersection (type 4) — the limit of a narrowing bracket sequence that no classical point
    inhabits. This is the literal `object1_not_surjective` / `cf_universal_total_modulus` residue applied
    to a *converging* (q=+1) pointing — the disk's seminorm is reached only as the sup over its
    interior, never by a single classical `a`. Type-4 (empty-intersection nested disks) is the
    completion residue exactly as `padic.md`'s reached-by-none limit.
  - **The maximality / completeness reading is the calibrated exterior** (the `stone_duality.md`
    /`nonstandard_analysis.md` boundary). M(A) defined as *all* multiplicative seminorms (a maximal
    object) is the spectrum-as-reconstruction; declaring "these are *all* the points" reifies the
    reached-by-none residue, the same LLPO/choice-strength totalization the corpus locates, NOT a
    ∅-axiom internal object (see VALIDATE).

## Re-seeing

```
   Berkovich point on 𝔸¹  =  ⟨ disk-refinement tree | L_seminorm = the ×↦· character into ℝ≥0 ⟩
   |fg| = |f||g|           =  the ×↦· character           vp_mul / det2_mul (the SAME arrow)
   valuation v = −log|·|   =  vp read as a distance        Zp.valEq_mul (v(fg)=v(f)+v(g))
   ultrametric |f+g|≤max   =  vp is the modulus            Zp.valEq_add_of_lt (strong triangle)
   spectrum M(A)           =  ⟨ A | space of seminorm-readings ⟩   = "object = its readings" (Stone/Yoneda)
   point determined by its readings  =  object1_injective  (faithful: an elt = its readings)
   type-1 (rigid) point    =  the q=+1 reached value (convergent that lands)   convergent pₙ/qₙ
   type-2/3/4 (generic/limit) point  =  Residue(L,C), reached by none          object1_not_surjective
   the Berkovich tree      =  the Stern–Brocot / mediant subdivision tree      mediant_adjacent_both
   tree branching          =  unimodular mediant split                        manin_unimodular_decomposition
   path-connected / contractible  =  the tree is a tree (no loops), q=+1       reduced_betti_d4_contractible
   "M(A) = ALL seminorms"  =  the maximality reading = a CALIBRATED exterior   (LLPO/choice, like 𝒰)
```

The single move: a Berkovich point is **not** a new kind of geometric object — it **is** the
multiplicative seminorm / valuation of `prime_factorization.md`+`padic.md`, made a *point*; the
Berkovich spectrum is the *space of these readings* (`stone_duality.md`'s "object = its readings"); the
Berkovich line's tree is the *Stern–Brocot/modulus refinement tree* of `continued_fractions.md`; and
its contractibility is *the tree being a tree* — the `q=+1` no-loops converging pointing.

## Revelation (collapse + forcing + spine)

**Collapse 1 — a Berkovich point IS the `×↦·` character / valuation, already built.** The defining
seminorm axiom `|fg|=|f||g|` is the calculus's single most-reused arrow. It is `prime_factorization.md`'s
`vp_mul` (`Lib/Math/NumberTheory/PrimeValuation.lean:96`, also `Meta/Nat/VpMul.lean:165`), its log-form
the valuation that *adds under product* and takes the `max` under sum — `padic.md`'s `Zp.valEq_mul`
(`Padic/Norm.lean:461`) and `Zp.valEq_add_of_lt` (`:335`), the literal ultrametric. So "a Berkovich
point = a multiplicative seminorm" collapses to "a Berkovich point = the `vp`/seminorm reading the repo
already proved is a `×↦·` character", made a point rather than a coordinate. No new object — the central
arrow, relocated.

**Collapse 2 — the spectrum M(A) = the points-from-readings reconstruction, the `stone_duality.md`
shape.** M(A) is *defined* as the space of multiplicative seminorms — an object is reconstructed from the
totality of its readings. That is `object1_injective` (`Lens/Foundations/FlatOntologyClosure.lean:47`:
an element is determined by its readings = faithfulness = Yoneda/Stone "object = its realizations"), the
same reconstruction `stone_duality.md` records for `Spec(B)` as ultrafilters and `motives.md`/
`tannakian_duality.md` for realizations. The inverse-limit-of-readings object the calculus uses for
exactly this (profinite/Stone) is `iProdLens` (`Lens/Lattice/IndexedJoin.lean:97`, the meet of a
Lens-family, 8/0). So the Berkovich spectrum is the seminorm-instance of the calculus's own
spectrum = `⟨ A | the space of its character-readings ⟩`.

**Collapse 3 — the Berkovich tree = the Stern–Brocot / modulus refinement tree.** The branching of the
Berkovich line (disks within disks, each point a sup over a disk) is the **mediant subdivision** of
`continued_fractions.md`: `mediant_strictly_between` (`Mediant.lean:54`) and `mediant_adjacent_both`
(`:77`, SL₂-unimodularity preserved under mediant) are the tree's branch rule, and
`manin_unimodular_decomposition` (`MinkowskiModularSymbol.lean:52`) is a unimodular symbol splitting into
two unimodular children — *the* tree branch. The type-1 points are the convergents (`continued_fractions`'s
`pₙ/qₙ`, the modulus that lands); type-2/3/4 are the residue at the nodes/limits. CF convergents,
modular-symbol periods, and Berkovich-line points are **one Stern–Brocot walk read three ways** (a
number's approximants / a geodesic's unimodular pieces / a disk-tree's seminorms).

**Forcing — contractibility is FORCED by the tree being a tree (`q=+1`, no loops).** The Berkovich line
is path-connected and contractible because it is an ℝ-tree: between any two points there is a unique arc
(up the tree to the join, back down), and there are no loops. In the calculus this is the `q=+1`
converging pole: a tree's reduced first Betti number is zero — `reduced_betti_d4_contractible`
(`Cohomology/Examples/BettiKernel.lean:63`, `ker δ = im δ`, the residue is empty, 11/0), the `q=+1`/exact
contractible pole that `NonzeroBetti.lean`'s `cycle_vs_contractible_qpm` (`:173`, 56/0) contrasts against
the `q=−1` non-contractible cycle (`loopClass_not_coboundary`, `:134`, `b₁=1`). The finiteness of the
arc — every two points joined by a *finite* chain — is `chain_finite`
(`Geometry/Topology/Connectedness.lean:65`, 8/0). So "the Berkovich line is contractible" is forced: it
is a tree, a tree has no loops, no loops = `q=+1` = `reduced_betti_d4_contractible`. The `q=±1` spine of
`SYNTHESIS.md` §3 reads it directly: contractible/converge (tree, q=+1) vs a non-contractible loop
(`fundamental_group.first_loop_is_the_fold`, q=−1).

**Spine — the residue doctrine, on a geometry.** Analytification `Xᵃⁿ` = reading a variety `X` through
its seminorm-spectrum (every classical point is a type-1 seminorm; the analytification *adds* the
type-2/3/4 residue points so the space becomes connected and contractible). This is the residue doctrine
of `continued_fractions.md`/`SYNTHESIS.md` made geometric: the classical (rigid) points are the modulus
(the convergents that land); the generic/limit points are the residue (reached by none, pointed at by
all). The "miracle" of Berkovich geometry — that adding the limit points makes the totally-disconnected
rigid space into a nice connected tree — is exactly **the limit being the residue's shape, not a god
above it**: the residue points are what the seminorm reading forces but no rigid point captures, and
filling them in is filling in the tree's interior nodes.

## VALIDATE verdict — **PREDICTION + a CALIBRATED BREAK** (no new primitive; named Berkovich objects ABSENT)

**No `Berkovich`/`seminorm`/`analytification`/`rigidSpace` object exists in the repo** (grep-confirmed,
zero hits for `Berkovich|seminorm|analytic_space|analytification|rigidSpace|rigid_analytic` across
`lean/E213/`). So this is **PREDICTION** at the structural/skeleton altitude — every load-bearing leg is
a *built* `×↦·` character / valuation / mediant-tree / contractible-Betti theorem, and the *named*
Berkovich objects are the open targets — plus one **calibrated break** at the maximality reading.

- **PREDICTION (the structural skeleton, all legs built ∅-axiom).** The calculus predicts, and the repo
  independently built, every component: a point = the multiplicative seminorm = the `×↦·` character
  (`vp_mul`, `Zp.valEq_mul`); the spectrum = the space of these readings (`object1_injective`,
  `iProdLens`); the tree = the mediant/Stern–Brocot subdivision (`mediant_adjacent_both`,
  `manin_unimodular_decomposition`); contractibility = the tree's empty reduced `H¹` (`q=+1`,
  `reduced_betti_d4_contractible`, with the `q=−1` loop contrast in `NonzeroBetti`). The match is
  evidence, not construction-to-fit: the seminorm, the tree, and the contractible-Betti pole were each
  built for other fields before this decomposition.

- **CALIBRATED BREAK (the same kind as `stone_duality.md`/`nonstandard_analysis.md`, not a new wall).**
  M(A) *as a maximal object* — "the space of **all** multiplicative seminorms", deciding the totality of
  size-readings — reifies the reached-by-none residue, the same totalization `stone_duality.md` locates
  for the ultrafilter spectrum and `nonstandard_analysis.md` calibrates at LLPO. The *internal* horn —
  each individual seminorm/valuation as a sequence-with-modulus, the tree, the type-1 convergents, the
  contractibility — is ∅-axiom (the built legs). The *break* horn — M(A)'s **completeness** ("these are
  ALL the points", every nested-disk family has a point, the Banach-ring `M(A)` compact Hausdorff) — is
  the maximality reading, the calibrated exterior, NOT built. This is the geometric twin of Ostrowski
  exhaustiveness in `padic.md` (the family is instantiated, "no others" is conceptual): the seminorm
  *instances* and the *tree* are built; the *spectrum-is-all-of-them / compactness* claim is the
  located residual.

- **No new primitive.** Berkovich = (a point = a multiplicative seminorm = the `×↦·` character/valuation,
  `prime_factorization`/`padic`) + (the spectrum = the space of these readings, `stone_duality`/yoneda)
  + (the tree = the Stern–Brocot/mediant refinement, `continued_fractions`) + (contractible = the `q=+1`
  tree, `reduced_betti_d4_contractible`). It slots entirely into v7.1: `C` = the disk-refinement tree
  (direction/`q=±1` + fold-height carried), `L` = the seminorm `×↦·` character at residue resolution
  with the `base` (radius) slot, `Residue` = the generic/limit points tagged `q=±1` (type-1 reached /
  type-2/3/4 reached-by-none). The interior is unchanged; the only addition is the marker that M(A)'s
  *maximality* sits on the calibrated LLPO/choice boundary.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**The `×↦·` character / multiplicative seminorm (the Berkovich point) — `vp_mul` (PrimeValuation 7/0;
VpMul/VpSeparation):**
- `lean/E213/Lib/Math/NumberTheory/PrimeValuation.lean:96` `vp_mul` — `vp(a·b)=vp(a)+vp(b)`, the `×↦+`
  log of the multiplicative seminorm (PrimeValuation: 7/0 PURE).
- `lean/E213/Meta/Nat/VpMul.lean:165` `vp_mul` (the exponent-lattice engine);
  `lean/E213/Meta/Nat/VpSeparation.lean:172` `vp_separation` (the reading is faithful = the seminorm
  separates points; VpSeparation: 9/0 PURE).

**The valuation read as a p-adic distance / ultrametric (the seminorm's metric) — `Padic/Norm` (21/0):**
- `lean/E213/Lib/Math/NumberSystems/Padic/Norm.lean:461` `Zp.valEq_mul` — valuations add under product
  (`v(xy)=v(x)+v(y)`, the multiplicative seminorm as a metric).
- `:335` `Zp.valEq_add_of_lt` — the ultrametric strong triangle inequality (`|f+g|≤max`).
- `:44` `Zp.valAtLeast_iff_trunc` — valuation depth = truncation-agreement depth (the modulus).

**The spectrum = the space of readings ("object = its readings") — `FlatOntologyClosure` (7/0) +
`IndexedJoin` (8/0):**
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:47` `object1_injective` — an element is
  determined by its readings (faithful = Yoneda/Stone reconstruction = "point = its seminorms").
- `:61` `object1_not_surjective`, `:69` `self_covering_closure` — faithful yet never total = the residue
  (the generic/limit points reached-by-none).
- `lean/E213/Lens/Lattice/IndexedJoin.lean:97` `iProdLens`, `:106` `iProdLens_view` — the
  inverse-limit/meet of a Lens-family (the profinite/Stone spectrum-as-readings object).

**The Berkovich tree = Stern–Brocot / mediant subdivision — `Mediant` (11/0) +
`MinkowskiModularSymbol` (5/0):**
- `lean/E213/Lib/Math/NumberTheory/Mediant.lean:54` `mediant_strictly_between`, `:77`
  `mediant_adjacent_both` (SL₂-unimodularity preserved under mediant = the tree branch rule).
- `lean/E213/Lib/Math/NumberSystems/Real213/Minkowski/MinkowskiModularSymbol.lean:52`
  `manin_unimodular_decomposition` — a unimodular symbol splits into two unimodular children (the tree
  branch).

**Contractibility = the tree being a tree (`q=+1`, no loops) — `BettiKernel` (11/0) +
`NonzeroBetti` (56/0) + `Connectedness` (8/0):**
- `lean/E213/Lib/Math/Cohomology/Examples/BettiKernel.lean:63` `reduced_betti_d4_contractible`
  (`ker δ = im δ`, residue empty = the `q=+1`/exact contractible pole).
- `lean/E213/Lib/Math/Cohomology/Examples/NonzeroBetti.lean:173` `cycle_vs_contractible_qpm`,
  `:134` `loopClass_not_coboundary`, `:111` `betti_one_cycle` (the `q=−1` non-contractible-loop
  contrast, `b₁=1`).
- `lean/E213/Lib/Math/Geometry/Topology/Connectedness.lean:65` `chain_finite` (any two points joined by
  a finite chain = path-connected).

**The `q=±1` residue tag (type-1 reached / type-2/3/4 reached-by-none) — `ResidueTag` (55/0):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:86` `multiplier_unimodular`,
  `:180` `golden_is_converge` (q=+1 converge), `:133` `escape_residue_outside` (q=−1 escape),
  `:160` `converge_residue_fixed`, `:228` `residue_tag_two_poles`.

**The modulus / reached-by-none completion (the analytification residue) — `ContinuedFractionModulus`
(23/0):**
- `lean/E213/Lib/Math/NumberSystems/Real213/ContinuedFraction/ContinuedFractionModulus.lean:203`
  `cf_universal_total_modulus`, `:248` `cfCauchySeq` (every real completes through its CF = the
  reached-by-none limit point as a finite-signature pointing).

**The 2-cell / reading-morphism (each realization factors through the universal reading — analytification
as a Lens) — `Morphism` (3/0):**
- `lean/E213/Lens/Compose/Morphism.lean:37` `view_factors_through_morphism` (every reading factors
  through the universal one — "three outputs of one machine", the analytification's factoring).

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`PrimeValuation` 7/0 · `VpSeparation` 9/0 · `Padic.Norm` 21/0 · `FlatOntologyClosure` 7/0 ·
`IndexedJoin` 8/0 · `Mediant` 11/0 · `MinkowskiModularSymbol` 5/0 · `BettiKernel` 11/0 ·
`NonzeroBetti` 56/0 · `Connectedness` 8/0 · `ResidueTag` 55/0 · `Morphism` 3/0. All PURE, 0 DIRTY.
(`VpMul` cited by name; PrimeValuation's `vp_mul` is the load-bearing copy.)

## Dropped / flagged

- **All named Berkovich objects — PREDICTED-NOT-BUILT (grep-confirmed ABSENT).** No
  `Berkovich`/`seminorm`/`MultiplicativeSeminorm`/`analytic_space`/`analytification`/`rigidSpace`/
  `rigid_analytic`/`BanachRing`/`affinoid` anywhere in `lean/E213/` (zero hits). The decomposition is
  structural; the named field objects are the open targets. Stated, not asserted as built.
- **The completeness / compactness of M(A) — the CALIBRATED BREAK, not built.** "M(A) is the space of
  ALL multiplicative seminorms and is compact Hausdorff" is the maximality reading — the same
  LLPO/choice-strength totalization `stone_duality.md` locates for `Spec(B)` (ultrafilters) and
  `nonstandard_analysis.md` calibrates at LLPO (`RealComparabilityLLPO.comparability_imp_llpo`, cited in
  `SYNTHESIS.md` §5, not re-scanned here). The geometric twin of `padic.md`'s open Ostrowski
  exhaustiveness: instances + tree built, "these are all the points" conceptual. Flagged as a calibrated
  boundary, not a wall.
- **Type-4 points specifically (empty-intersection nested disks) need a `Real213`-cut residue.** The
  reached-by-none limit of a nested-disk family with empty intersection is a value-cut, the same
  `Real213` residual the corpus flags (`SYNTHESIS.md` §5 item 5): irrationality/non-attainment of a
  *value* is not a hole in the *derivation* (CLAUDE.md "Transcendental-as-exterior"). The discrete tree
  is closed; only the value-cut is reached-by-none.
- **Buildable witness (verified anchors, proposed).** No new ∅-axiom lemma is asserted here. The honest
  closeable target, mirroring `padic.md`'s `completion_parametric_in_modulus_base`: a
  `seminorm_is_vp_character` bridge stating the disk-seminorm reading is `vp_mul`'s `×↦·` character at a
  radius-`base` (each side built — `vp_mul` `PrimeValuation.lean:96`, the radius `base` slot
  `padic.md`), and a `berkovich_line_tree_contractible` welding `mediant_adjacent_both` (the tree) to
  `reduced_betti_d4_contractible` (q=+1, no loops). Both are conceptual welds of *built* theorems, not
  new content; named as targets, not claimed.
