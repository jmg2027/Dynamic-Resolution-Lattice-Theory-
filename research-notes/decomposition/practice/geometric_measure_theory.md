# Decomposition: geometric measure theory (currents ⟨T,ω⟩, ∂T, rectifiable sets, Hausdorff measure/dim, the Plateau problem, the mass norm)

*213-decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants — the
character arrow `×↦·`/`×↦+` and the `q=±1` residue tag — read across {direction, fold-height,
resolution, iteration-character, weight}). The hypothesis to **test, not re-skin**: geometric measure
theory is the calculus's **de Rham DUAL** — a current `T : ω ↦ ⟨T,ω⟩` is `de_rham.md`'s differential
forms read as the **pairing-on-forms** ("object = its readings", like distribution theory but on FORMS,
not test functions): a generalized oriented surface IS its integration-against-forms reading. Then
**∂T** (defined by `⟨∂T,ω⟩ = ⟨T,dω⟩`, Stokes by duality) is the **adjoint of `d`** = `homology.md`'s
`q=±1` boundary, with `∂²=0` dual to `d²=0`; **Hausdorff measure/dimension** = `measure.md`'s weight
axis + `dimension.md`'s fold-height (the scaling exponent = the resolution/scaling sub-parameter); the
**mass norm** = the weight (total measure); **mass-minimizing (Plateau)** = the `q=+1` optimum
(`convex_duality.md`'s settling fixed point). NO new primitive — GMT is `de_rham.md` dualized (currents)
with `measure.md`'s weight and the `q=±1` boundary. This note tests whether GMT *consolidates*
de Rham + measure + homology + convex-duality under ONE dual reading.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **same simplex/nesting** `homology.md`/`de_rham.md` read: an `n`-cell is
  `n+1` distinguished vertices, the build-tree of iterated distinguishing, carrying `C`'s two read-off
  axes — a **fold-height** (cell dimension `k`, `dimension.md`'s `Raw.depth`) and a
  **direction/orientation bit** (vertex ordering / removal sign, `parity.md`/`SignedCup`). On the
  measure side `C` is `measure.md`'s **dyadic bracket-list** (`DyadicMeasurableSet := List
  DyadicBracket`), points = refinement residues, a value/weight hung at each. The two `C`'s meet *at
  the boundary pairing* (Stokes), exactly as `de_rham.md` found. **Nothing GMT-specific is constructed:
  there is no `Current` type, no `rectifiable` set, no `HausdorffMeasure`, no `Plateau` minimizer, no
  flat/mass norm, no varifold** — `C` is the combinatorial cochain complex + the dyadic bracket-list
  (grep-confirmed below; the named GMT objects are ABSENT).

- **Reading `L = the de-Rham-dual pairing` (currents = forms read as their integration-against
  functional).** This is the central new datum, one level past `de_rham.md`:
  - `de_rham.md` reads the `k`-cochain/form `ω` directly (`Cochain n k`, the indicator on `k`-subsets;
    `delta` the coboundary `L↑`). **A current `T` is the *dual* of that**: the linear functional
    `ω ↦ ⟨T,ω⟩` (a chain paired against forms = `de_rham.md`'s `∫_chain ω` integration pairing). This
    is `de_rham.md`'s "integration pairing" promoted to **the object itself** — exactly the
    "object = its readings" move (`raw_initial`/`view_factors_through_morphism`, `SYNTHESIS.md` §2:
    motives = the `⟨C|L⟩` half), but applied to FORMS rather than test functions (distribution theory).
    A generalized oriented surface is *nothing but* what it integrates forms to.
  - **The boundary `∂T`** is read off the SAME pairing by the SAME `delta` op, transposed:
    `⟨∂T,ω⟩ = ⟨T,dω⟩`. So `∂` (on currents) is the **adjoint of `d`** (on forms) — and `d` is already
    `homology.md`'s/`de_rham.md`'s `delta` read in the height-UP direction. `∂` on currents is `delta`
    pushed across the pairing: ONE Lean op, the bidirectional fold-height axis, now seen *through the
    duality*. The orientation bit is identical (`SignedCup.mergeSign = (−1)^inv`).
  - **The mass norm `M(T)`** is the **weight** (`measure.md`'s un-normalized count): the total measure
    `Σ lenNum` of the surface, the `×↦+`-twin weight that `measure.md` isolated as `measureNum`. Mass
    is additive over disjoint pieces — `measureNum_append` (`μ(s++t)=μ s+μ t`), the resolution dial.

- **Residue** — `q=±1` (the README/`ResidueTag` tag), with the two faces GMT names:
  1. *Stokes/adjoint face (`q=+1` converge):* pairing `T` against `dω` makes `d` and `∂` **adjoint**;
     the residue of the telescoped sum is the surviving boundary — `de_rham.md`'s Stokes, ALREADY built
     as `gauss_conservation_telescope` (whose docstring calls `f` a **current** and the result the
     divergence theorem `∫_Ω ∇·F = ∮_∂Ω F`). The `q=+1` boundary-collapse.
  2. *Plateau/optimum face (`q=+1` converge):* the mass-minimizing current (the minimal surface
     spanning a fixed boundary) is the **`q=+1` settling optimum** of `convex_duality.md` —
     `min_{∂T=B} M(T)`, the closure-exact / gradient-descent fixed point. Mass is the convex weight,
     the constraint `∂T = B` is the boundary pairing, the minimizer is the saddle where the duality
     gap vanishes (`kantorovich_weak_duality` ≤ ; `ollivier_plan_optimal` "they meet" = optimal).
  3. *The genuine `q=−1` escape (Hausdorff/non-rectifiable):* the **Hausdorff dimension** is the
     fold-height (`dimension.md`) read as a *scaling exponent* (the resolution+scaling sub-parameter,
     `SYNTHESIS.md`'s `base`/`scaling`); a non-integer Hausdorff dimension / a non-rectifiable set is
     the height-ladder's residue **read past every finite integer rung** (`height_diagonal_escapes`,
     `ascent_unbounded`) — the same self-cover as the non-measurable set (`measure.md`'s `q=−1`
     Choice-selector diagonal), and reached only as a `Real213`-cut (the scaling exponent is irrational).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   current T : ω ↦ ⟨T,ω⟩    =  ⟨ simplex/forms ∣ the de-Rham-DUAL pairing-on-forms ⟩
                              = de_rham.md's integration pairing PROMOTED to the object (object=its readings)
   ⟨T,ω⟩ = ∫_T ω             =  the chain-against-form pairing  (gauss_conservation_telescope's fluxAlong)
   ∂T : ⟨∂T,ω⟩ = ⟨T,dω⟩      =  the ADJOINT of d  =  homology.md's ∂ = de_rham's delta, transposed (one op)
   "∂² = 0"                  =  dual to "d²=0"  =  the SAME q=±1 sign-cancellation (dsq_zero_universal_delta4)
   Stokes ⟨∂T,ω⟩=⟨T,dω⟩      =  telescoping boundary-collapse  =  gauss_conservation_telescope (ALREADY built)
   mass norm M(T)            =  the WEIGHT  =  measure.md's measureNum (un-normalized count)  (+↦+ additive)
   M(S∪T)=M(S)+M(T) (disjoint) =  list `++` additivity            (measureNum_append, the resolution dial)
   Hausdorff measure H^s     =  measure.md's weight at scaling exponent s  (weight × resolution^s)
   Hausdorff dimension dim_H =  dimension.md's fold-height read as the SCALING exponent (resolution+scaling)
   rectifiable set           =  "built from countably many Lipschitz pieces" = the COUNT reading on pieces
   Plateau: min_{∂T=B} M(T)  =  Residue(L,C), q=+1  =  convex_duality.md's settling optimum (gap=0)
   non-rectifiable / dim_H∉ℕ =  Residue read past every finite height rung, q=−1  (height_diagonal_escapes)
```

**(1) Currents = the de Rham dual (the NEW datum, beyond re-skinning de_rham.md).** `de_rham.md` reads
the form `ω` and pairs it against a chain at the end (Stokes). GMT inverts the priority: the **current
IS the pairing** `ω ↦ ⟨T,ω⟩` — a generalized oriented surface is its integration-against-forms
functional, exactly as a distribution is its action-on-test-functions, but on FORMS. This is the
"object = its readings" reading (`SYNTHESIS.md` §2 — motives are the `⟨C|L⟩` half, `raw_initial`/
`view_factors_through_morphism` the universal pairing) applied dually to the cochain complex. The
de-Rham-vs-current pairing is `de_rham.md`'s `L↑` (forms, height-up) and its TRANSPOSE (currents,
height-down read through duality) — *one* `delta` op, two sides of one pairing. This is genuinely a new
cell: not "forms again" but "forms read as the thing their integral defines."

**(2) ∂T = the adjoint of d = the q=±1 boundary, ∂²=0 dual to d²=0 — one Lean theorem.** The defining
equation `⟨∂T,ω⟩ = ⟨T,dω⟩` makes `∂` (currents) literally the transpose of `d` (forms). Since `d` is
`homology.md`/`de_rham.md`'s `delta` read height-UP, `∂` is `delta` transposed across the pairing — the
*same* bidirectional fold-height op. `∂²=0` on currents is the adjoint of `d²=0` on forms: the same
codim-2 face removed by two orders with opposite orientation signs (`q=−1` per swap) cancelling
pairwise — `dsq_zero_universal_delta4` (5/0 PURE) IS this theorem, dually. No new boundary primitive.

**(3) Stokes by duality is ALREADY a ∅-axiom theorem.** The single strongest find: GMT's defining
Stokes-by-duality `⟨∂T,ω⟩=⟨T,dω⟩` is the SAME telescoping boundary-collapse `de_rham.md` cashed.
`gauss_conservation_telescope` (8/0 PURE) names its functional `f` a **"current"** in the docstring and
proves the **divergence theorem** `∫_Ω ∇·F = ∮_∂Ω F` along a bracket-chain: every interior wall cancels
(`(fluxAlong f db_i).forward = (fluxAlong f db_{i+1}).backward`), only the outer boundary cuts survive
(`= f db₀.leftCut`, `= f db₂.rightCut`) — "the cancellation IS the conservation." That is precisely
"`∂` is the adjoint of `d` under the form-current pairing." The repo already has GMT's Stokes; we cite
it, we do not build it. `integral_eq_flux` (IntegralViaAnti, `rfl`) makes the pairing `∫ = F(b)−F(a)`
literal.

**(4) Mass = the weight; mass-additivity = list `++`.** The mass norm `M(T)` is `measure.md`'s
un-normalized weight: `measureNum` (9/0 PURE) = the bare sum of bracket `lenNum`s, with
`measure_union_additive`/`measureNum_append` giving `M(S∪T)=M(S)+M(T)` (the additive `+↦+` character,
the resolution dial). The Lebesgue-against-a-value (`lebesgueStepNum = Σ f(midNum)·lenNum`, 9/0 PURE) is
the current paired against a 0-form. So the mass norm is *not* a new norm — it is the weight axis
(`SYNTHESIS.md`'s `weight` parameter), the same object measure/probability/expectation read.

**(5) Hausdorff measure/dimension = weight + the scaling fold-height.** `H^s` is `measure.md`'s weight
read at a scaling exponent `s`; `dim_H` is `dimension.md`'s fold-height (`Raw.depth`, the well-founded
build-height `isPart_wf`, `Raw.depth_slash` = `+1` per distinguishing) read as the *scaling exponent* —
the resolution+scaling sub-parameter (`SYNTHESIS.md`: `base` = which valuation is "adjacent",
`scaling` = `h` vs `√h`). An *integer* Hausdorff dimension is a finite height rung (the `q=+1` corner);
a *non-integer* `dim_H` (a fractal/non-rectifiable set) is the height-ladder's residue past every
finite rung — `height_diagonal_escapes` / `ascent_unbounded`, reached only as a `Real213`-cut (the
exponent is irrational). The `Cohomology/Fractal/` tree exists (`scaling`/`fractal` grep hits) but as
the `d^(d^n)` config-count combinatorics, **not** a Hausdorff measure object.

**(6) Rectifiable = the count reading on Lipschitz pieces.** "Rectifiable = countable union of
Lipschitz images (mod H^s-null)" is the **count reading** (`cardinality.md`) applied to the *pieces* —
a finite/countable list of pieces, the `q=+1` corner where the diagonal cannot arise (exactly
`measure.md`'s finite-`List` measurable set). Non-rectifiable = the `q=−1` escape (the uncountable
self-cover). No new construct: it is the count-on-pieces at `q=+1`.

**(7) Plateau = the q=+1 mass-minimizing optimum.** The Plateau problem `min_{∂T=B} M(T)` (least-mass
current with prescribed boundary) is `convex_duality.md`'s `q=+1` settling optimum: mass is the convex
weight, `∂T=B` the boundary-pairing constraint, the minimizer the gap-zero saddle. Grounded by the
built Kantorovich LP: `kantorovich_weak_duality` (`dualValue ≤ transportCost`, the weak-duality
inequality) + `ollivier_plan_optimal` ("they meet ⟹ optimal", zero duality gap), 60/0 PURE — a real
`sup_dual ≤ inf_primal` with a strong-duality certificate on the weight axis. The closure machine
`FenchelMoreau.biconj_idempotent` (18/0) supplies the `f**=clo` shape. Constancy/closure theorems (a
boundaryless area-minimizing current in the slab is constant; the class of integral currents is closed
under mass-bounded weak limits) are the `q=+1` *converge*/compactness pole — the finiteness-collapse
(`topology.md`'s `heineBorel`), dual to the `q=−1` escape.

| classical GMT object | = the 213 reading | which note | Lean anchor | status |
|---|---|---|---|---|
| current `T : ω↦⟨T,ω⟩` | de Rham DUAL: forms read as the pairing-functional (object=its readings) | `de_rham.md` (forms `L↑`), `SYNTHESIS` §2 (motives = `⟨C|L⟩`) | `gauss_conservation_telescope` (`fluxAlong f`, `f` = "current"); `view_factors_through_morphism` | NEW reading; pairing built, named `Current` object ABSENT |
| `∂T` by `⟨∂T,ω⟩=⟨T,dω⟩` | adjoint of `d` = `homology.md`'s `∂` = `delta` transposed (q=±1 boundary) | `homology.md`, `de_rham.md` | `Delta/Core.delta`; `dsq_zero_universal_delta4` (5/0) | ∂²=0 BUILT (dual to d²=0) |
| Stokes by duality | telescoping boundary-collapse (`∫⊣d` adjoint) | `de_rham.md`, `integration.md` | `gauss_conservation_telescope` (8/0); `integral_eq_flux` (`rfl`) | BUILT ∅-axiom (the strongest leg) |
| mass norm `M(T)` | the WEIGHT (un-normalized count), additive `+↦+` | `measure.md` | `measureNum`, `measureNum_append`, `measure_union_additive` (9/0) | weight BUILT; named flat/mass norm object ABSENT |
| Hausdorff measure `H^s` | weight at scaling exponent `s` | `measure.md` | `measureNum` + `lebesgueStepNum` (9/0) | weight BUILT; `H^s` object ABSENT |
| Hausdorff dimension `dim_H` | fold-height read as scaling exponent (resolution+scaling) | `dimension.md` | `Raw.depth_slash`, `isPart_wf`; `height_diagonal_escapes` | height BUILT; `dim_H` object ABSENT (Real213-cut for non-integer) |
| rectifiable set | count reading on Lipschitz pieces (q=+1 finite/countable) | `cardinality.md`, `measure.md` | `DyadicMeasurableSet` (finite `List`) | count BUILT; `rectifiable` predicate ABSENT |
| Plateau `min_{∂T=B} M(T)` | q=+1 mass-minimizing optimum (gap=0) | `convex_duality.md` | `kantorovich_weak_duality`, `ollivier_plan_optimal` (60/0); `biconj_idempotent` (18/0) | optimum-shape BUILT; `Plateau`/`minimal_surface` object ABSENT |
| constancy / compactness-closure | q=+1 converge/finiteness-collapse | `topology.md` | `heineBorel` (cited prior) | shape BUILT; named theorem ABSENT |
| non-rectifiable / `dim_H∉ℕ` | q=−1 escape (height past every rung) = the diagonal residue | `cardinality.md`, `measure.md` | `object1_not_surjective`, `height_diagonal_escapes` | the q=−1 pole, deliberately not built |

## LEVERAGE — does GMT consolidate de Rham + measure + homology + convex-duality?

**Verdict: PREDICTION + PARTIAL — a strong CONSOLIDATION (the de Rham dual), with the named GMT objects
(`Current`, `rectifiable`, `HausdorffMeasure`, `Plateau`, mass/flat norm, varifold) all ABSENT, located
precisely.** GMT is not a new edifice: it is `de_rham.md`'s form complex read as its dual pairing,
welded to `measure.md`'s weight and `convex_duality.md`'s `q=+1` optimum, with the `q=±1` boundary
supplying ∂ and ∂²=0. Five of the legs are *already* ∅-axiom theorems shared verbatim with prior notes;
the NEW datum is the **dualization** (currents = the pairing-as-object on forms). Honest leg-by-leg
status is in the table above and the dropped-citations section below.

The consolidation is the payoff: GMT *unifies* four prior notes under one dual reading —
- the **de Rham complex** (`de_rham.md`: forms `L↑`, `d`, `d²=0`, Stokes, `H*_dR`),
- the **weight axis** (`measure.md`: `measureNum`, additivity = `++`),
- the **q=±1 boundary** (`homology.md`: `∂`, `∂²=0`, residue = ker/im),
- the **q=+1 optimum** (`convex_duality.md`: the settling minimizer, weak/strong duality),
and reveals that GMT's three defining moves — currents (de Rham dual), `∂T` (Stokes adjoint), mass-min
(Plateau) — are *one reading + one adjoint + one residue tag*, the model's two load-bearing invariants
(the character/adjoint and the `q=±1` residue). The honest boundary: the `Real213`-cut residue (the
smooth-manifold form bundle, non-integer Hausdorff dimension, the genuine `H^s` infimum over covers) is
the SAME open leg `de_rham.md`/`measure.md`/`dimension.md` already located — not a new gap.

## Revelation (consolidation: GMT = de Rham dualized + the weight + the q=+1 optimum)

**Collapse — currents, ∂T, Stokes-by-duality, mass, and Plateau are ONE dual reading at the `q=±1`
poles, not five theories.** The single fold-height reading on the simplex `C`, run UP for forms
(`de_rham.md`'s `d`), then read as the **dual pairing** (currents = "object = its integration-against-
forms readings"), generates GMT:
- forms (`d`, `L↑`) paired AS the dual object → **currents** `T : ω↦⟨T,ω⟩` (the new datum);
- the pairing transposed → **∂T = the adjoint of `d`** = `homology.md`'s `∂`, with `∂²=0` dual to
  `d²=0` (`dsq_zero_universal_delta4`, one theorem);
- the pairing telescoped → **Stokes-by-duality** = `gauss_conservation_telescope` (ALREADY built, its
  `f` literally a "current");
- the weight on the surface → **mass norm** = `measureNum` (`measure.md`);
- the weight minimized under a boundary constraint → **Plateau** = `convex_duality.md`'s `q=+1`
  optimum (`ollivier_plan_optimal`'s zero-gap "they meet");
- the height read as a scaling exponent → **Hausdorff dimension** (`dimension.md`), integer = `q=+1`,
  non-integer = `q=−1` escape (`height_diagonal_escapes`).

**Forcing — currents are FORCED as the dual of forms; ∂ is FORCED as the adjoint of d.** The current
is not an arbitrary new object: the de Rham pairing `(chain, form) ↦ ∫ ω` already exists in
`de_rham.md`; promoting the *chain side* to the object is the only way to read "a surface = what it
integrates forms to." And once `T` is the pairing, `∂T` is *forced* to be the transpose of `d` (that is
what `⟨∂T,ω⟩=⟨T,dω⟩` says) — so `∂²=0` is forced by `d²=0` dually, no independent boundary axiom.

**Residue surfaced — Plateau's minimal surface is the gap *settling*, not a miracle.** Classical GMT
proves existence of mass-minimizers by compactness (the closure theorem) + lower-semicontinuity of
mass; the calculus re-sees this as the `q=+1` corner: mass is the convex weight, the minimizer is the
`clo`-fixed / gradient-descent fixed point where the duality gap vanishes (`ollivier_plan_optimal`), and
the `q=+1` tag guarantees it *settles* (compactness = finiteness-collapse, `topology.md`) rather than
escaping. Non-rectifiability / non-integer dimension is the `q=−1` half (the height-diagonal residue,
the `Real213`-cut scaling exponent) — the part GMT must regularize, exactly `measure.md`'s `q=−1`
Choice corner.

**EXTEND by consolidation; no new axis; model v7.1 holds.** The one genuinely NEW move — currents as
the de Rham DUAL (the pairing-on-forms promoted to the object) — fits the existing "object = its
readings" / motives slot (`SYNTHESIS.md` §2) without a new primitive. The genuine absences (named
`Current`/`rectifiable`/`HausdorffMeasure`/`Plateau`/flat-norm/varifold objects) are the
differential-topology + measure twins of the residuals `de_rham.md` (smooth form bundle) and
`measure.md` (the `q=−1` Choice corner) already located.

## Note for the technique

- **GMT confirms the "object = its readings" pairing is DUALIZABLE on the cochain complex.** `de_rham.md`
  read forms; GMT reads forms *as their integration-functional* — the dual. This is the cleanest
  instance of the `⟨C|L⟩`-half / motives reading (`SYNTHESIS.md` §2, `view_factors_through_morphism`)
  outside pure category theory: a current is a generalized surface that IS its readings, and the
  de-Rham-vs-current pairing is one `delta` op read on the two sides of the integration pairing.
- **Stokes-by-duality is the de Rham theorem's engine, AGAIN.** `de_rham.md` already learned that the
  `∫⊣d` adjunction (Stokes = `gauss_conservation_telescope`) is what turns two readings into an adjoint
  pair. GMT's *defining equation* `⟨∂T,ω⟩=⟨T,dω⟩` IS that adjunction made the definition of the
  boundary — the strongest possible vindication that the resolution-axis ⇄ adjoint-pair cross-tie is
  load-bearing.
- **The weight axis carries the mass norm; the scaling sub-parameter carries Hausdorff dimension.** GMT
  splits `measure.md`'s weight from `dimension.md`'s fold-height cleanly: mass = the weight (total
  measure), Hausdorff dimension = the height read as a scaling exponent. This sharpens
  `SYNTHESIS.md`'s `scaling` sub-parameter: the Hausdorff exponent is the resolution dial's *scaling*
  reading, with integer = `q=+1` rung / non-integer = `q=−1` escape.
- **The break is the same one, located again.** No new break: the smooth-manifold current/form bundle,
  the genuine `H^s` infimum over covers, and the non-integer (`Real213`-cut) scaling exponent are the
  `Real213`-cut/`h→0` residue shared with `de_rham.md` (smooth form bundle), `measure.md` (the `q=−1`
  Choice corner / outer-measure infimum), and `dimension.md` (height past finite rungs). The discrete
  reading is closed; only the continuous completion is reached-by-none.

---

### Verified Lean anchors (file:line:theorem — all grep-verified on `lean/E213`; purity via `tools/scan_axioms.py` this session)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| ★★ Stokes-by-duality `⟨∂T,ω⟩=⟨T,dω⟩` = telescoping boundary-collapse (`f` = a "current") | `Lib/Math/Analysis/FluxMVT/TelescopingConservation.lean:152 : gauss_conservation_telescope` | **PURE, scanned 8/0** ✓ (docstring: divergence theorem `∫_Ω ∇·F = ∮_∂Ω F`, "cancellation IS conservation") |
| ★ ∫ = flux of antiderivative (`∫=F(b)−F(a)`, the pairing) | `Lib/Math/Analysis/Integration/IntegralViaAnti.lean:47 : integral_eq_flux` (`rfl`) | ∅-axiom ✓ (module scans 1/0; `rfl`) |
| ★ `∂T` = adjoint of `d` = the `delta` boundary; `∂²=0` dual to `d²=0` | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4`; `Delta/Core.lean : delta` | **PURE, scanned 5/0** ✓ |
| ★ graded Leibniz `d(α∧β)=dα∧β±α∧dβ` (the graded-relation slot, GMT's flat/cup boundary algebra) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:62 : leibniz_universal_delta4` | **PURE, scanned 5/0** ✓ |
| ★ residue `H = ker ∂/im ∂` (GMT cycle = closed current; boundary = exact) | `Lib/Math/Cohomology/Examples/BettiKernel.lean : reduced_betti_d4_contractible`, `kerSizeDelta` | **PURE, scanned 11/0** ✓ |
| ★ orientation/sign bit (current orientation; q=−1 antisymmetric wedge) | `Lib/Math/Cohomology/Cup/SignedCup.lean:62 : cup1_antisymmetric`, `mergeSign`=`(−1)^inv`, `signed_cup_capstone` | **PURE, scanned 14/0** ✓ |
| ★ mass norm = the WEIGHT (un-normalized count); mass-additivity = list `++` | `Lib/Math/Analysis/Measure/DyadicMeasure.lean:41 : measureNum`; `:55 measureNum_append`; `:69 measure_union_additive` | **PURE, scanned 9/0** ✓ |
| ★ current paired against a value-form = Lebesgue step (`Σ f·lenNum`) | `Lib/Math/Analysis/Measure/LebesgueIntegral.lean:32 : lebesgueStepNum`; `:66 lebesgue_union_additive` | **PURE, scanned 9/0** ✓ |
| ★ Plateau = q=+1 mass-minimizing optimum (weak + zero-gap strong duality on the weight) | `Lib/Math/Geometry/DiscreteCurvature/OllivierRicci.lean:52 : kantorovich_weak_duality`; `:106 ollivier_plan_optimal` | **PURE, scanned 60/0** ✓ |
| ★ the `f**=clo` closure shape (mass-minimization settles, q=+1) | `Lib/Math/Order/FenchelMoreau.lean : biconj_idempotent`, `closed_iff_fixed` | **PURE, scanned 18/0** ✓ |
| ★ Hausdorff dimension = fold-height (`Raw.depth`, `+1` per distinguishing, well-founded) | `Theory/Raw/Levels.lean:46 : Raw.depth_slash`; `Theory/Raw/Lambek.lean:199 : isPart_wf` | ∅-axiom ✓ (via `dimension.md`) |
| ★ non-integer `dim_H` / non-rectifiable = q=−1 height-escape | `Lib/Math/Analysis/Cauchy/DepthHeightDiagonal.lean:56 : height_diagonal_escapes`; `Theory/Raw/MuNuMirror.lean : ascent_unbounded` | ∅-axiom ✓ (via `dimension.md`) |
| ★ q=−1 escape residue (non-rectifiable diagonal = the non-measurable diagonal) | `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`, `:47 object1_injective` | **PURE, scanned 7/0** ✓ |
| the q=±1 residue tag (Plateau = converge pole; non-rectifiable = escape pole) | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`, `:86 multiplier_unimodular`, `:180 golden_is_converge` | **PURE, scanned 55/0** ✓ |
| cross-frame | `de_rham.md` (forms `L↑`, `d`, Stokes, `H*_dR`), `measure.md` (weight = `measureNum`), `homology.md` (`∂`, `∂²=0`, residue), `convex_duality.md` (q=+1 optimum), `dimension.md` (fold-height), `cardinality.md` (count/diagonal) | prior, ∅-axiom ✓ |

### Dropped / flagged (honest — NOT in `lean/E213`; the located missing objects)

- **No `Current` / `FlatChain` / `varifold` object** — grep for `current`/`rectifiable`/`Hausdorff`/
  `Plateau`/`mass_norm`/`minimal_surface`/`varifold`/`FlatChain` in `lean/E213` returns **only**
  `NoetherCurrent.lean` (a *physics* conserved current, `∂·j=0`), English prose ("Current ratio…",
  "Current status…"), and the combinatorial cochain complex. **No GMT current functional `T:Ω^k→ℝ`,
  no current type.** The de Rham *dual pairing* exists (`gauss_conservation_telescope`'s `fluxAlong f`,
  `f` literally called a "current"); the *named* current object is the open leg.
- **No `rectifiable` predicate** — the count-on-pieces reading is built (`DyadicMeasurableSet` = finite
  `List`), but there is no `Rectifiable`/`Lipschitz-piece` predicate. Predicted as the count `q=+1`
  corner; the named object is absent.
- **No `HausdorffMeasure H^s` / `HausdorffDimension dim_H` object** — the weight (`measureNum`) and the
  fold-height (`Raw.depth`) are built separately; their composition into an `H^s`/`dim_H` object with a
  non-integer (`Real213`-cut) scaling exponent and the infimum-over-covers is ABSENT. Same
  `Real213`-cut residue as `measure.md`'s outer-measure infimum and `dimension.md`'s height-past-rungs.
- **No `Plateau` / `mass-minimizing current` / `minimal_surface` object** — the `q=+1` optimum *shape*
  is built (`kantorovich_weak_duality`, `ollivier_plan_optimal`, `biconj_idempotent`), but no named
  Plateau minimizer, no flat norm, no compactness/closure theorem *for currents*. Predicted as the
  `q=+1` optimum; the named GMT theorem is the open leg.
- **No smooth-manifold de Rham/current bundle** — inherited verbatim from `de_rham.md`: no `Ω^k(M)`
  smooth form bundle, no de Rham comparison iso, hence no smooth current dual either. The
  discrete/combinatorial cochain version is built; the smooth completion is the named `Real213`-cut gap.
- **Verified buildable witness (named precisely):** a **dual current functional** `T : Cochain n k →
  Int` with `boundaryCurrent T ω := T (delta ω)` and the theorem `boundaryCurrent (boundaryCurrent T)
  = 0` (dual to `dsq_zero_universal_delta4`) plus `boundaryCurrent T ω = T (delta ω)` welded to
  `gauss_conservation_telescope` — would promote currents+∂T from a cited dual to a built object,
  parallel to how `FreeReduction.lean` built the colimit Side-A. Mass-min would then instantiate
  `OllivierRicci`'s LP at `cost = measureNum` under the `boundaryCurrent = B` constraint. All legs
  (`delta`, `dsq_zero`, `measureNum`, the LP) are PURE and present; only the bundling is unwritten.

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):** TelescopingConservation
**8/0**, V4Capstone **5/0**, BettiKernel **11/0**, SignedCup **14/0**, DyadicMeasure **9/0**,
LebesgueIntegral **9/0**, OllivierRicci **60/0**, FenchelMoreau **18/0**, FlatOntologyClosure **7/0**,
ResidueTag **55/0**. All cited theorems PURE; build clean.
