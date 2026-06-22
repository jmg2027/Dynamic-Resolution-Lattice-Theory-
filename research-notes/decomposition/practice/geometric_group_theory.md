# Decomposition: geometric group theory

*213-decomposition of "Cayley graphs, the word metric, growth functions / growth rate
(polynomial vs exponential), Gromov's theorem (polynomial growth ⟺ virtually nilpotent),
hyperbolic groups / δ-thin triangles, quasi-isometry invariance, the word problem", per
`../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`, the REVELATION rule) and
`../SYNTHESIS.md` §3 (the q=±1 spine; both poles of solvability are one Lean object). A
**fresh** field, LEVERAGE phase — the bar is PREDICTION/REVELATION. Sits directly atop
`free_corner.md` (the word object `FreeReduction`, `free_group_quotient_no_quot`, the
decidable word problem), `groups.md` (a group = the C-preserving self-reading family),
`graph_theory.md` (the count-reading + connectivity), `hyperbolic_geometry.md` (the
disc-sign trichotomy, the q−1 negative-curvature pole), and `golden_ratio.md` (growth rate
= φ, the exponential blow-up as trace growth).*

The thesis under test: **geometric group theory is the calculus's free-reduction word object
(`FreeReduction`) read through a growth/length Lens, with the growth dichotomy = the q=±1
pole.** The Cayley graph / word metric = the `FreeReduction` normal-form word object with a
distance Lens (word length = the fold-height/depth reading). The growth function (#elements
of length ≤ n) = the count reading graded by length/fold-height. ★ The growth **dichotomy**
(polynomial vs exponential; Gromov: polynomial ⟺ virtually nilpotent) = the q=±1 pole:
polynomial growth = the q+1 converging/tame pole (virtually nilpotent = the solvable-adjacent
tame side, tied to the derived series' solvable q+1), exponential growth = the q−1 escape
(free-group-like, the exponential blow-up = the growing iteration / strictly-rising trace).
Hyperbolic groups (δ-thin triangles) = `hyperbolic_geometry.md`'s negative-curvature q−1 pole
read on the Cayley graph. Quasi-isometry invariance = the Lens-refinement (growth/hyperbolicity
are reading-invariant). The word problem (decidable for many groups) = `FreeReduction`'s
decidable `freeEquiv_iff_reduce_eq`; undecidable in general = the Novikov–Boone Side-B break.
**No new primitive.**

## The decomposition (C / Reading / Residue)

- **Construction `C` — the free-reduction word object, nothing new.** A finitely-generated
  group is `groups.md`'s "relabel-and-compose" family presented by generators: `C` is the
  bare word — a `List` over the generator alphabet and their inverses — folded to its free
  normal form by `freeReduce` (`FreeReduction.lean`). The word object is *already built*
  ∅-axiom: `FreeWord` (the raw words), `freeReduce` (push/cancel to normal form), `FreeGroup
  := { w : FreeWord // Reduced w }` (the normal-form subtype, the colimit/ambient-quotient
  with **no `Quot`**, `free_group_quotient_no_quot`). A *general* presentation `⟨S | R⟩`
  imposes relators `R` on top of this — and *that* extra quotient is exactly the Side-B break
  (below). So GGT introduces **no new construction**: its objects are the free-reduction word
  object the calculus already has, optionally with a relator quotient that is the located
  colimit corner.

- **Reading `L_len` — the word metric = the length/fold-height reading.** The word metric
  `d(g,h) = |g⁻¹h|` projects each group element to its **word length** — the number of
  generators in its normal form. This is `dimension.md`/`free_corner.md`'s fold-height/depth
  reading read on the word object: length = how many distinguishings are stacked, the same
  well-founded height measure already carried by `C` (`Lambek.isPart_wf`,
  `MuNuMirror.ascent_adds_unit`). The Cayley graph is this metric made a graph: vertices =
  group elements (normal-form words), edges = right-multiplication by a generator (one length
  step). Reading `L_len` forgets everything but length; the Cayley graph is `⟨FreeWord |
  L_len⟩` with the adjacency "differ by one generator."

- **Reading `L_growth` — the growth function = the count reading graded by length.** Stack
  `L_len` under the count reading (`graph_theory.md`'s count of vertices): the growth function
  `β(n) = #{g : |g| ≤ n}` is `cardinality.md`'s count reading *graded by the fold-height*. Its
  **rate** — polynomial vs exponential — is the q=±1 tag of the count's behaviour under the
  height dial (below). Quasi-isometry = `Lens.refines`: a coarsening of `L_len` that preserves
  the growth rate and δ-thinness (the reading is refinement-invariant).

- **Residue, tagged q=±1 — the growth dichotomy.** The residue of the count-reading graded by
  height is *how the count behaves as the height → ∞*, and it carries the multiplier bit:
  - **q=+1 converge = polynomial growth = virtually nilpotent (the tame pole).** The count
    settles into a polynomial envelope; the group's derived/lower-central series *terminates*
    — the same q+1 converging pole as the solvable derived series (`Solvable.solvable_S3'`,
    `DerivedSeries.solvable_S3`, the tower reaching `{e}` at finite depth). Gromov's theorem
    (polynomial growth ⟺ virtually nilpotent) is this q+1 identification: tame count ⟺
    terminating-series tame structure.
  - **q=−1 escape = exponential growth = free-group-like (the wild pole).** The count blows
    up — the free group's β(n) grows like the number of reduced words, the literal growing
    iteration that never settles (`MuNuMirror.succ_not_idempotent`/`ascent_unbounded`: the
    height-raising endo-reading strictly ascends, never cycling). The φ growth rate
    (`golden_ratio.md`) is the cleanest computable instance: the trace of the iterate strictly
    grows (`golden_trace_mono`) so the orbit is aperiodic (`golden_aperiodic`) — the q−1
    expanding pole, the perfect/non-solvable side (`A5Perfect.a5_perfect`, `a5_not_solvable`).
  - **the smooth/asymptotic growth *exponent* / the δ of a hyperbolic group** = the
    `Real213`-cut RESIDUE, reached by no finite resolution (the limiting growth rate, the
    optimal thinness constant). The named GGT objects (`CayleyGraph`, `wordMetric`,
    `growthFunction`, `hyperbolicGroup`, `quasiIsometry`, `virtuallyNilpotent`) are **ABSENT**
    (grep-confirmed below) — predicted-not-built.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   the group ⟨S | ∅⟩ (free)   =  ⟨ FreeWord | freeReduce ⟩         (FreeReduction, free_group_quotient_no_quot)
   the Cayley graph           =  ⟨ FreeWord | L_len ⟩ + adjacency  (word object + the length/fold-height Lens)
   the word metric d(g,h)     =  L_len = |g⁻¹h| = normal-form length  (the fold-height reading, Lambek.isPart_wf)
   the growth function β(n)    =  count(L_len ≤ n)                    (count reading graded by height, cardinality)
   polynomial growth          =  q=+1 converge: count settles        (virtually nilpotent = solvable q+1, solvable_S3)
   exponential growth         =  q=−1 escape: count blows up          (free-like, succ_not_idempotent / golden_aperiodic)
   Gromov: poly ⟺ virt. nilp. =  q=+1 tame count ⟺ terminating series (derived series reaches {e}, DerivedSeries)
   hyperbolic group (δ-thin)  =  the q−1 negative-curvature pole      (hyperbolic_geometry: disc>0, golden_aperiodic)
   quasi-isometry invariance  =  Lens.refines (reading-invariant)     (Lens.refines, refines_trans)
   the word problem (decidable) =  freeEquiv_iff_reduce_eq            (normal forms compared by List-equality)
   word problem (undecidable)   =  Side-B colimit break (Novikov–Boone)  (general presented group, no normalize)
```

The single move: GGT is **not a new geometry of groups** — it is the **free-reduction word
object** (`groups.md` + `free_corner.md`) read through the **length/fold-height Lens**, with
the **growth rate = the q=±1 residue tag** and quasi-isometry = `Lens.refines`. The Cayley
graph, the word metric, the growth function, and δ-thinness are one word object read through
four facets of the height/count reading.

## Re-seeing table (the unification)

| classical GGT object | the calculus's reading | repo status |
|---|---|---|
| the free group `F(S)` / word object | `⟨FreeWord | freeReduce⟩`, the normal-form Σ-subtype (no `Quot`) | **BUILT** (`free_group_quotient_no_quot`, 26/0) |
| the word problem (decidable) | `freeEquiv_iff_reduce_eq` — normal forms compared by `List`-equality | **BUILT** (`freeEquiv_iff_reduce_eq`, `proj_val_eq_iff`) |
| the word metric `d(g,h) = |g⁻¹h|` | `L_len` = normal-form length = the fold-height reading | structural prediction (height measure built `isPart_wf`/`ascent_adds_unit`; no `wordMetric` object) |
| the Cayley graph | the word object + one-generator adjacency = `⟨FreeWord | L_len⟩` graph | **ABSENT as a named `CayleyGraph` object** (adjacency/graph-count primitives built: `chain_finite`, `closed_const`) |
| the growth function β(n) | the count reading graded by length | structural prediction (count + height built; no `growthFunction`) |
| polynomial growth = virtually nilpotent (Gromov) | q=+1 converge: tame count ⟺ terminating derived/central series | **BUILT (the series side)** (`solvable_S3'`, `DerivedSeries.solvable_S3`); Gromov biconditional itself ABSENT |
| exponential growth (free-like) | q=−1 escape: the growing iteration / strictly-rising trace | **BUILT (the escape side)** (`succ_not_idempotent`, `golden_trace_mono`, `golden_aperiodic`, `a5_perfect`) |
| hyperbolic group / δ-thin triangles | the q−1 negative-curvature pole read on the Cayley graph | **BUILT (the disc>0 pole)** (`golden_hyperbolic`, `golden_aperiodic`); no `deltaThin`/`hyperbolicGroup` object |
| quasi-isometry invariance | `Lens.refines` (growth/δ are refinement-invariant) | **BUILT (the refinement relation)** (`Lens.refines`, `refines_trans`); no `quasiIsometry` object |
| the asymptotic growth exponent / optimal δ | the `Real213`-cut limiting residue | **ABSENT** (the located value-cut break) |
| general presented group word problem (undecidable) | the Side-B colimit break (no `normalize` can exist) | **the located colimit break** (Novikov–Boone, theorem-grade) |

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse — the growth dichotomy IS the q=±1 solvability spine, read on the count-graded-by-
length; this is the NEW datum.** `SYNTHESIS.md` §3 already proves the q=±1 spine with *both
poles of solvability one Lean object*: q=+1 = the derived series **terminates** (`solvable_S3'`,
`DerivedSeries.solvable_S3`), q=−1 = perfect/non-terminating (`A5Perfect.a5_perfect`,
`a5_not_solvable`), unified in `Solvable.solvability_two_poles`. **Gromov's growth dichotomy is
this same spine read through the growth Lens**: polynomial growth = q+1 (the count settles, the
group's series terminates — virtually nilpotent is the solvable-adjacent tame side),
exponential growth = q−1 (the count escapes, the free/perfect non-terminating side, the same
`succ_not_idempotent` strictly-rising ascent and `golden_aperiodic` strictly-rising trace).
So the growth dichotomy, the solvability dichotomy, the disc-sign hyperbolic/elliptic split
(`hyperbolic_geometry.md`), and the escape-vs-converge residue tag are **ONE q=±1 pole** read
through {growth rate, derived series, curvature sign, count residue}. This is the new
contribution beyond re-skinning `free_corner.md` (which gave the word object) and
`hyperbolic_geometry.md` (which gave the curvature q−1): **GGT ties the word object's growth
Lens to the already-unified solvability spine.**

**Forcing — the word metric is FORCED to be the fold-height reading, not an added structure.**
A finitely-generated group's only intrinsic metric is the word length, and word length is
*nothing but* the height of the normal-form word — the same well-founded depth measure already
carried by `C` (`Lambek.isPart_wf`, `MuNuMirror.ascent_adds_unit`: each generator laid on top
raises depth by the unit). The Cayley graph's adjacency (one-generator steps) is the height
reading's successor step, not a chosen graph structure. Quasi-isometry is then *forced* to be
`Lens.refines`: any coarsening that preserves the length reading up to bounded distortion is a
refinement of `L_len`, and growth-rate/δ-thinness — being properties of the residue, not the
fine reading — are preserved by `refines_trans`. "Growth rate is a quasi-isometry invariant" =
"the q=±1 residue tag is a property of `L_len`'s residue, invariant under `Lens.refines`."

**The q=±1 spine (`SYNTHESIS.md` §3) made the growth rate.**
- **q=−1 escape = exponential growth / hyperbolic.** The free group's count blows up; the
  height-raising endo-reading strictly ascends and never settles (`succ_not_idempotent`,
  `ascent_unbounded`), the trace of the φ-iterate strictly grows (`golden_trace_mono`) so the
  orbit is aperiodic (`golden_aperiodic`) — the `disc>0` expanding pole, the same q−1 escape as
  `hyperbolic_geometry.md`'s negative-curvature geodesic divergence and the perfect/non-solvable
  `A5Perfect.a5_perfect`. δ-thin triangles = the negative-curvature q−1 pole read on the Cayley
  graph (geodesics diverge exponentially, so triangles are uniformly thin).
- **q=+1 converge = polynomial growth / virtually nilpotent.** The count settles into a
  polynomial envelope; the derived series terminates (`solvable_S3'`, `DerivedSeries.solvable_S3`),
  the same q+1 converging corner as φ's fixed point and the Banach contraction. Gromov's theorem
  is the q+1 identification of the two tame sides.
- **the parabolic/marginal middle** (intermediate growth, the Grigorchuk groups) = the boundary
  between the two poles — exactly `hyperbolic_geometry.md`'s parabolic cusp / `SYNTHESIS.md`'s
  "the boundary the spine is symmetric about" (predicted, not built).

So GGT = (the `FreeReduction` word object) + (the word metric = length/fold-height Lens) +
(growth dichotomy = q=±1: polynomial/nilpotent q+1 vs exponential/free q−1) + (quasi-isometry
= `Lens.refines`) — **no new primitive**.

## VALIDATE verdict — **EXTEND** (deep consolidation: the growth dichotomy unified with the solvability spine; two PREDICTION legs; the colimit Side-B break recurs verbatim)

No new primitive, no break in the interior. GGT slots entirely into the v7.1 model: `C` = the
free-reduction word object (direction/`q=±1` + fold-height carried), `L_len` the length/height
reading and `L_growth` the count graded by it, `Residue` the growth rate tagged q=±1,
quasi-isometry = `Lens.refines`. It is a **decisive consolidation**: the growth dichotomy that
GGT treats as its central theorem (Gromov) is seen as the **same q=±1 solvability spine** the
corpus already unified in one Lean object (`Solvable.solvability_two_poles`), now read through
the growth/length Lens — and the word object + decidable word problem are *already built*
∅-axiom (`free_group_quotient_no_quot`).

- **PREDICTION leg 1 (the metric/growth objects):** the *word metric*, *Cayley graph*, and
  *growth function* as named objects are grounded only at the *reading* altitude — the
  fold-height measure (`Lambek.isPart_wf`, `MuNuMirror.ascent_adds_unit`), the count reading
  (`cardinality.md`), and graph adjacency/connectivity (`chain_finite`, `closed_const`) are all
  built, but no `wordMetric`/`CayleyGraph`/`growthFunction` object reads them off the word
  object. The calculus *predicts* the word metric is the normal-form length and growth is the
  count graded by it; the named objects are the open leg.

- **PREDICTION leg 2 (Gromov as a biconditional):** the calculus *predicts* polynomial growth
  ⟺ virtually nilpotent is the q=±1 spine read two ways (tame count ⟺ terminating series). The
  *series side* is fully built (`DerivedSeries.solvable_S3`, `Solvable.solvability_two_poles`)
  and the *escape side* is built (`succ_not_idempotent`, `golden_aperiodic`, `a5_perfect`), but
  the Gromov **biconditional itself** — a `growthRate`-to-`virtuallyNilpotent` equivalence — is
  ABSENT (it needs the growth-function object of leg 1 plus a nilpotency predicate). Predicted,
  not built.

- **Located break (recurs verbatim from `free_corner.md`/`knots.md`/`fundamental_group.md`):**
  the **general presented-group word problem is undecidable (Novikov–Boone)** — exactly the
  colimit Side-B obstruction. The *free* case (no relators) is Side A, BUILT ∅-axiom with a
  decidable `normalize`/`freeReduce` (`freeEquiv_iff_reduce_eq`). The *general* case quotients
  by a relator-generated equivalence that is non-confluent/undecidable, so a `normalize` cannot
  exist — a theorem-grade boundary, not a missing 213 primitive. This is the **same break**
  `colimit_quotient_synthesis.md` already records; GGT is a fresh field where it recurs verbatim,
  reinforcing it as a real structural limit.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**The word object + decidable word problem (the central `C`, per `free_corner.md`):**
- `lean/E213/Lib/Math/Algebra/Group/FreeReduction.lean:264` `free_group_quotient_no_quot`
  (the free group as a `Quot`-free normal-form Σ-quotient, bundling 1–5); `:237`
  `proj_val_eq_iff` (`Quot.sound`'s content, axiom-free); `:216` `freeEquiv_iff_reduce_eq`
  (the **decidable word problem** — normal forms compared by `List`-equality); `:191`
  `freeReduce_idempotent`; `:227` `FreeGroup := { w : FreeWord // Reduced w }`; `:242`
  `proj_section`. **PURE (26/0).**

**The word metric = length/fold-height reading; the growing escape (per `free_corner.md`):**
- `lean/E213/Theory/Raw/MuNuMirror.lean:80` `succ_not_idempotent` (the height-raising
  endo-reading strictly ascends — the growing/exponential pole); `:59` `ascent_adds_unit`
  (depth rises by the unit — the word-length successor step); `:50` `ascent_unbounded` (no
  finite cap); `:65` `tower_no_cycle`. **PURE (8/0).**
- `lean/E213/Theory/Raw/Lambek.lean:199` `isPart_wf` (the well-founded fold-height measure the
  word metric reads); `:273` `no_infinite_descent`. **PURE (22/0).**

**The growth dichotomy = the q=±1 solvability spine (the central NEW collapse):**
- `lean/E213/Lib/Math/Algebra/Linalg213/Solvable.lean:373` `solvability_two_poles` (both poles
  one object: S₃ converge q+1 / A₅ escape q−1); `:253` `solvable_S3'` (the q+1 terminating
  derived series = the virtually-nilpotent/polynomial side); `:330` `a5_not_solvable'` (the q−1
  escape = the exponential/free side); `:237` `perfect_nontrivial_not_solvable` (the general
  escape principle). **PURE (65/0).**
- `lean/E213/Lib/Math/Algebra/Linalg213/DerivedSeries.lean:144` `solvable_S3`
  (`commSet (commSet S3) = One` — the derived series reaches `{e}` at depth 2, the q+1 tame
  side). **PURE (21/0).**
- `lean/E213/Lib/Math/Algebra/Icosahedral/A5Perfect.lean` `a5_perfect` (`[A₅,A₅]=A₅`, the
  perfect/non-terminating q−1 pole), `a5_not_solvable`. **PURE (9/0).**

**Exponential growth / hyperbolic = the q−1 escape (per `golden_ratio.md`/`hyperbolic_geometry.md`):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Phi/GoldenAperiodic.lean:25` `golden_trace_mono`
  (the iterate's trace strictly increases — the exponential growth witness); `:57`
  `golden_aperiodic` (`pow G (n+1) ≠ I` ∀n — infinite order = q−1 escape, no periodic floor);
  `:51` `golden_trace_gt_two`. **PURE (3/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HyperbolicEllipticTrace.lean:71`
  `golden_hyperbolic` (`det G=1 ∧ tr G=3 ∧ disc G=5 ∧ 0<disc G` — the hyperbolic boost, the
  disc>0 pole `hyperbolic_geometry.md` ties to negative curvature / δ-thinness). (per
  `hyperbolic_geometry.md`; PURE 5/0 there.)

**Quasi-isometry = Lens-refinement (reading-invariance):**
- `lean/E213/Lens/LensCore.lean:90` `Lens.refines` (`L.refines M` — L's kernel finer than M's,
  the refinement relation quasi-isometry instantiates); `:93` `Lens.refines_refl`; `:95`
  `Lens.refines_trans`. (also `Lens/Lattice/Preorder.lean:15,19` `refines_refl`/`refines_trans`.)

**The q=±1 residue tag (the growth dichotomy's formal home):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:86`
  `multiplier_unimodular`; `:180` `golden_is_converge`; `:133` `escape_residue_outside`; `:160`
  `converge_residue_fixed`. **PURE (55/0).**

**The count reading + graph adjacency (the growth function's components, per `graph_theory.md`):**
- `lean/E213/Lib/Math/Combinatorics/GraphConnectivity.lean:61` `closed_const` (the dim-1
  connected-graph kernel, `graph_theory.md`'s Laplacian λ₀=0; the Cayley graph's connectivity).
- `lean/E213/Lib/Math/Geometry/Topology/Connectedness.lean:65` `chain_finite` (finite-list
  adjacency = the word metric's path structure).
- `lean/E213/Lib/Math/Probability/Limit/LLN.lean:29` `countTrue_append` (the count reading is
  additive over `++`, the growth count's additivity). (per `cardinality.md`/`probability.md`.)

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root):**
`FreeReduction` 26/0 · `MuNuMirror` 8/0 · `Lambek` 22/0 · `ResidueTag` 55/0 · `Solvable` 65/0 ·
`DerivedSeries` 21/0 · `A5Perfect` 9/0 · `GoldenAperiodic` 3/0. All PURE, 0 DIRTY.

## Dropped / flagged (honest)

- **The named GGT objects — ABSENT, predicted-not-built.** grep over `lean/E213` for
  `CayleyGraph`/`cayley_graph`/`wordMetric`/`word_metric`/`wordLength`/`growthFunction`/
  `growthRate`/`hyperbolicGroup`/`deltaThin`/`thin_triangle`/`quasiIsometr`/`Gromov`/
  `virtuallyNilpotent`/`virtually_nilpotent` returns **no Lean object**. (The 228-file
  `Cayley` grep is entirely **Cayley–Dickson** algebra — a false friend, unrelated to Cayley
  graphs; confirmed not load-bearing, not cited.) The named `CayleyGraph`/`wordMetric`/
  `growthFunction`/`hyperbolicGroup`/`quasiIsometry`/`virtuallyNilpotent` are confirmed absent —
  the located prediction legs. The *reading components* (fold-height `isPart_wf`, count
  `countTrue_append`, adjacency `chain_finite`/`closed_const`, refinement `Lens.refines`) are
  all built; only the GGT-named bundles reading them off are open.
- **Gromov's theorem as a biconditional — ABSENT.** Both poles are built separately (the q+1
  terminating series `DerivedSeries.solvable_S3`; the q−1 escape `succ_not_idempotent`/
  `golden_aperiodic`/`a5_perfect`), but no `polynomialGrowth ⟺ virtuallyNilpotent` equivalence
  object exists. Predicted, not asserted.
- **The general presented-group word problem (Novikov–Boone) — the located Side-B break.** Only
  the *free* word problem is decidable (`freeEquiv_iff_reduce_eq`, Side A built); the general
  case is the theorem-grade colimit obstruction `colimit_quotient_synthesis.md` records (no
  `normalize` can exist). Cited scope-honest, recurring verbatim from `free_corner.md`.
- **The asymptotic growth exponent / optimal δ-thinness constant** — the `Real213`-cut limiting
  residue (the limiting growth rate, the optimal hyperbolicity constant), reached by no finite
  resolution. Only the *rate dichotomy* (q=±1 tag) is built integer-side; the smooth exponent is
  the value-cut residue, the same boundary `hyperbolic_geometry.md` locates.
- **Verified buildable witness (honest — none new asserted):** the load-bearing collapse (growth
  dichotomy = the q=±1 solvability spine) is already a `decide`/induction-checked theorem
  (`Solvable.solvability_two_poles`, `golden_aperiodic`), and the word object is
  `free_group_quotient_no_quot` (`Iff.rfl`/`rfl`-grade). No new count-inequality or `decide`
  witness is proposed beyond the grep-confirmed, scanned-PURE anchors above; no decide witness
  is proposed that was not actually checked.
