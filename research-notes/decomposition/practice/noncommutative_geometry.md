# Decomposition: noncommutative geometry (Connes)

*213-decomposition of "the spectral triple `(A, H, D)` = algebra + Hilbert space + Dirac operator;
recovering a manifold from its spectral data; Connes' distance formula
`d(p,q) = sup{ |f(p)−f(q)| : ‖[D,f]‖ ≤ 1 }`; noncommutative tori; cyclic cohomology; the local index
formula; the slogan *geometry = spectrum*", per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the
two invariants — the character arrow `×↦·`/`×↦+` and the `q=±1` residue tag — + the q=±1 spine + the
spectral character + the reflexive "object = its readings").*

This entry sits directly on five neighbors and consolidates them onto **one new datum**:
- `operator_algebras.md` (KEY) — a commutative C*-algebra IS its characters (Gelfand `A ≅ C(σ(A))`);
  the `×↦·` character arrow read on the operator algebra; the `*`-involution = the `q=±1` bit; states
  + GNS = the weight axis. The located break: the Hilbert-space / C*-norm completion is absent.
- `index_theory.md` (JUST DONE) — the local index formula = the analytic index (`ker − coker`, the
  `q=±1` alternating residue count) = the topological index (the `×↦·` curvature character integrated);
  the Dirac operator `D` as the diagonal self-map shape.
- `spectral.md` — the spectrum = the multiset of `q=+1` scale-residues; `det/tr = e₂/e₁`.
- `quantum_mechanics.md` — the operator / Hilbert-space pole; the bracket obstructs a common eigenbasis.
- `hyperbolic_geometry.md` / `curvature.md` — the metric / the loop residue.

**The thesis under test (the NEW datum):** noncommutative geometry is the calculus's
**"geometry = its spectral readings"** — `operator_algebras.md`'s Gelfand (commutative C*-algebra IS
its characters/spectrum) **pushed past commutativity**, with the **Dirac operator `D` the
resolution/metric reading** and the **distance formula reading the metric off the `q=±1` commutator
`[D,f]`** (the *same* antisymmetric bracket as `Mat2Bracket.bracket_antisymm`). Concretely:

- **"geometry = spectrum"** = `operator_algebras.md`'s Gelfand `A ≅ C(σ(A))` (the `×↦·` character
  arrow saying "the commutative algebra is its characters"), with commutativity dropped: a spectral
  triple `(A,H,D)` recovers the geometry from spectral data = the SAME reflexive **"object = its
  readings"** (yoneda / motives / Berkovich, `SYNTHESIS.md` §2 — a space IS its algebra-of-functions
  read spectrally). When `A` is commutative the points come back as characters `χ : A → ℂ`; when `A` is
  noncommutative there are too few characters and the *spectral data* `(A,H,D)` carries the geometry
  instead. **No new primitive** — Gelfand at a wider codomain/index.
- **The Dirac operator `D` = the resolution/metric reading.** `D`'s eigenvalues are an inverse length
  scale (the spectral/resolution axis, `README.md`'s resolution dial via `IsResolutionShift`); `D`
  encodes how finely the algebra resolves the geometry. This is `index_theory.md`'s `D`-as-diagonal
  read one level over: there `D` indexed the residue, here `D` dials the resolution.
- **The distance formula reads the metric off the `q=±1` commutator.**
  `d(p,q) = sup{ |f(p)−f(q)| : ‖[D,f]‖ ≤ 1 }` recovers the geodesic distance from `[D,f]`, the
  commutator of `D` against a function `f`. `[D,f]` is the antisymmetric Lie bracket — the *same*
  `q=−1` pair-swap as `Mat2Bracket.bracket A B = −[B,A]` (`bracket_antisymm`); the metric is read off
  the `q=±1` bracket exactly as `quantum_mechanics.md` reads the uncertainty obstruction off `[X,P]`.
- **The local index formula** = `index_theory.md`'s analytic = topological index in the NC setting
  (the `×↦·` character + the `q=±1` alternating index, `residue_tag_two_poles`).
- **Cyclic cohomology** = the NC de Rham — the residue-taking operation (`homological_algebra.md`) in
  the NC setting: `δ²=0` (`dsq_zero_universal_delta4`) and the graded-relation Leibniz
  (`leibniz_universal_delta4`).
- **NC tori** = the `q`-deformation (`quantum_groups.md`'s deformation-`q`, `qbinom`).

So NCG = ("geometry = spectrum" = Gelfand past commutativity, "object = its readings") + (`D` = the
resolution/metric reading, the distance via the `q=±1` commutator `[D,f]`) + (local index =
`index_theory.md`'s analytic = topological) + (cyclic cohomology = NC de Rham residue) + (NC tori = the
deformation-`q`). **No new primitive** — Gelfand's algebra=spectrum + the Dirac resolution-reading +
the `q=±1` commutator-metric. The genuine residue is the Hilbert-space / C*-norm completion shared with
`operator_algebras.md` / `quantum_mechanics.md`, plus the smooth `Real213`-cut metric.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the same operator `×`-construction as `operator_algebras.md` /
  `spectral.md`, no new build.** A spectral triple's algebra `A` is the operator `×`-construction (in
  the discrete `d=2` shadow, `Mat2` = `HyperbolicEllipticTrace.Mat2`, the directed-count bundle built
  by `mul`, carrying the orientation/swap bit = sign of `det` and fold-height `2`); its multiplication
  IS `representation.md`'s Aut-family composition. **Noncommutativity is not a new primitive** — it is
  the operator product's failure to commute, *already a theorem in-repo*
  (`SternBrocotMarkov.markovGen_noncommutative : mul genL genR ≠ mul genR genL`, `decide`). So the
  passage "commutative C* ⟶ NC C*" is not a new construction; it is the *same* `Mat2`/operator `C`
  read where `mul` does not commute — exactly the regime where the bracket `[A,B] = AB − BA` is
  nonzero (`Mat2Bracket.bracket`). The genuinely new object would be the *Hilbert space `H`* (the
  infinite-resolution completion `D` acts on) — and that, grep-confirmed, is the located absence (below).

- **Reading — four readings of one operator `C`, all already named in the notebook:**
  - **`L_χ` (geometry = spectrum / Gelfand = the `×↦·` character arrow):** for commutative `A`, the
    points are the multiplicative functionals `χ : A → ℂ`, `χ(xy) = χ(x)χ(y)` — exactly
    `operator_algebras.md`'s Gelfand reading, the `×↦·` character (`det2_mul`, `legendre_mul` at the
    scalar / `{±1}` codomain; ℂ-widened for Gelfand). "geometry = spectrum" is "the algebra IS its
    characters" (`representation.md`/`fourier.md`/`SYNTHESIS.md` §2 "object = its readings"). NCG's
    move: when `A` is noncommutative the character set is too small, so the geometry is read off the
    full spectral datum `(A,H,D)` rather than the character space. The reading is unchanged; only
    *which* surplus carries the geometry shifts.
  - **`L_D` (the Dirac operator = the resolution/metric reading):** `D` is the resolution dial made an
    operator — its eigenvalues are an inverse length scale, so reading `A` *against* `D` resolves the
    geometry at finer and finer scales. This is `README.md`'s resolution parameter
    (`IsResolutionShift`, `IsResolutionShift_compose` — grades add under composition, the
    resolution-tower modulus) promoted to the spectral axis. `index_theory.md` read `D` as the
    *diagonal self-map* whose `ker`/`coker` give the index; here the *same* `D` is read as the
    *resolution dial* whose spectrum gives the metric. One operator, two readings (the resolution dial
    vs the residue-indexer) — the corpus's recurring "two readings of one object".
  - **`L_[D,·]` (the distance / the `q=±1` commutator-metric):** the distance formula
    `d(p,q) = sup{ |f(p)−f(q)| : ‖[D,f]‖ ≤ 1 }` reads the metric off `[D,f] = D·f − f·D`, the
    commutator. `[D,f]` is the antisymmetric Lie bracket — the **`q=−1` pair-swap**: `[A,B] = −[B,A]`
    (`Mat2Bracket.bracket_antisymm`), tracelessness `tr[A,B] = 0` (`tr_bracket_zero`, the bracket lands
    in `tr`'s kernel), Jacobi (`jacobi`), Leibniz/derivation `[D, fg] = [D,f]·g + f·[D,g]`
    (`bracket_leibniz` — the *graded-relation* slot, `SYNTHESIS.md`). So `‖[D,f]‖ ≤ 1` is the
    Lipschitz/unit-gradient condition: the bracket `[D,f]` IS the differential `df` (the derivation
    `bracket_leibniz`), and bounding it bounds the metric gradient. The metric is read off the `q=±1`
    bracket — exactly as `quantum_mechanics.md` reads the uncertainty obstruction off `[X,P]` and
    `lie_theory.md` reads the structure off `Mat2Bracket`. The `q=−1` antisymmetry is *what makes
    `[D,f]` a derivation*: the same direction bit that signs `det`, `∂`, ℤ's `−`.
  - **`L_HC` (cyclic cohomology = the NC de Rham residue):** cyclic cohomology is the
    residue-taking operation `Residue(L,C)` of `homological_algebra.md` in the NC setting — the
    homological residue `ker δ / im δ` graded by degree, tagged `q=±1`. The mechanism is built and
    PURE: `δ²=0` (`dsq_zero_universal_delta4`, the orientation bits cancelling pairwise — the same
    `q=±1` sign-propagation), the graded-relation Leibniz `δ(α⌣β)=δα⌣β ⊕ α⌣δβ`
    (`leibniz_universal_delta4`, the cup-product = the cyclic-cocycle pairing's shape), the reduced
    Betti residue (`reduced_betti_d4_contractible`, `ker δ / im δ`). Cyclic cohomology is the NC
    replacement for de Rham `H*_dR` — and de Rham is already named as one *output* of the residue
    machine (`SYNTHESIS.md` §2). No new operation; the NC de Rham complex is the residue machine on
    the (noncommutative) algebra.

- **Residue — the `q=±1` tag, plus the located completion residue.**
  - The spectral triple's *positivity / self-adjointness* select the `q=+1` corner exactly as
    `operator_algebras.md`: `D` self-adjoint ⟹ real spectrum (`disc_symmetric_nonneg`, the `q=+1`
    converge pole), the index obstruction (`coker D ≠ 0`) the `q=−1` escape
    (`object1_not_surjective`/`escape_residue_outside`).
  - The genuine residue is the **Hilbert space `H` / C*-norm completion at infinite resolution** —
    the `Real213`/ℂ + completeness object the analysis cluster repeatedly locates as absent
    (`operator_algebras.md`'s `‖x*x‖=‖x‖²`, `quantum_mechanics.md`'s `⟨ψ|φ⟩`, `measure.md`'s `Lp`),
    grep-confirmed un-built. The Dirac operator `D` as a genuine unbounded self-adjoint operator on a
    Hilbert space, the operator norm `‖[D,f]‖`, and the `sup` in the distance formula all sit on this
    completion — predicted-not-built. Plus the smooth `Real213`-cut metric (`curvature.md`'s open leg).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   the algebra A of a spectral triple   =  ⟨ operator ×-construction (Mat2 where mul ≠ comm) | the spectral readings ⟩   (markovGen_noncommutative)
   commutative case: a point             =  a character χ:A→ℂ, χ(xy)=χ(x)χ(y) = the ×↦· arrow (Gelfand)                 (det2_mul, legendre_mul)
   "geometry = spectrum"                 =  operator_algebras.md's Gelfand "the algebra IS its characters", past commutativity   (SYNTHESIS §2 object=readings)
   the Dirac operator D                  =  the resolution/metric reading (eigenvalues = inverse length; the resolution dial)    (IsResolutionShift, IsResolutionShift_compose)
   [D,f] = D·f − f·D                     =  the q=−1 antisymmetric bracket; [A,B]=−[B,A]; tr[A,B]=0                            (bracket_antisymm, tr_bracket_zero)
   [D,fg] = [D,f]·g + f·[D,g]            =  the bracket is a derivation = df (the graded-relation Leibniz slot)               (bracket_leibniz, leibniz_universal_delta4)
   d(p,q)=sup{|f(p)−f(q)|:‖[D,f]‖≤1}     =  the metric READ OFF the q=±1 commutator [D,f] (‖df‖≤1 = unit gradient)            (Mat2Bracket; RESIDUE: ‖·‖ completion)
   self-adjoint D ⟹ real spectrum        =  the q=+1 converge pole (the C*-axiom shadow)                                       (disc_symmetric_nonneg)
   cyclic cohomology HC*                 =  the NC de Rham residue = ker δ/im δ graded, tagged q=±1                            (dsq_zero_universal_delta4, reduced_betti_d4_contractible)
   the local index formula               =  index_theory.md's analytic (ker−coker) = topological (×↦· char) in the NC setting (residue_tag_two_poles, det2_mul)
   the NC torus A_θ                       =  the deformation-q twist of the commutative torus (quantum_groups' q)             (qbinom; qbinom_q1 = θ→0 commutative)
   the Hilbert space H / ‖[D,f]‖ / the sup =  the completion residue (RESIDUE — un-built)                                      (no Hilbert/inner-product; LOCATED BREAK)
```

| reading | what it does to the operator `C` | invariant / pole | built anchor |
|---|---|---|---|
| `L_χ` Gelfand / geometry=spectrum | the `×↦·` multiplicative functional ("algebra IS its characters") | character arrow | `det2_mul`, `legendre_mul` |
| `L_D` Dirac = resolution/metric | the resolution dial as an operator (eigenvalues = inverse length) | resolution axis | `IsResolutionShift_compose` |
| `L_[D,·]` distance / commutator-metric | reads the metric off `[D,f]` (the bracket = `df`) | direction `q=−1` | `bracket_antisymm`, `tr_bracket_zero`, `bracket_leibniz` |
| `L_HC` cyclic cohomology = NC de Rham | the residue `ker δ/im δ` graded, `δ²=0` | residue `q=±1` | `dsq_zero_universal_delta4`, `reduced_betti_d4_contractible` |
| `L_idx` local index formula | analytic (`ker−coker`) = topological (`×↦·` char) | `q=±1` count + char | `residue_tag_two_poles`, `det2_mul` |
| NC torus = deformation-`q` | the `q`-twist of the commutative torus | (the OTHER `q`) | `qbinom`, `qbinom_q1` |
| `H` / `‖[D,f]‖` / the `sup` | the Hilbert-space / norm completion | **RESIDUE** | un-built (no Hilbert space) |

## Revelation (collapse + forcing + spine)

**★ Collapse (the NEW datum) — "geometry = spectrum" IS Gelfand pushed past commutativity, and the
distance formula reads the metric off the `q=±1` bracket.** The load-bearing distinction from the
neighbors is twofold, and neither re-skins `operator_algebras.md` or `index_theory.md`:

1. **Gelfand past commutativity.** `operator_algebras.md` proved the *commutative* case: a commutative
   C*-algebra IS its characters (`A ≅ C(σ(A))`, the `×↦·` arrow's image), the eighth field of the
   character arrow. Connes' "geometry = spectrum" is *that same Gelfand reading carried past
   commutativity*: a spectral triple `(A,H,D)` recovers the geometry from spectral data even when `A`
   has too few characters to be `C(X)`. The calculus reads this exactly — it is the reflexive "object
   = its readings" (`SYNTHESIS.md` §2: yoneda → motives → Tannakian → distribution/current/Berkovich),
   the move that already appears as a theorem in five independent fields, now made on the *operator
   algebra at the noncommutative locus* (`markovGen_noncommutative`). So the character arrow's
   "algebra = spectrum" is not a re-skin of the commutative Gelfand: NCG is the *extension* that says
   the spectral datum carries the geometry where the character space alone cannot. **The character
   arrow's home field gains its widest statement.**

2. **The metric is read off the `q=±1` commutator `[D,f]`.** This is the genuinely new structural
   datum vs `index_theory.md` (which read `D` as the residue-indexing diagonal). Connes' distance
   formula `d(p,q) = sup{ |f(p)−f(q)| : ‖[D,f]‖ ≤ 1 }` recovers the *metric* — not the index — from
   `[D,f]`. And `[D,f]` is the antisymmetric Lie bracket the repo builds PURE
   (`Mat2Bracket.bracket_antisymm`, `[A,B]=−[B,A]`, the `q=−1` pair-swap): the metric is read off the
   *same* bracket as `quantum_mechanics.md`'s uncertainty `[X,P]` and `lie_theory.md`'s structure. The
   bracket is a **derivation** (`bracket_leibniz`, `[D,fg]=[D,f]·g+f·[D,g]`), so `[D,f]` IS the
   differential `df` and `‖[D,f]‖≤1` is the unit-gradient (Lipschitz) condition. **So the
   noncommutative metric = the `q=−1` bracket-derivation read as a gradient bound** — the direction
   bit (`q=±1`) supplying the *differential*, the resolution reading `L_D` supplying the *scale*. The
   metric is built from the calculus's two standing pieces (the `q=±1` bracket + the resolution dial),
   not a new primitive.

**Forcing — the local index formula is `index_theory.md`'s collapse, transported to NC.** Connes'
local index formula equates the analytic index (the `q=±1` alternating `ker − coker` residue count,
`residue_tag_two_poles` signed by `multiplier_unimodular`) with a sum of *cyclic-cohomology* residues
of the `×↦·` character of `D` — the NC replacement for `∫ ch·Td`. This is *forced* as
`index_theory.md`'s "analytic = topological" two-readings collapse, with cyclic cohomology (`L_HC`,
the NC de Rham residue, `dsq_zero_universal_delta4`) standing in for de Rham. No new equality — the
same `det/tr=e_i` / Lefschetz=trace shape, between the NC analytic and NC topological readings.

**Spine — the `q=±1` tag organizes the whole field (`SYNTHESIS.md` §3).** The `[D,f]` bracket is the
`q=−1` antisymmetry pole (`bracket_antisymm`); self-adjoint `D` / positivity select the `q=+1`
converge pole (`disc_symmetric_nonneg`); the index obstruction (`coker D`) is the `q=−1` escape
(`object1_not_surjective`/`escape_residue_outside`), `ker D` the `q=+1` converge
(`converge_residue_fixed`); cyclic cohomology `H^{>0}` is the `q=−1` obstruction residue,
`HC⁰` the `q=+1` exact part. `ResidueTag.residue_tag_two_poles` (55/0) is the formal home;
`golden_is_converge` ties `+1` to the converge pole. **The NC-torus `q` is the OTHER `q`** (the
quantum-groups deformation dial, `qbinom`), distinct from the tag-`q` per `SYNTHESIS.md` §2's
quantum-groups test: `qbinom_q1` (the deformation `q=1` = the ordinary binomial = the commutative
torus `θ→0`) is the deformation dial on the *count*, not the ±1 swap bit on the *residue* — they share
only the ±1 locus by containment.

## VALIDATE — verdict: **EXTEND** (decisive consolidation: Gelfand's "algebra=spectrum" reaches its widest statement; the metric = the `q=±1` bracket; one PREDICTION leg; one located break)

No new primitive, no break in the interior. NCG slots entirely into v7.1: `C` = the operator algebra
read at its noncommutative locus (`markovGen_noncommutative`, no new construction); `L_χ` = Gelfand =
the `×↦·` character ("geometry = spectrum"); `L_D` = the Dirac/resolution dial; `L_[D,·]` = the metric
read off the `q=±1` bracket-derivation; `L_HC` = cyclic cohomology = the NC de Rham residue; the local
index = `index_theory.md`'s analytic=topological collapse transported to NC. It is a **decisive
consolidation**: the character arrow's "algebra = its readings" reaches its widest form (past
commutativity), and the *metric itself* is shown to be built from the `q=±1` bracket + the resolution
dial. Leg by leg:

- **Leg 1 — geometry = spectrum = Gelfand past commutativity. PREDICTION (consolidation).**
  A character `χ(xy)=χ(x)χ(y)` is `det2_mul` (130/0) / `legendre_mul` (5/0) with ℂ codomain;
  "geometry = spectrum" = `operator_algebras.md`/`SYNTHESIS.md` §2 "object = its readings" carried to
  the NC operator algebra (`markovGen_noncommutative` the built noncommutativity). The character
  arrow's widest field; no new work. Honest: the *named* spectral-triple / Gelfand object is absent
  (the structural prediction is the deliverable).

- **Leg 2 — `D` = the resolution/metric reading. PREDICTION, the dial BUILT.**
  The resolution dial is built ∅-axiom (`IsResolutionShift`, `IsResolutionShift_compose` 17/0 — grades
  add under composition, the resolution-tower modulus). `D` = that dial promoted to a spectral
  operator (eigenvalues = inverse length). Honest: the genuine *unbounded self-adjoint `D` on a
  Hilbert space* is the completion residue (below).

- **Leg 3 — the distance formula reads the metric off the `q=±1` commutator `[D,f]`. PREDICTION,
  the bracket BUILT.** `[D,f]` = the antisymmetric bracket: `bracket_antisymm` (`[A,B]=−[B,A]`),
  `tr_bracket_zero` (`tr[A,B]=0`), `jacobi`, and the derivation `bracket_leibniz`
  (`[D,fg]=[D,f]·g+f·[D,g]`) — all PURE (`Mat2Bracket` 10/0). The metric = the `q=−1`
  bracket-derivation (= `df`) bounded in norm (the unit-gradient condition). The genuinely new datum.
  **PARTIAL:** the operator *norm* `‖[D,f]‖` and the `sup` need the Hilbert-space completion (below).

- **Leg 4 — cyclic cohomology = the NC de Rham residue. PREDICTION (consolidation).**
  The residue mechanism is built and PURE: `δ²=0` (`dsq_zero_universal_delta4`), the graded-relation
  Leibniz (`leibniz_universal_delta4`), the reduced Betti residue `ker δ/im δ`
  (`reduced_betti_d4_contractible` 11/0). Cyclic cohomology = `homological_algebra.md`'s residue
  operation on the noncommutative algebra, the NC replacement for de Rham. Honest: the *named* cyclic
  complex / `HC*` / Connes' `B`,`b` operators are absent.

- **Leg 5 — the local index formula = `index_theory.md`'s analytic=topological. EXTEND
  (consolidation).** The `q=±1` alternating `ker−coker` count (`residue_tag_two_poles`,
  `multiplier_unimodular`) = the `×↦·` character of `D` paired with cyclic cohomology — the same
  two-readings collapse as `index_theory.md`, in the NC setting. The discrete shadow (Gauss–Bonnet,
  the alternating Euler count) is closed ∅-axiom per `index_theory.md`; the smooth NC local index
  formula is the inherited residue.

- **Leg 6 — NC tori = the deformation-`q`. EXTEND (consolidation).** The NC torus `A_θ` is the
  `q`-twist of the commutative torus; `qbinom` is the built deformation, `qbinom_q1` the `q=1`
  (`θ→0`) commutative limit. This is the OTHER `q` (the count-scaling dial), distinct from the tag-`q`
  (`SYNTHESIS.md` §2). No new work; consolidation onto `quantum_groups.md`.

**The located break (honest, the one the task predicted — the Hilbert-space / completion primitive).**
A spectral triple is `(A, H, D)` with `H` a Hilbert space and `D` an unbounded self-adjoint operator
on `H`; the distance formula needs an operator norm `‖[D,f]‖` and a `sup`. The completion is **absent**:
1. **The Hilbert space `H` / inner product / `D` as an operator on it** — absent (the same gap
   `quantum_mechanics.md` / `operator_algebras.md` located; closest built structure is `CDNorm`'s
   `cdNormSq` + `cdConj`, a norm with conjugation but no inner-product space and no completion).
2. **The operator norm `‖[D,f]‖` and the C*-norm `‖x*x‖=‖x‖²`** — un-built (no `normSq_mul` /
   norm-multiplicativity in `CDNorm.lean`, per `operator_algebras.md`).
3. **The named `SpectralTriple` / `DiracOperator` / `Connes` / `ConnesDistance` / `cyclicCohomology` /
   `HC` / `NCtorus` / `noncommutativeTorus` objects** — grep-confirmed ABSENT (a case-insensitive
   declaration sweep for `spectralTriple|diracOperator|connesDistance|cyclicCohomology|ncTorus|
   noncommutativeTorus|spectral_triple` returns **zero Lean declarations**; the only token "noncommutative"
   hit is `markovGen_noncommutative` — a Markov-generator non-commutativity *fact*, used here as the
   built witness that `mul` is noncommutative, NOT a spectral-triple object). Predicted-not-built, as
   the task anticipated.

This is the same `Real213`/ℂ + completeness residue the analysis cluster repeatedly hits
(`operator_algebras.md`, `quantum_mechanics.md`, `measure.md`). Located, not failed: the discrete
character / bracket / resolution-dial / cyclic-residue / index legs are all PURE-anchored; the
completion object names a concrete open target (a Hilbert space + an operator norm + the `D` operator
on it, then the distance formula's `sup` and Connes' `b`,`B` cyclic operators).

## Touches on model v7.1?

**No new primitive; EXTEND + one consolidation note.** The two invariants (character arrow, `q=±1`
residue) and four axes absorb NCG with nothing added: Gelfand/geometry=spectrum is the `×↦·` character
("object = its readings"), `D` is the resolution dial, the distance formula reads the metric off the
`q=±1` bracket, cyclic cohomology is the residue machine, the NC torus is the deformation-`q`. The note
for the README's batch log:

> **Noncommutative geometry is "geometry = its spectral readings" — `operator_algebras.md`'s Gelfand
> (commutative C*-algebra IS its characters/spectrum) pushed PAST commutativity, with the Dirac
> operator `D` the resolution/metric reading and the distance formula reading the metric off the
> `q=±1` commutator `[D,f]`.** "geometry = spectrum" = the `×↦·` character arrow's "object = its
> readings" (`SYNTHESIS.md` §2, yoneda/motives/Berkovich) at the noncommutative operator locus
> (`markovGen_noncommutative`). `D` = the resolution dial as an operator (`IsResolutionShift_compose`).
> The distance `d(p,q)=sup{|f(p)−f(q)|:‖[D,f]‖≤1}` reads the metric off the antisymmetric bracket
> `[D,f]` — the *same* `q=−1` pair-swap as `Mat2Bracket.bracket_antisymm`, a derivation
> (`bracket_leibniz`, so `[D,f]=df`, `‖[D,f]‖≤1` = unit gradient). Cyclic cohomology = the NC de Rham
> residue (`dsq_zero_universal_delta4`, `reduced_betti_d4_contractible`); the local index formula =
> `index_theory.md`'s analytic=topological collapse in the NC setting; NC tori = the deformation-`q`
> (`qbinom`, the OTHER `q`). Located break (the predicted one): the Hilbert space `H` / operator norm
> `‖[D,f]‖` / the named `SpectralTriple`/`Dirac`/`Connes`/`cyclicCohomology`/`NCtorus` objects are
> grep-confirmed absent — the shared `Real213`/completeness residue. **The character arrow's home
> field reaches its widest statement; the metric itself is the `q=±1` bracket + the resolution dial.**

This sharpens, not alters, model v7.1: it carries Gelfand's "algebra=spectrum" to the noncommutative
locus and pins the noncommutative *metric* as the `q=±1` bracket-derivation read at a resolution scale.

## Verified Lean anchors (file:line:theorem — all grep + `scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file:line) | Purity (scan this session) |
|---|---|---|
| ★★★★ the metric off the `q=±1` commutator `[D,f]`: `[A,B]=−[B,A]`, `tr[A,B]=0`, Jacobi, derivation | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76` `bracket_antisymm`; `:101` `tr_bracket_zero`; `:118` `jacobi`; `:135` `bracket_leibniz`; `:66` `bracket` (def) | **10 PURE / 0 DIRTY** ✓ |
| ★★★★ Gelfand / geometry=spectrum = the `×↦·` multiplicative-functional character (scalar codomain) | `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul` (`det(MN)=det M·det N`) | **130 PURE / 0 DIRTY** ✓ |
| ★★★ Gelfand character = `×↦·` (`{±1}` codomain) | `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` (`QR(ab)⟺(QR(a)⟺QR(b))`) | **5 PURE / 0 DIRTY** ✓ |
| ★★★ the algebra is noncommutative (the regime where `[D,f]≠0`; `C` unchanged) | `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:2433` `markovGen_noncommutative` (`mul genL genR ≠ mul genR genL`) | (in `SternBrocotMarkov`, `det2_mul` module ∅-axiom ✓) |
| ★★★★ `D` = the resolution/metric reading = the resolution dial (grades add under composition) | `Lib/Math/Analysis/ResolutionShift.lean:130` `IsResolutionShift_compose`; `:73` `IsResolutionShift` (def) | **17 PURE / 0 DIRTY** ✓ |
| ★★★ cyclic cohomology = the NC de Rham residue: `δ²=0` + the graded-relation Leibniz | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41` `dsq_zero_universal_delta4`; `:62` `leibniz_universal_delta4` | **5 PURE / 0 DIRTY** ✓ |
| ★★★ cyclic residue `ker δ/im δ` (the reduced Betti residue) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63` `reduced_betti_d4_contractible`; `:42` `kerSizeDelta` (def) | **11 PURE / 0 DIRTY** ✓ |
| ★★★★ the local index = the `q=±1` alternating residue count (ker=converge, coker=escape; `±1` weight) | `Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:86` `multiplier_unimodular`; `:133` `escape_residue_outside`; `:160` `converge_residue_fixed`; `:180` `golden_is_converge` | **55 PURE / 0 DIRTY** ✓ |
| ★★★ the index obstruction / `coker` = the diagonal residue (self-cover faithful but not total) | `Lens/Foundations/FlatOntologyClosure.lean:47` `object1_injective`; `:61` `object1_not_surjective`; `:69` `self_covering_closure` | **7 PURE / 0 DIRTY** ✓ |
| ★★ self-adjoint `D` ⟹ real spectrum = the `q=+1` converge pole (the C*-axiom shadow) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83` `disc_symmetric_nonneg`; `:137` `symmetric_spectrum_real` | **9 PURE / 0 DIRTY** ✓ |
| ★★ `det/tr = e₂/e₁` (the spectrum dissolves the split; the `×↦·`/`×↦+` of `σ(D)`) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:115` `tr_eq_e1`; `:103` `det_eq_e2`; `:204` `det_tr_split_is_e1_e2`; `:167` `disc_eq_gap_squared` | **9 PURE / 0 DIRTY** ✓ |
| ★★ the `*`-involution = the `q=±1` conjugation bit (`(x*)*=x`) | `Lib/Math/NumberSystems/SignedCut/CD/CDConjugation.lean:50` `cdConj_involutive`; `:21` `cdConj` (def) | **7 PURE / 0 DIRTY** ✓ |
| ★★ NC torus = the deformation-`q`; `q=1` (`θ→0`) = commutative limit | `Lib/Math/Combinatorics/QBinomial.lean:36` `qbinom` (def); `:60` `qbinom_q1` (`qbinom 1 n k = choose n k`) | (in `QBinomial`; the OTHER `q`, `SYNTHESIS.md` §2) |
| cross-frame | `operator_algebras.md` (Gelfand = `×↦·`, the C*-completion break), `index_theory.md` (analytic=topological, `D`-as-diagonal), `spectral.md` (`det/tr=e_i`), `quantum_mechanics.md` (`[X,P]`, the Hilbert gap), `curvature.md`/`hyperbolic_geometry.md` (the metric) | prior, ∅-axiom ✓ |

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`Mat2Bracket` 10/0 · `ResidueTag` 55/0 · `FlatOntologyClosure` 7/0 · `Mat2SymmetricSpectrum` 9/0 ·
`Mat2Spectrum` 9/0 · `V4Capstone` 5/0 · `BettiKernel` 11/0 · `ResolutionShift` 17/0 ·
`CDConjugation` 7/0. All PURE, 0 DIRTY. (`det2_mul` 130/0, `legendre_mul` 5/0 per neighbors.)

## Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No named `SpectralTriple` / `DiracOperator` / `Connes` / `ConnesDistance` object in `lean/E213`.**
  A case-insensitive declaration sweep for
  `spectralTriple|diracOperator|connesDistance|spectral_triple|Dirac|Connes` returns **zero Lean
  declarations**. The distance formula `d(p,q)=sup{|f(p)−f(q)|:‖[D,f]‖≤1}` is the calculus's `[D,f]`
  bracket-derivation (built, `Mat2Bracket`) bounded in operator norm (un-built). DROPPED (named open
  target).
- **No `cyclicCohomology` / `HC` / Connes' `b`,`B` operators object.** Grep: zero declarations. The
  *residue mechanism* (`δ²=0` `dsq_zero_universal_delta4`, the graded-relation Leibniz, the reduced
  Betti residue) is built and PURE — cyclic cohomology is `homological_algebra.md`'s residue machine
  on the NC algebra; the named cyclic complex / periodicity operator is absent. CONCEPTUAL.
- **No `NCtorus` / `noncommutativeTorus` / `A_theta` object.** Grep: zero declarations. The
  deformation is the built `qbinom` (the OTHER `q`); `qbinom_q1` is the commutative `θ→0` limit. The
  named NC-torus algebra (the irrational-rotation C*-algebra) is absent — and would sit on the same
  Hilbert/completion residue. PREDICTED-NOT-BUILT.
- **The Hilbert space `H` / inner product / the operator norm `‖[D,f]‖` / the C*-identity
  `‖x*x‖=‖x‖²`** — grep-confirmed un-built (no inner-product vector space, no `normSq_mul` in
  `CDNorm.lean`; closest is `cdNormSq` + `cdConj`, a norm with conjugation, no completion). The genuine
  residue the task predicted; the same gap `operator_algebras.md` / `quantum_mechanics.md` /
  `measure.md` locate. CONCEPTUAL.
- **The smooth `Real213`-cut metric / the geodesic `sup`** — the genuine metric value is a
  `Real213`-cut object (`curvature.md`'s open leg); only the discrete bracket-derivation and the
  resolution dial are built. Cited scope-honest.

### Verified buildable witness (named, not asserted)

The nearest concrete promotion target the legs already support: a **`d=2` discrete commutator-metric
toy** — pick a fixed `D : Mat2` (e.g. a traceless symmetric `Mat2`, `disc_symmetric_nonneg` giving a
real spectrum, the inverse-length scale) and read `[D, M]` for `M` in a commutative sub-`*`-algebra of
`Mat2` (e.g. the diagonal matrices, where `mul` commutes so the two "points" are the two diagonal
characters `χᵢ(M)=Mᵢᵢ` by `det2_mul`-style). Then `[D, M]` (= `Mat2Bracket.bracket D M`, PURE,
`bracket_antisymm`/`bracket_leibniz`) is the discrete `df`, and a finite `max` over `M` with a discrete
`bracket`-norm bound (e.g. the `Mat2.disc`/entrywise `max` of `[D,M]`) realizes a **finite Connes
distance** between the two diagonal points — a `decide`/`ring_intZ` lemma welding `bracket_antisymm`
(the `q=−1` differential) + `det2_mul` (the two characters = the two points) + a finite max into a
literal `d(χ₁,χ₂)` two-point spectral-distance, the discrete `q=+1` shadow of Connes' formula. This is
parallel to `operator_algebras.md`'s `d=2` Gelfand toy and the 2-vertex Laplacian toy
(`graph_theory.md`). Flagged as buildable; **not built** this session (not asserted as an anchor).
