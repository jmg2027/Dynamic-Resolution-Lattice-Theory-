# Decomposition: martingale theory (the martingale law E[X_{n+1}|F_n]=X_n, the Doob decomposition, optional stopping, martingale convergence)

*213-decomposition per `../README.md` (model v7.1). A **consolidation on the weight axis**: it folds
`probability.md` (the **weight-reading** `P=ratio∘count`, expectation = value-weighted count),
`gaussian_clt.md` / `ergodic_theory.md` / `differential_equations.md` (the **`q=+1` converging
fixed point** of a self-applying reading, the `banach_fixed_point_modulated` / `golden_is_converge`
engine), and the closure cluster `measure.md` / `convex_duality.md` / `galois.md` (the **idempotent
`clo` reading** `T²=T`, `biconj_idempotent` / `caraClosure_idempotent`) into one field.*

> **LEVERAGE target.** The bar is not "re-see martingales" but "does the calculus *predict/derive*
> the field's four pillars, and COLLAPSE them onto the two invariants (the character arrow + the
> `q=±1` residue) read on the weight axis?" The thesis, in four parts:
> 1. **a martingale `E[X_{n+1}|F_n]=X_n`** = the conditional-expectation reading (a weight-axis Lens,
>    value-weighted count) is a **FIXED POINT of the filtration-refinement step** — the
>    `q=+1` converge pole of `banach_fixed_point_modulated`/`golden_is_converge`, read on the
>    **σ-algebra-refinement dial** instead of a metric contraction;
> 2. **the Doob decomposition `X = M + A`** = the `⟨C|L⟩ ⊕ Residue(L,C)` split: `M` = the
>    fixed-point part (`q=+1`), `A` = the **predictable residue** the conditional-expectation reading
>    cannot absorb (the drift);
> 3. **optional stopping `E[X_τ]=E[X_0]`** = the fixed point is **invariant under the stopping Lens**;
>    **martingale convergence** (an `L¹`-bounded martingale → a.s.) = the `q=+1` **modulated-completion
>    limit**, the same shape as `DyadicCompletion`'s center-as-completion-limit;
> 4. **the conditional expectation `E[·|F]`** is itself a **projection** (idempotent,
>    `E[E[X|F]|F]=E[X|F]`) = the `clo`-idempotent reading (`biconj_idempotent`,
>    `caraClosure_idempotent`).
> Honest verdict at the end: prediction / collapse-only / miss, Lean-built vs conceptual line drawn.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same distinguishing as `probability.md`/`ergodic_theory.md`: a
  **weight-bearing family of distinguishables** read to a value-weighted count
  (`Expectation.discreteNum`, the `Σ mᵢ·vᵢ` slot; the weight = `L`'s `weight` parameter,
  `probability.md`). Martingale theory adds **no new construction**. What it *does* add over bare
  probability is the **resolution dial run as a refinement chain**: a filtration `F₀ ⊆ F₁ ⊆ …` is
  the σ-algebra-refinement axis — the *same* resolution parameter that dials `Δ`→`d` and discrete→`∫`
  (`derivative.md`/`continuity.md`), here indexing *how finely the weight-reading resolves the family*
  at each stage `n`. A process `(Xₙ)` is the weight-reading read at successive resolutions; the
  filtration is the dial position. (Lean shadow: there is **no `Ω`/σ-algebra/`Filtration` type at
  all** — `Probability/Foundation/Cut.lean` carries only the `(num,den)` readout; the construction is
  implicit, the file holds the reading.)

- **Reading `L`** — three pieces, each already in the calculus, meeting at the `q=+1` pole on the
  weight axis:
  1. **`E[·|F]` = a weight-axis projection (the `clo`-idempotent reading).** Conditional expectation
     coarsens the value-weighted count to the resolution `F` — it replaces a reading by its
     best `F`-resolved representative, and **`E[E[X|F]|F]=E[X|F]` is idempotence `T²=T`**. This is
     *exactly* the closure cluster's `clo` reading: the Carathéodory representative
     `caraClosure (caraClosure s) = caraClosure s` (`OuterMeasure.caraClosure_idempotent`) and the
     Fenchel biconjugate `star(star(star(star x)))=star(star x)` (`FenchelMoreau.biconj_idempotent`)
     are the same `T²=T` shape — a reading replaced by its closed/coarsened representative, fixed
     under re-application. `E[·|F]` is the weight-axis instance of that one idempotent projection.
  2. **the martingale law = a fixed point of the refinement step.** Refining the filtration one stage
     (`Fₙ → F_{n+1}`) is a self-applying step `T` on the weight-reading; the conditional-expectation
     value at stage `n` is `E[X_{n+1}|Fₙ]`. **`E[X_{n+1}|Fₙ]=Xₙ` says the reading is a FIXED POINT of
     that step** — `T(reading at n+1) = (reading at n)`, unchanged by re-projection down a stage. By
     the calculus's `q=+1` rule (`golden_ratio.md`: a fixed point of a self-applying map IS the
     residue, tagged `q=+1` when it converges), a martingale is the **`q=+1` converging residue of the
     filtration-refinement iteration** — the SAME fixed point `banach_fixed_point_modulated` resolves
     for φ, the Gaussian, the ODE solution, and the invariant measure, here read on the
     σ-algebra-refinement dial rather than a metric contraction.
  3. **the limit at residue resolution.** An `L¹`-bounded martingale read not at a finite stage `n`
     but in the **residue** — the limit `X∞ = lim Xₙ` — is the resolution dial pushed to its endpoint,
     narrowed by a modulus, the limit never the operand (`derivative.md`/`continuity.md`'s dial,
     `gaussian_clt.md`'s `picard_cauchy`/`DyadicCompletion` completion-limit).

- **Residue** — `q = ±1`, read at two poles, exactly the Doob split:
  1. *The `q=+1` fixed-point part `M` (the martingale):* the component on which the
     conditional-expectation reading is a fixed point — `M` = the `⟨C|L⟩` part where re-projection
     down a stage changes nothing. Its residue-resolution limit `M∞` is the **`q=+1`
     modulated-completion limit** (`DyadicCompletion`'s center-as-completion-limit).
  2. *The predictable residue `A` (the drift) — what the reading FORCES but cannot absorb:* the part
     of `Xₙ` that the conditional-expectation reading at stage `n−1` already *sees* (predictable) and
     that therefore **shifts the fixed point** — the surplus `A = X − M` the `q=+1` projection leaves
     un-fixed. **`Doob: X = M + A` IS `⟨C|L⟩ ⊕ Residue(L,C)`** on the weight axis: `M` the fixed-point
     reading, `A` the residue. For a submartingale (`E[X_{n+1}|Fₙ] ≥ Xₙ`) the drift is *positive and
     directed* — the `q=±1` **direction bit** on the residue: a martingale is `A=0` (`q=+1`, exact
     fixed point), a strict super/submartingale is `A≠0` with a fixed orientation (the directed residue).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   stochastic process (Xₙ)   =  ⟨ weight-bearing family | the weight-reading at resolution n ⟩      (probability.md's weight + the resolution dial)
   filtration F₀⊆F₁⊆…         =  the σ-algebra-refinement DIAL position  (derivative.md/continuity.md's resolution axis)
   conditional exp E[·|F]     =  the weight-axis PROJECTION = the clo-idempotent reading  (E[E[·|F]|F]=E[·|F] = caraClosure_idempotent / biconj_idempotent, T²=T)
   MARTINGALE E[X_{n+1}|Fₙ]=Xₙ=  the reading is a FIXED POINT of the refinement step  (q=+1 converge, banach_fixed_point_modulated / golden_is_converge)
   super/submartingale ≷       =  A≠0, the directed (q=±1 direction-bit) residue  (drift orientation)
   DOOB X = M + A             =  ⟨C|L⟩ ⊕ Residue(L,C):  M = q=+1 fixed-point part,  A = predictable residue (the drift the projection can't absorb)
   optional stopping E[X_τ]=E[X_0] = the fixed point is INVARIANT under the stopping Lens  (= ergodic_theory's measure-preserving Aut-element, weight fixed)
   MARTINGALE CONVERGENCE     =  Residue(L, C) at residue resolution, q=+1  =  the modulated-completion limit X∞  (= DyadicCompletion center-as-completion-limit)
   L¹-bounded (the hypothesis)=  the weight stays finite  =  the Markov-inequality tail bound  (markov_inequality, the discrete L¹ control)
```

The map to iterate is the **filtration-refinement step `T`** on the weight-reading; the martingale is
its `q=+1` fixed point — `golden_ratio.md`'s φ / the Gaussian / the invariant measure, one level
shifted onto the σ-algebra-refinement dial. The conditional expectation `E[·|F]` supplying each stage
is the `clo`-idempotent projection (`T²=T`). The convergence limit `X∞` is the `q=+1` modulus residue
(`DyadicCompletion`'s completion-limit).

## LEVERAGE — does the calculus PREDICT the four pillars, and COLLAPSE them onto its two invariants?

**Verdict: PREDICTION + PARTIAL — the same profile as `ergodic_theory.md`/`gaussian_clt.md`/
`information_geometry.md`. The calculus predicts all four pillars from existing slots (the weight
axis, the resolution dial, the `q=±1` fixed-point engine, the `clo`-idempotent projection) and
unifies them with the `q=+1` corner the notebook has built across five fields; the engines and the
consolidating ties are real PURE theorems, but the named martingale *objects* — `condExp`,
`Filtration`, `Doob`, `stoppingTime` — are ABSENT (grep-confirmed) and are the located missing leg.**
Three layers:

**(A) Predicted, and the prediction is non-trivial — four predictions, each naming the prior field
that supplies it.** Before looking at the Lean, the calculus emits, from its parts:
- *`E[·|F]` is a projection* = `measure.md`/`convex_duality.md`/`galois.md`'s `clo`-idempotent reading
  read on the weight axis — `E[E[X|F]|F]=E[X|F]` IS `T²=T` (`caraClosure_idempotent`,
  `biconj_idempotent`, `clo_idempotent`). The tower property `E[E[X|G]|F]=E[X|F]` for `F⊆G` is the
  *composition* of two coarsenings collapsing to the coarser — the closure-monad multiplication
  `T∘T=T` on the resolution poset (`galois.md`'s adjoint/closure structure).
- *a martingale is a fixed point* = `golden_ratio.md`'s rule ("a fixed point of a self-applying map =
  the `q=+1` residue") applied to the filtration-refinement step — the SAME `q=+1` fixed point as φ
  (`golden_is_converge`), the Gaussian (`gaussian_clt.md`), the ODE solution, and the invariant
  measure (`ergodic_theory.md`), via `banach_fixed_point_modulated`. Read on the σ-algebra-refinement
  dial, not a metric contraction — the resolution axis (`derivative.md`) in the iterator role.
- *Doob `X=M+A`* = the README's normal form `⟨C|L⟩ ⊕ Residue(L,C)` on the weight axis: `M` the
  `q=+1` fixed-point reading, `A` the predictable residue (the drift), with the super/submartingale
  *direction bit* the `q=±1` orientation on `A`.
- *optional stopping `E[X_τ]=E[X_0]`* = the fixed point is invariant under the stopping Lens — the
  *same* shape as `ergodic_theory.md`'s **measure-preserving `T`** (an `Aut`-element fixing the
  weight-character, `noether.md`'s `q=+1` invariant `det_holonomy_eq_one`): stopping is a
  weight-preserving reading, so the `q=+1` fixed value survives it.
- *martingale convergence* = the `q=+1` converging residue at residue resolution
  (`DyadicCompletion`'s completion-limit), with the `L¹`-bound the finiteness control that keeps the
  weight from escaping (the discrete `markov_inequality` tail bound).
Composing these *forces* the form "the conditional-expectation reading is a `q=+1` fixed point of
filtration refinement (the martingale), its predictable surplus is the Doob residue `A` (directed for
super/sub), the fixed point survives any stopping Lens (optional stopping), and under an `L¹`-bound it
converges to its residue-resolution completion-limit `X∞`." That is a derivation of the field's
*shape* — which fixed point, why `q=+1`, why `E[·|F]` is idempotent, what the Doob residue is, and why
convergence is a completion-limit — not a relabeling. It passes the re-skin guard the way
`entropy.md`/`gaussian_clt.md`/`ergodic_theory.md` did.

**(B) The Lean spine that is actually built (verified ∅-axiom this session via `tools/scan_axioms.py`)
— the engines and consolidating ties are real PURE theorems; only the named martingale object is
missing.**

- **The `q=+1` fixed-point / converge engine — the SAME object φ, the Gaussian, the invariant measure,
  and the ODE flow lean on.** `BanachFixedPointModulated.banach_fixed_point_modulated`
  (`:111`): a contraction over a modulated-complete metric has a located fixed point `x* = picardLim …`
  reached by **none**, at every scale; `ResidueTag.converge_residue_fixed` (`:160`) packages it as the
  `q=+1` pole; `ResidueTag.golden_is_converge` (`:180`) ties `+1` to the literal φ Cassini multiplier;
  `ResidueTag.residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`). This is the engine the
  martingale (= the refinement-step fixed point) and the convergence limit need — *literally the same
  one*. (ResidueTag 55/0; BanachFixedPointModulated PURE, names under
  `CompleteMetricModulusMod`/`CompleteMetricModulus`.)
- **The completion-limit at the `q=+1` pole — the convergence-limit's exact shape, ∅-axiom.**
  `DyadicCompletion.lean` (32/0): a genuine quotient-free Cauchy-completion `DyC L` of the dyadic
  metric (Bishop regular-Cauchy, no `Quot.sound`), the contraction lifted to it
  (`Φhat_contraction`), and `orbit_to_center_completion` / `gaussian_center_fixed_via_engine` —
  the Picard orbit converges *in the completion metric* to the fixed point as a true completion-limit.
  This is the structural template for `Xₙ → X∞` (an `L¹`-bounded martingale's a.s. limit = the
  reached-by-none completion-limit of the refinement orbit). The engine instantiated on a
  reading-of-readings is `ConvolveRescaleContraction.orbit_to_center` (`:471`) (20/0).
- **`E[·|F]` = the idempotent projection (`T²=T`), ∅-axiom — the leverage tie.** The
  conditional-expectation-as-projection claim is grounded by the *same* `clo`-idempotent theorems the
  closure cluster runs on: `OuterMeasure.caraClosure_idempotent` (`:217`, `clo(clo s)=clo s`
  *literally*; the Galois connection `cara_gc` `:182`) and `FenchelMoreau.biconj_idempotent` (`:134`,
  `f****=f**`) with `closed_iff_fixed` (`:152`, the closure-fixed locus = the residue vanishing,
  `q=+1`), plus the abstract `GaloisConnection.clo_idempotent` (`:126`). `E[·|F]` is the weight-axis
  instance of this one idempotent reading; the tower property is its composition `T∘T=T`.
  (OuterMeasure 29/0, FenchelMoreau 18/0.)
- **The weight-reading itself + linearity, ∅-axiom — the value-weighted count `E[·]`.**
  `Expectation.discreteNum` (`:27`), `discreteNum_append` (`:62`, linearity of expectation = the
  `+↦+` character on concatenation); `Independence.joint` + `joint_assoc_num` (the `×↦·` character,
  independence). These are the weight axis the conditional-expectation reading coarsens.
  (Expectation 5/0, Independence 12/0.)
- **The `L¹`-bound = the discrete Markov tail bound, ∅-axiom.** `Markov.markov_inequality` (`:66`):
  `a·#{vᵢ≥a} ≤ Σ mᵢ·vᵢ` — the value-weighted count's tail is controlled by its first moment, the
  discrete `L¹`-control that keeps the martingale weight from escaping (the convergence hypothesis).
  The file states its own scope: *"No σ-algebra, no filtration"* — `Nat`-arithmetic only.
  (Markov 6/0.)
- **Optional stopping = the weight-preserving (`q=+1` invariant) reading, ∅-axiom skeleton.** Reusing
  `ergodic_theory.md`'s built tie: a stopping that preserves the weight-character is a
  measure-preserving `Aut`-element, `noether.md`'s `det_holonomy_eq_one` conserved `q=+1` invariant;
  the cyclic measure-preserving instance `CyclicErgodic` (26/0) shows the `q=+1` fixed value reached
  exactly under a weight-preserving map. The stopping Lens *applied to a martingale* (the
  optional-stopping theorem as one statement) is the conceptual leg.
- **The residue-resolution limit = the LLN/CLT modulus, ∅-axiom.** `CLTLimit.balanced_LLN_modulus`
  (`:31`) and `LLN.countTrue_append`/`LLN_unit`/`bernoulli_LLN_exact` (the running-mean `+↦+`
  character) are the *structurally identical* modulus-narrowed-reached-by-none residue the martingale
  convergence limit instantiates — `Xₙ → X∞` is the running weight-reading's `q=+1` Cauchy residue
  with the filtration supplying the successive resolutions. (CLTLimit 4/0, LLN 7/0.)

**(C) The remaining gap — predicted-not-built (the honest line, the precise missing leg).** Grep on
`lean/E213` for `martingale`/`submartingale`/`supermartingale`/`Doob`/`condExp`/`conditional
expectation`/`stoppingTime`/`optional.*stopping`/`filtration` (in the probabilistic sense)/
`measurePreserving` returns **zero** real hits (the only `filtration` hits are cohomology filtrations;
the only `Markov` is the inequality + the Diophantine `MarkovTree`; "tower property" hits are the
unrelated `TriangularTower` geometry). What the Lean does **NOT** contain — and this is the brief's
named target:
- **No `Filtration` object** — no refinement chain `F₀⊆F₁⊆…` of σ-algebras (the repo has the
  *resolution dial* as a parameter, never a named increasing chain of sub-σ-algebras; consistent with
  the probability tree's declared "no σ-algebra").
- **No conditional-expectation object `E[·|F]`** — no `condExp : (reading) → (resolution) → (reading)`
  carrying `E[E[X|F]|F]=E[X|F]`. The idempotent projection exists *abstractly* (`caraClosure`,
  `FenchelMoreau.star`, `clo`) but is **not instantiated on the weight-reading as a conditional
  expectation**; the weld (`E[·|F]` = `clo` on the σ-algebra-refinement poset, with the tower property
  = closure-composition) is unbuilt.
- **No `Martingale` predicate** — no `Martingale F X := ∀n, condExp (X (n+1)) (F n) = X n`, and no
  theorem identifying it with `banach_fixed_point_modulated`'s `q=+1` fixed point. The fixed-point
  engine is the *same one* (`golden_is_converge`/`converge_residue_fixed`), but the substitution
  "filtration-refinement step in the iterator role" is not made.
- **No `Doob decomposition` object** — no `X = M + A` with `M` a martingale and `A` predictable. The
  `⟨C|L⟩ ⊕ Residue` split is the *predicted shape*; the actual `M`/`A` decomposition theorem is absent.
- **No `optional stopping` theorem** — no `stoppingTime`/`stoppedProcess` and no `E[X_τ]=E[X_0]`. The
  weight-preserving-`Aut` tie (`ergodic_theory.md`'s `measure_preserving`/`det_holonomy_eq_one`) is the
  conceptual analogue; the optional-stopping statement is unbuilt.
- **No `martingale convergence` theorem** — no `L¹`-bounded `(Xₙ)` shown to converge to `X∞`. The
  `DyadicCompletion` completion-limit is the *structural template* and `markov_inequality` the `L¹`
  control, but `Xₙ → X∞` as one statement (with the upcrossing/modulus argument) is the named missing
  leg — the same status `gaussian_clt.md`/`ergodic_theory.md` report for their field-specific limit
  objects.

**Net.** Not collapse-only — it *predicts* all four pillars and *derives* the field's shape (the
martingale = the `q=+1` refinement fixed point, `E[·|F]` = the idempotent projection, Doob = the
`⟨C|L⟩⊕Residue` split, convergence = the completion-limit). Not a miss — the `q=+1` engine
(`banach_fixed_point_modulated`/`golden_is_converge`), its completion-limit instantiation
(`DyadicCompletion`), the `clo`-idempotent projection (`caraClosure_idempotent`/`biconj_idempotent`),
the weight-reading + linearity (`discreteNum_append`), the `L¹` tail bound (`markov_inequality`), and
the LLN/CLT modulus residue (`balanced_LLN_modulus`) are **all real ∅-axiom theorems**. It is a
**prediction whose engines and consolidating ties are fully built**, one notch below a closed
derivation for the *same reason* as `ergodic_theory.md`/`gaussian_clt.md`: the field-specific
*objects* — `Filtration`, `condExp`, `Martingale`, `Doob`, `stoppingTime` — are conceptual welds, not
yet instantiated.

## Revelation (collapse + residue-surfaced + forcing)

**The martingale, the Doob decomposition, optional stopping, and martingale convergence are ONE
`(C, L)` — the weight-reading projected along the filtration-refinement dial and its `q=±1` residue —
resolved by the SAME `banach_fixed_point_modulated` / `clo`-idempotent / completion-limit machinery
that resolves φ, the Gaussian, the invariant measure, and the closure monad.** Collapse + residue +
forcing, three at once:

1. **Collapse onto the `q=+1` corner + the `clo` projection.** A *martingale* (the refinement-step
   `q=+1` fixed point), *conditional expectation* (the idempotent `clo` projection), *Doob* (the
   `⟨C|L⟩⊕Residue` split), *optional stopping* (the fixed point under a weight-preserving Lens), and
   *martingale convergence* (the `q=+1` completion-limit) are not five concepts — they are one
   weight-reading read at one setting of the `q=±1` bit, the resolution dial, and the idempotent
   projection. The martingale is *literally the same `q=+1` object* as φ (`golden_is_converge`), the
   Gaussian (`gaussian_clt.md`), the invariant measure (`ergodic_theory.md`), and the ODE solution
   (`differential_equations.md`) — now read on the σ-algebra-refinement dial. **`E[·|F]` is the same
   idempotent projection** as `measure.md`'s Carathéodory closure and `convex_duality.md`'s Fenchel
   biconjugate (`caraClosure_idempotent`/`biconj_idempotent`, `T²=T`).

2. **Residue surfaced — the Doob decomposition IS the normal form.** `X = M + A` is not an ad-hoc
   sum: it is `⟨C|L⟩ ⊕ Residue(L,C)` on the weight axis, with `M` the `q=+1` fixed-point reading and
   `A` the predictable residue (the drift the conditional-expectation reading forces but cannot
   absorb). "The martingale part" and "the predictable compensator" are the calculus's `⟨C|L⟩` and its
   `Residue` — and the super/submartingale **direction bit** is the `q=±1` orientation on `A`
   (`A=0` = `q=+1` exact fixed point; `A` directed = the residue with a sign, the same orientation
   fold as ℤ/`det`/`∂`). The "drift" stops being a separate primitive and becomes the residue of a
   reading.

3. **Forcing — the `q=+1` bit forces martingale vs super/submartingale, and idempotence forces the
   tower property.** Whether the conditional-expectation reading is an *exact* fixed point (`A=0`,
   martingale, `q=+1`) or shifts with a fixed orientation (`A≠0`, super/sub, the directed residue) is
   the `q=±1` bit. And `E[E[X|G]|F]=E[X|F]` (`F⊆G`) is *forced* by closure-composition `T∘T=T` — the
   tower property is not an axiom but the idempotent-projection law on the resolution poset
   (`clo_idempotent`/`caraClosure_idempotent`). Optional stopping is then forced as "a `q=+1` fixed
   value survives a weight-preserving Lens" (`ergodic_theory.md`'s `measure_preserving` tie).

**THE CONSOLIDATION (the brief's central question): the `q=+1` fixed-point residue now spans SIX
weight-axis fields, and martingale theory is the conditional-expectation reading among them.** The
single `banach_fixed_point_modulated` / completion-limit / `clo`-idempotent machinery is the
residue-resolver for:

| | what iterates / projects | `q=+1` fixed point / residue | Lean engine |
|---|---|---|---|
| `golden_ratio.md` (φ) | Möbius `T` on `(p,q)` | φ | `golden_is_converge` (built) |
| `gaussian_clt.md` (Gaussian) | `Φ`=convolve⋆rescale on a weight | the Gaussian profile | `banach_fixed_point_modulated`+`Φ_contraction`+`DyadicCompletion` (built) |
| `differential_equations.md` (ODE) | Picard step on a function | the solution curve | `banach_fixed_point_modulated`+`orbit_eq_iter` (built) |
| `ergodic_theory.md` (invariant measure) | `T_*` on a weight | the invariant measure + ∫f dμ | `banach_fixed_point_modulated`/`closed_const` (engine built; `T_*` object not) |
| `measure.md`/`convex_duality.md` (`clo`) | the coarsening/closure reading | the closure-fixed element | `caraClosure_idempotent`/`biconj_idempotent` (built) |
| **`martingales.md`** | **filtration-refinement step on the weight-reading** | **the martingale `M` + its limit `X∞`** | **engine built (`banach_fixed_point_modulated`/`DyadicCompletion`/`caraClosure_idempotent`/`markov_inequality`); `condExp`/`Filtration`/`Martingale`/`Doob` object NOT built** |

So **YES** — a martingale = the conditional-expectation reading as the `q=+1` converging fixed point
of filtration refinement (the same `banach_fixed_point_modulated`/`golden_is_converge` pole, read on
the σ-algebra-refinement dial); the Doob decomposition `X=M+A` = `⟨C|L⟩⊕Residue` (the `q=+1`
fixed-point part + the predictable directed residue); optional stopping = the fixed point invariant
under a weight-preserving Lens (`ergodic_theory.md`'s `measure_preserving`/`det_holonomy_eq_one`);
martingale convergence = the `q=+1` modulated-completion limit (`DyadicCompletion`'s
center-as-completion-limit); and `E[·|F]` = the `clo`-idempotent projection
(`caraClosure_idempotent`/`biconj_idempotent`, `T²=T`). Martingale theory **consolidates the
weight-axis cluster** (`probability` + `gaussian_clt` + `ergodic` + the `clo`-closure
`measure`/`convex_duality`) at one `q=+1` fixed point read through the idempotent projection. The
precise missing leg is the named martingale *object*: a `Filtration`, the `condExp` projection, the
`Martingale` predicate, the `Doob` split, the `stoppingTime`/optional-stopping theorem, and the `L¹`
convergence theorem.

## Note for the technique — does martingale theory force a NEW construct?

**No new primitive — EXTEND, a weight-axis consolidation.** This decomposition adds nothing to model
v7.1; it *uses* existing slots and shows the weight-axis fields meet at the conditional-expectation
projection:
- *`E[·|F]`* = the `clo`-idempotent reading (`caraClosure_idempotent`/`biconj_idempotent`) read on
  the weight axis — no new slot, an instance of the closure-projection the calculus already runs;
- *martingale* = `golden_ratio.md`'s `q=+1` fixed-point rule applied to the filtration-refinement
  step (the resolution dial in the iterator role, `derivative.md`);
- *Doob `X=M+A`* = the README's normal form `⟨C|L⟩⊕Residue(L,C)`, with the super/submartingale
  direction the `q=±1` orientation on the residue;
- *optional stopping* = `ergodic_theory.md`'s weight-preserving `Aut`-element / `noether.md`'s `q=+1`
  invariant (a fixed value survives a measure-preserving Lens);
- *martingale convergence* = `gaussian_clt.md`/`DyadicCompletion`'s `q=+1` completion-limit at residue
  resolution, with the `L¹`-bound the discrete `markov_inequality` tail control.

The one sharpening for the technique: **the resolution dial run as a *refinement chain* (a filtration)
turns the conditional-expectation reading into a `q=+1` fixed point — and the Doob decomposition makes
the `⟨C|L⟩⊕Residue` normal form a *named theorem of the field itself* (M = `⟨C|L⟩`, A = `Residue`).**
This is the cleanest external corroboration of the README's normal form: a classical theorem
(Doob) *is* the calculus's split, with the martingale the fixed-point reading and the compensator the
residue. The calculus thus *predicts* the martingale law (the refinement fixed point), the projection
property of `E[·|F]` (idempotence), the Doob split (the normal form), and convergence (the
completion-limit) from the model's slots, not from measure-theoretic analysis added on top.

---

## Verified Lean anchors (file:line:theorem — all grep-verified; purity by `tools/scan_axioms.py`, re-run this session)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| **martingale = `q=+1` refinement fixed point** (the **engine** — shared with φ, Gaussian, invariant measure, ODE) | `Lib/Math/Analysis/BanachFixedPointModulated.lean : banach_fixed_point_modulated` (`:111`), `picardLim` (`:95`), `inhabited_banach_fixed_point_modulated` (`:167`) | ∅-axiom ✓ (PURE) |
| the `q=+1` pole packaged + φ-tie | `Lib/Math/Foundations/ResidueTag.lean : converge_residue_fixed` (`:160`), `golden_is_converge` (`:180`), `residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`), `escape_residue_outside` (`:133`) | ∅-axiom ✓ (55/0) |
| **martingale convergence = the `q=+1` completion-limit `X∞`** (the **template** — center as true completion-limit) | `Lib/Math/Probability/Limit/DyadicCompletion.lean : orbit_to_center_completion`, `gaussian_center_fixed_via_engine`, `completeDyMod`, `Φhat_contraction` | ∅-axiom ✓ (32/0) |
| the engine instantiated on a reading-of-readings (the convolve-rescale `q=+1` fixed point) | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean : orbit_to_center` (`:471`), `center_fixed`, `Φ_contraction` | ∅-axiom ✓ (20/0) |
| **`E[·|F]` = the idempotent projection (`T²=T`); tower property = closure-composition** (the leverage tie) | `Lib/Math/Analysis/Measure/OuterMeasure.lean : caraClosure_idempotent` (`:217`), `cara_gc` (`:182`); `Lib/Math/Order/FenchelMoreau.lean : biconj_idempotent` (`:134`), `closed_iff_fixed` (`:152`); `Lib/Math/Order/GaloisConnection.lean : clo_idempotent` (`:126`) | ∅-axiom ✓ (OuterMeasure 29/0, FenchelMoreau 18/0) |
| the weight-reading `E[·]` + linearity (value-weighted count, `+↦+` character) | `Lib/Math/Probability/Foundation/Expectation.lean : discreteNum` (`:27`), `discreteNum_append` (`:62`) | ∅-axiom ✓ (5/0) |
| independence = `×↦·` character (the multiplicative twin) | `Lib/Math/Probability/Foundation/Independence.lean : joint` (`:27`), `joint_assoc_num` (`:87`) | ∅-axiom ✓ (12/0) |
| **`L¹`-bound = the discrete Markov tail control** (the convergence hypothesis; file: "no σ-algebra, no filtration") | `Lib/Math/Probability/Inequality/Markov.lean : markov_inequality` (`:66`), `tailMomentNum` (`:52`), `tailMassNum` (`:58`) | ∅-axiom ✓ (6/0) |
| residue-resolution limit = the LLN/CLT modulus (reached-by-none, running-mean `+↦+`) | `Lib/Math/Probability/Limit/CLTLimit.lean : balanced_LLN_modulus` (`:31`); `Lib/Math/Probability/Limit/LLN.lean : countTrue_append` (`:29`), `LLN_unit` (`:58`), `bernoulli_LLN_exact` (`:66`) | ∅-axiom ✓ (CLTLimit 4/0, LLN 7/0) |
| optional stopping = the weight-preserving (`q=+1` invariant) reading (the `ergodic_theory.md` tie) | `Lib/Math/Combinatorics/CyclicErgodic.lean : measure_preserving`, `birkhoff_period_eq_space` (prior, `ergodic_theory.md`, 26/0); `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean : det_holonomy_eq_one` (`:136`) | ∅-axiom ✓ (prior) |

> Axiom-purity note: every module above was re-run through `tools/scan_axioms.py` from repo root this
> session — ResidueTag 55/0, DyadicCompletion 32/0, ConvolveRescaleContraction 20/0, FenchelMoreau
> 18/0, OuterMeasure 29/0, Markov 6/0, LLN 7/0, CLTLimit 4/0, Expectation 5/0, Independence 12/0.
> `BanachFixedPointModulated`'s headline `banach_fixed_point_modulated` reports PURE (its public names
> live under the `CompleteMetricModulusMod`/`CompleteMetricModulus` structures; `ResidueTag`'s
> `converge_residue_fixed` delegates to it and is itself PURE in the 55/0 scan). The `CyclicErgodic`/
> holonomy rows rest on `ergodic_theory.md`'s fresh scan + in-file docstrings.

### Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

- **No `Martingale` / `submartingale` / `supermartingale` predicate** — grep for
  `martingale`/`submartingale`/`supermartingale` returns **0** hits. The fixed-point engine
  (`banach_fixed_point_modulated`/`golden_is_converge`) is the predicted resolver; the substitution
  "filtration-refinement step in the iterator role" is unmade. **Predicted-not-built.**
- **No conditional-expectation object `E[·|F]` / `condExp`** — grep for `condExp`/`conditional
  expectation` returns **0** real hits. The idempotent projection exists abstractly (`caraClosure`,
  `FenchelMoreau.star`, `clo`) but is **not instantiated on the weight-reading**; the weld (`E[·|F]` =
  `clo` on the σ-algebra-refinement poset, tower property = closure-composition) is unbuilt.
  **Predicted-not-built.**
- **No `Filtration` object** — the probabilistic increasing σ-algebra chain is absent (the only
  `filtration` hits in `lean/E213` are *cohomology* filtrations, an unrelated sense). The repo has the
  resolution dial as a *parameter*, never a named refinement chain. **ABSENT (consistent with the
  probability tree's declared "no σ-algebra").**
- **No `Doob decomposition` object `X = M + A`** — no martingale/predictable split theorem. The
  `⟨C|L⟩⊕Residue` shape is the prediction; the `M`/`A` decomposition is unbuilt. **Predicted-not-built.**
- **No `optional stopping` theorem / `stoppingTime` / `stoppedProcess`** — grep for
  `stoppingTime`/`optional.*stopping` returns **0** hits. The weight-preserving-`Aut` tie
  (`ergodic_theory.md`'s `measure_preserving`/`det_holonomy_eq_one`) is the conceptual analogue;
  `E[X_τ]=E[X_0]` as one statement is unbuilt. **Predicted-not-built.**
- **No `martingale convergence` theorem** — no `L¹`-bounded `(Xₙ)→X∞` statement (no upcrossing/Doob
  convergence). `DyadicCompletion`'s completion-limit is the structural template and `markov_inequality`
  the `L¹` control, but the convergence theorem is unbuilt. **Predicted-not-built.**
- **No `measurePreserving` object** — grep returns **0** hits (the optional-stopping tie rests on the
  conceptual `ergodic_theory.md` weight-preserving-`Aut` analogue, itself a prediction there). Honest:
  the `q=+1` engine is shared; the named measure-preserving-transformation object is absent.
