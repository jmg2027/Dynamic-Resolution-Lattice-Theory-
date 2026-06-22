# Decomposition: ergodic theory (measure-preserving transformations, the Birkhoff/von Neumann ergodic theorem, mixing, the ergodic decomposition)

*213-decomposition of ergodic theory, per `../README.md` (model v7.1).*
*The consolidation entry: this field is where **five** prior decompositions meet at one fixed point —
`measure.md` (the **weight-reading**, the Choice-free `q=+1` corner), `gaussian_clt.md` (the **q=+1
convolve-rescale fixed point**, the Birkhoff/LLN modulus residue), `differential_equations.md` (the
**q=+1 contraction** engine `banach_fixed_point`; the flow as the iterated reading), `graph_theory.md`
(the **dim-1 constant `q=+1` kernel** = the Laplacian's `λ₀=0`), and `spectral.md` (the transfer
operator's dominant eigenvalue 1 / spectral gap = the symmetric-spectrum `q=+1` corner).*

> **LEVERAGE target.** The bar is not "re-see ergodicity" but "does the calculus *predict/derive* the
> ergodic theorem, and does it COLLAPSE the field's four pillars into the calculus's two invariants
> (the character arrow + the `q=±1` residue)?" Hypothesis, in four parts:
> 1. **measure-preserving `T`** = a weight-preserving reading = an `Aut`-family element fixing the
>    measure-character (`measure.md`'s weight ∘ `groups.md`'s `Aut` ∘ `noether`'s invariant);
> 2. **the invariant measure `μ`** = the **q=+1 fixed point of the push-forward `T_*`** — the SAME
>    `banach_fixed_point`/Markov-stationary/Gaussian fixed point;
> 3. **the ergodic theorem "time-average = space-average"** = the **q=+1 converging Birkhoff residue**
>    `(1/n)Σ f∘Tⁱ → ∫f dμ` — the SAME modulus-narrowed-reached-by-none structure as the LLN/Gaussian
>    (`balanced_LLN_modulus`/`picard_cauchy`); **ergodicity** = the T-invariant subspace is 1-dimensional
>    = the constant = the SAME `dim ker = 1` `q=+1` kernel as `graph_theory.md`'s Laplacian `λ₀=0`;
> 4. **mixing** = correlation decay = a **contraction** (the transfer/Koopman operator's spectral gap,
>    `spectral.md`'s `λ₁`); **the ergodic decomposition** = the extreme-point/`q=±1` simplex
>    decomposition (`convex_duality`).
> Honest verdict at the end: prediction / collapse-only / miss, Lean-built vs conceptual line drawn.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **self-applying weight-bearing distinguishing**. Two structures from prior
  notes meet in one `C`: (i) the **weight-bearing point-family** of `measure.md` (`DyadicMeasurableSet`
  = a finite `List DyadicBracket`, the weight-reading `measureNum` = `Σ lenNum`, no `Ω`/σ-algebra/Choice
  — the `q=+1` corner); and (ii) the **self-applying evolution step** of `differential_equations.md` (a
  reading whose next operand is its own output, `orbit_eq_iter`: an orbit *is* the count iterating the
  step). A "dynamical system with a measure" is exactly these glued: a weight-bearing family with a
  reading `T` that is re-fed its own output. Nothing measure-theoretic or analytic is constructed beyond
  what `measure.md` + `differential_equations.md` already built — `T` iterated by the count is the flow
  (`OrbitIsIter`), the weight is `measureNum`.

- **Reading `L`** — three pieces, each already in the calculus, meeting at the `q=+1` pole:
  1. **`T` = a measure-preserving reading = an `Aut`-family element fixing the weight-character.**
     `groups.md` established a group = `⟨C | the C-preserving self-readings (Aut C), composition⟩`. A
     measure-preserving transformation is an `Aut`-element that *additionally preserves the measure
     readout* — `measureNum(T S) = measureNum(S)`. This is `noether.md`'s conserved-character condition
     (`det_holonomy_eq_one`, the `q=+1` invariant) read on the weight: `T` is in the subgroup of `Aut`
     that fixes the measure-character. The composition-closed family `{Tⁿ}` is the cyclic monoid of
     `differential_equations.md` (the flow). So `T` carries no new primitive — it is the intersection of
     `groups.md`'s `Aut`, `measure.md`'s weight, and `noether.md`'s invariant.
  2. **the push-forward `T_*` on measures + its fixed point** — `T` lifts to a map `T_*` on the
     weight-readings themselves (a reading-of-readings, `gaussian_clt.md`'s level). An **invariant
     measure** is `T_*`'s **fixed point** `T_* μ = μ`. By the calculus's `q=+1` rule
     (`golden_ratio.md`: a fixed point of a self-applying map IS the residue, tagged `q=+1` when it
     converges), the invariant measure is the **q=+1 converging residue** of the push-forward iteration —
     the SAME fixed point `banach_fixed_point` resolves for φ, the Gaussian, and the ODE solution.
  3. **the Birkhoff time-average at residue resolution** — `Aₙf := (1/n)Σ_{i<n} f∘Tⁱ`, the running
     mean of `f` along the orbit, read not at a finite stage but in the **residue**, narrowed by a
     modulus `N(ε)` — `derivative.md`/`continuity.md`'s resolution dial, `measure.md`'s interior `q=+1`
     modulus residue. This is *structurally identical* to the LLN's sample mean `(1/n)Σ` and its modulus
     `balanced_LLN_modulus` — the time-average is the LLN's `q=+1` Cauchy residue with `T` supplying the
     successive samples.

- **Residue** — what this iterated weight-bearing reading forces but cannot capture, at two poles:
  1. *The `q=+1` Birkhoff residue (the ergodic theorem itself):* the **space-average `∫f dμ`** is the
     reached-by-none limit of the time-averages `Aₙf`. No finite `n` lands on it; the modulus `N(ε)`
     narrows it (the limit never the operand) — the EXACT signature of `golden_ratio.md`'s φ, the LLN's
     `balanced_LLN_modulus`, and the Gaussian's `picard_cauchy`. "Time-average = space-average" IS this
     residue surfacing: the orbit-mean and the weight-mean are one `q=+1` residue read two ways
     (dynamically along the orbit / frozen as the integral), the same "frozen = dynamic" simultaneity as
     `golden_ratio.md`'s `P(φ)=φ` vs `Pⁿ→φ`.
  2. *The `q=−1` escape pole (non-ergodicity / the simplex's extreme points):* when the T-invariant
     reading is *not* 1-dimensional, the invariant subspace splits — the system decomposes into pieces.
     The **ergodic decomposition** writes any invariant `μ` as an average of the *extreme* (ergodic)
     invariant measures — the `q=±1` extreme-point/simplex decomposition of `convex_duality.md`. A
     non-ergodic system is the `q=−1`-flavoured failure of the constant-kernel collapse (more than one
     independent invariant), exactly `graph_theory.md`'s disconnected graph where `dim ker L > 1`.

  **Ergodicity = the `q=+1` collapse to dimension 1.** The T-invariant functions form a subspace; the
  constant function is always invariant (`f∘T = f` for `f ≡ c`). **Ergodic ⟺ that subspace = the
  constants = dimension 1** — which is *literally* `graph_theory.md`'s `λ₀=0` constant kernel: the
  invariant subspace is the kernel of `(I − Koopman)` exactly as the connected-component space is the
  kernel of the Laplacian `L = D − A`, and "ergodic" = "connected" = `dim ker = 1` = the all-ones/constant
  fixed vector (`pathLaplacian_const_kernel`, `closed_const`, `closed_root_determines`).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   dynamical system (X,μ,T)  =  ⟨ weight-bearing point-family | a self-applying reading T ⟩
                               (C = measure.md's measureNum-weight ⊕ diff_eq.md's evolution step)
   measure-preserving T      =  T ∈ Aut(C) fixing the weight-character  (groups.md ∘ noether's q=+1 invariant)
   flow / orbit Tⁿ           =  ⟨ T | iterated by the count ⟩ = iter      (OrbitIsIter.orbit_eq_iter)
   push-forward T_*          =  T lifted to the weight-readings           (a reading-of-readings, CLT level)
   INVARIANT MEASURE μ       =  Residue(T_*, C), q=+1  =  the fixed point T_* μ = μ   (= φ/Gaussian/ODE/Markov-stationary)
   Birkhoff average Aₙf      =  (1/n) Σ_{i<n} f∘Tⁱ      =  the LLN sample-mean along the orbit (resolution dial)
   SPACE-AVERAGE ∫f dμ       =  Residue(Aₙ, C), q=+1  =  reached-by-none, narrowed by modulus N(ε)  (limit never operand)
   "time-avg = space-avg"    =  the q=+1 Birkhoff residue surfacing  (Aₙf → ∫f dμ)  = LLN/picard_cauchy structure
   ERGODICITY                =  invariant subspace = constants = dim ker(I−Koopman) = 1   (= graph_theory's λ₀=0!)
   transfer / Koopman op     =  the linear reading; dominant eigenvalue 1 (q=+1) = the invariant measure
   MIXING                    =  correlation decay  =  a CONTRACTION  (the spectral gap λ₁, diff_eq's q=+1 contraction)
   ergodic decomposition     =  any invariant μ = average of extreme (ergodic) μᵢ  =  q=±1 simplex (convex_duality)
```

The map to iterate is `T_*` on weights (`gaussian_clt.md`'s `Φ` with `T_*` in the iterator role); the
invariant measure is its `q=+1` fixed point — `golden_ratio.md`'s φ one level up, the SAME `Φ` /
Markov-stationary / Banach object. The Birkhoff average `Aₙ` is the LLN sample-mean (`countTrue_append`'s
running count) read at residue resolution; the space-average `∫f dμ` is its `q=+1` modulus residue.

## LEVERAGE — does the calculus PREDICT the ergodic theorem, and COLLAPSE the field's four pillars?

**Verdict: PREDICTION — the most consolidating entry in the notebook. The calculus predicts all four
pillars from existing slots and unifies FIVE prior fields at one `q=+1` fixed point, with the
ergodicity = constant-kernel = `graph_theory`-Laplacian tie and the Birkhoff = LLN tie both Lean-grounded
at the structural level. The missing leg is precisely an *actual measure-preserving-transformation /
Birkhoff-average object* — the same kind of gap `differential_equations.md`/`gaussian_clt.md` have for
their field-specific operators, and `knots.md`/`model_theory.md` have for a named object.** Three layers:

**(A) Predicted, and the prediction is non-trivial — it is FOUR predictions, each naming the prior field
that supplies it.** Before looking at the Lean, the calculus emits, from its parts:
- *measure-preserving `T`* = `groups.md`'s `Aut` ∩ `measure.md`'s weight ∩ `noether.md`'s `q=+1`
  invariant — `T` is the weight-character-preserving automorphism, ties Noether (`det_holonomy_eq_one`);
- *invariant measure* = the `q=+1` fixed point of `T_*` — `golden_ratio.md`'s rule ("fixed point of a
  self-applying map = the `q=+1` residue") applied to the push-forward; the SAME fixed point as the
  Gaussian (`gaussian_clt.md`), the ODE solution (`differential_equations.md`), φ, and a Markov stationary
  vector;
- *ergodic theorem* = the `q=+1` converging Birkhoff residue, narrowed by a modulus, reached by none —
  `golden_ratio.md`/`gaussian_clt.md`'s residue, with ergodicity = `dim`-1 invariant subspace =
  `graph_theory.md`'s constant Laplacian kernel `λ₀=0`;
- *mixing* = a contraction / spectral gap — `differential_equations.md`'s `q=+1` contraction +
  `spectral.md`'s `λ₁` (the gap below the dominant eigenvalue 1).
Composing these *forces* the form "the orbit-mean converges to the weight-mean iff the invariant reading
is 1-dimensional (the constant), the invariant measure being the contraction/push-forward's `q=+1` fixed
point, with mixing the rate (the spectral gap)." That is a derivation of the field's *shape* — which fixed
point, why it converges (`q=+1`), what 1-dimensionality means (the constant kernel), and what mixing's
rate is (the gap) — not a relabeling. It passes the re-skin guard the way `entropy.md`/`gaussian_clt.md`
did: the model says *which* residue, *why*, and *what fails* (`q=−1`, the ergodic decomposition's split).

**(B) The Lean spine that is actually built (verified ∅-axiom — `tools/scan_axioms.py` re-run this
session):** the *engines and the consolidating ties are real PURE theorems*; what is missing is only the
named ergodic *object* that would weld them.

- **The `q=+1` fixed-point / contraction engine — the SAME object φ, the Gaussian, and ODE flows lean on.**
  `banach_fixed_point` (`BanachFixedPoint.lean:202`): a `Contraction T` has `x* = lim(picard T x0)` as a
  fixed point reached by **none**, with the explicit geometric modulus `picard_cauchy` (`:154`);
  `banach_unique` (`:250`); `Contraction` (`:29`), `picard` (`:33`). This is the engine the invariant
  measure (= `T_*`'s fixed point) and the Birkhoff residue need — *literally the same one*. (12 pure / 0
  dirty, re-scanned.)
- **The convolve-rescale `q=+1` pole already instantiated — the template `T_*` would follow.**
  `ConvolveRescaleContraction.Φ_contraction` (`:345`) proves a concrete reading-of-readings map `Φ` is a
  `Contraction (dyMet L)`; `Φ_picard_cauchy` (`:399`) applies `picard_cauchy`; `center_fixed`/
  `orbit_to_center` (`:419`/`:471`) locate the `q=+1` fixed point reached-by-none. The push-forward
  `T_*` on weights is `Φ` with `T_*` in the role of the doubling map — the engine *fires on a real
  reading-of-readings instance*, exactly the template the invariant measure needs. (20/0, re-scanned.)
- **The Birkhoff average = the LLN sample-mean, ∅-axiom.** The time-average `(1/n)Σ f∘Tⁱ` is the LLN's
  running count/mean: `LLN.countTrue_append` (`:29`, `countTrue(xs++ys)=countTrue xs + countTrue ys` —
  the additive `+↦+` character that makes a running mean accumulate along the orbit), `LLN_unit` (`:58`),
  `bernoulli_LLN_exact` (`:66`, the sample-frequency = expectation identity), `fair_LLN` (`:72`);
  `Expectation.discreteNum_append` (`:62`, linearity). (LLN 7/0.)
- **The time-average's `q=+1` modulus residue — the ergodic theorem's reached-by-none core, ∅-axiom.**
  `CLTLimit.balanced_LLN_modulus` (`:31`): the centered sample-deviation is within `ε` for all `n ≥ N(ε)`
  (witness `N=0` at balance) — the **Cauchy modulus the Birkhoff average converges by**, the limit never
  the operand; `ProbCauchy`/`absDevCross_self` (`CauchyModulus.lean:39`/`:33`), `cltModulus_of_varBound`
  (`CLTGeneric.lean:41`), `genericCLT_balanced_collapse` (`:59`). This is the `measure.md` interior `q=+1`
  modulus residue, here carrying the time-average → space-average convergence. (CLTLimit 4/0.)
- **★ Ergodicity = the dim-1 constant `q=+1` kernel = graph_theory's Laplacian `λ₀=0`, ∅-axiom — the
  leverage tie.** The T-invariant subspace being 1-dimensional (= the constants) is *the same theorem* as
  graph connectivity = `dim ker L = 1`: `GraphLaplacian.pathLaplacian_const_kernel`
  (`GraphLaplacian.lean:127`, PURE): the all-ones/constant vector is in `ker L` (`λ₀=0`);
  `GraphConnectivity.closed_const` (`:61`): connected ⟹ a closed (= invariant-under-the-step) colouring
  is globally **constant**; `closed_root_determines` (`:79`): two closed colourings agreeing at the root
  agree everywhere — i.e. `dim ker = 1`, the invariant reading is pinned by one value, *the constant*.
  This is *exactly* "ergodic ⟺ the invariant functions are constant ⟺ the invariant subspace is
  dimension 1": the Koopman operator's eigenvalue-1 eigenspace = the Laplacian's `λ₀=0` kernel = the
  constants. The brief's central leverage tie is a built PURE theorem at the structural level.
  (GraphConnectivity 8/0, GraphLaplacian 16/0.)
- **★ Mixing = the spectral gap, `q=+1` symmetric-spectrum corner, ∅-axiom.** The transfer/Koopman
  operator's spectrum: `Mat2SymmetricSpectrum.disc_symmetric_nonneg` (`:83`, PURE): a symmetric reading
  has real spectrum (`disc ≥ 0`, the `q=+1` corner — a self-adjoint transfer operator has real
  eigenvalues); `Mat2Spectrum.tr_eq_e1`/`det_eq_e2` (`:115`/`:103`): `tr=Σλ`, `det=Πλ` — the dominant
  eigenvalue is the invariant (eigenvalue 1, the `q=+1` fixed reading = the invariant measure) and the
  **gap to `λ₁` is the mixing rate** = correlation-decay speed = `differential_equations.md`'s
  contraction modulus. (Mat2SymmetricSpectrum 9/0.)
- **`T` = the weight-preserving Aut-element, ∅-axiom skeleton.** The `Aut`-groupoid: `Lens/Unified.lean`
  `lensIso_refl`/`lensIso_symm`/`lensIso_trans` (`:46`/`:50`/`:54`) — the composition-closed family of
  measure-preserving readings is a groupoid; `det_holonomy_eq_one` (`HolonomyLattice.lean:136`) = the
  conserved `q=+1` character `T` must fix (`noether.md`). `PermGroup.lean` gives the `Aut`-as-group
  axioms. The *weight-preservation condition itself* (`measureNum∘T = measureNum`) is the conceptual leg.
- **The Choice-free `q=+1` corner — the measure side, from `measure.md`.** `measureNum`
  (`DyadicMeasure.lean:41`), `measure_union_additive` (`:69`), all PURE; the non-ergodic/non-measurable
  `q=−1` pathologies live at the Choice-built uncountable selector (`object1_not_surjective`), which the
  finite-`List` setting never builds — the ergodic decomposition's `q=−1` extreme points sit at the same
  pole `measure.md` located.

**(C) The remaining gap — predicted-not-built (the honest line, the precise missing leg).** What the
Lean does **NOT** contain — and this is the brief's named target:
- **No `measure-preserving transformation` object** — no `T : MeasurableSet → MeasurableSet` carrying a
  proof `measureNum (T S) = measureNum S`, and no push-forward `T_*` on the weight-readings instantiated
  as a `Contraction`. The `Aut`-groupoid (`LensIso`), the weight (`measureNum`), and the conserved
  character (`det_holonomy_eq_one`) all exist *separately*; the **weld** — an `Aut`-element that fixes the
  measure-character, lifted to `T_*` and shown to be a `Contraction` so `banach_fixed_point` delivers the
  invariant measure — is unbuilt. (Exactly `differential_equations.md`'s unbuilt continuous Picard
  operator and `gaussian_clt.md`'s unbuilt full-profile convolution: engine + template present, the
  field-specific operator conceptual.)
- **No `Birkhoff average` object** — no `Aₙf := (1/n)Σ_{i<n} f∘Tⁱ` defined *along an orbit of `T`*, and
  no theorem "`Aₙf → ∫f dμ` with modulus `N(ε)`". The LLN sample-mean (`countTrue_append`, the running
  count) and its modulus (`balanced_LLN_modulus`) are the *structurally identical* objects — but they run
  over a `List Bool`/balanced sequence, **not over the orbit `f∘Tⁱ` of a transformation `T`**. The
  Birkhoff theorem as one statement ("orbit-mean = weight-mean") is the named missing leg; the calculus
  predicts it is `balanced_LLN_modulus` with `T` supplying the samples, but the substitution is not made.
- **No `ergodic` predicate / no `Koopman`/`transfer` operator object** — "ergodic ⟺ invariant subspace =
  constants" is grounded *by analogy* to `closed_const`/`pathLaplacian_const_kernel` (the graph Laplacian
  constant kernel), but there is no `Ergodic T := (∀f, f∘T = f → f constant)` definition and no Koopman
  operator `Uf := f∘T` whose eigenvalue-1 space is shown to be that kernel. The dim-1-kernel theorem
  exists for the *graph* Laplacian; transporting it to a *Koopman* operator is the unbuilt weld.
- **No `ergodic decomposition` / simplex object** — `convex_duality.md`'s extreme-point/`q=±1` simplex is
  the predicted shape, un-instantiated for invariant measures (the same status `convex_duality.md` reports
  for the Legendre-transform object).
- **No Markov-chain `stationary` distribution** — `MarkovTree` in the repo is the *Diophantine* Markov
  equation `x²+y²+z²=3xyz` (`MarkovTree.lean:30`), **not** a transition matrix; the only `stationary`
  theorems are Ricci-flow fixed points (`flat_torus_stationary`, `ricci_uniform_stationary`). So the
  "Markov stationary vector = the invariant measure" tie is *conceptual* — the `q=+1` fixed-point engine
  is shared, but there is no Markov-chain stationary object to point at. (Honest correction to the brief:
  the Markov stationary leg is a prediction, not a built anchor.)

**Net.** Not collapse-only — it *predicts* all four pillars and *derives* the ergodic theorem's shape
(which fixed point, why `q=+1`, ergodicity = dim-1 constant kernel, mixing = the gap). Not a miss — the
`q=+1` engine (`banach_fixed_point`), its reading-of-readings instantiation (`Φ_contraction`), the
Birkhoff = LLN sample-mean + modulus (`countTrue_append`/`balanced_LLN_modulus`), the ergodicity =
constant-kernel tie (`pathLaplacian_const_kernel`/`closed_const`/`closed_root_determines`), and mixing =
the symmetric spectrum/gap (`disc_symmetric_nonneg`/`tr_eq_e1`) are **all real ∅-axiom theorems**. It is a
**prediction whose engines and consolidating ties are fully built**, one notch below a closed derivation
for the *same reason* as `differential_equations.md`/`gaussian_clt.md`: the field-specific *objects* — a
measure-preserving `T`, the Birkhoff average along its orbit, the Koopman operator, the ergodic-decomposition
simplex — are conceptual welds, not yet instantiated.

## Revelation (collapse + residue-surfaced + forcing — the deepest consolidation)

**The invariant measure, the ergodic theorem, ergodicity, and mixing are ONE `(C, L)` — a weight-bearing
self-applying reading and its `q=±1` residue — resolved by the SAME `banach_fixed_point`/LLN/Laplacian
machinery that resolves φ, the Gaussian, ODE flows, graph connectivity, and the spectrum.** Five fields
collapse onto two invariants. This is collapse + residue-surfaced + forcing, three at once:

1. **Collapse across the ergodic dictionary AND across five prior fields.** A *measure-preserving `T`*
   (weight-fixing `Aut`-element), an *invariant measure* (`T_*`'s `q=+1` fixed point), the *ergodic
   theorem* (the time-average's `q=+1` Birkhoff residue = `∫f dμ`), *ergodicity* (the dim-1 constant
   kernel), and *mixing* (the spectral gap) are not five concepts — they are one weight-bearing
   self-applying reading read at settings of the `q=±1` bit, the resolution dial, and the spectrum. And
   the invariant measure is *literally the same object* as φ (`golden_ratio.md`), the Gaussian
   (`gaussian_clt.md`), the ODE solution (`differential_equations.md`), and — by the constant-kernel tie —
   graph connectivity's `λ₀=0` fixed vector (`graph_theory.md`). The ergodic theorem and the LLN are the
   *same theorem* (a running mean's `q=+1` Cauchy residue, `balanced_LLN_modulus`) aimed at two questions
   (does a sample mean converge / does an orbit mean converge).

2. **Residue surfaced — "time-average = space-average" is not an equality of two pre-existing numbers,
   it is one `q=+1` residue read two ways.** The space-average `∫f dμ` is the reached-by-none fixed point
   of the orbit-means `Aₙf`, computed by a modulus, the limit never the operand — `golden_ratio.md`'s
   "Limit/infinity deified" failure stated positively, here for the Birkhoff average. The orbit-mean
   (dynamic) and the integral (frozen) are `golden_ratio.md`'s `Pⁿ→φ` vs `P(φ)=φ` simultaneity:
   "time-average = space-average" *is* `dynamic = frozen` for the weight-reading's `q=+1` residue.

3. **Forcing — the `q=±1` bit forces ergodic vs non-ergodic, and the dimension of the invariant kernel
   IS that bit.** Whether the invariant reading is 1-dimensional — the constant, `q=+1`, ergodic, the
   orbit equidistributes, `closed_const` — or splits into independent invariants — `q=−1`-flavoured, the
   ergodic decomposition's simplex of extreme measures, `dim ker > 1`, `graph_theory.md`'s disconnected
   graph — is the *same* collapse-to-dimension-1 the calculus already proves for the graph Laplacian
   (`closed_root_determines`). Ergodicity is not an add-on property; it is the `q=+1` constant-kernel
   collapse, identical to connectivity. Mixing is then the *rate* of that collapse = the spectral gap
   below the dominant eigenvalue 1 (`disc_symmetric_nonneg` real spectrum + the `λ₀=1`→`λ₁` gap).

**THE CONSOLIDATION (the brief's central question): the `q=+1` fixed-point residue now spans FIVE
fields, and ergodic theory is where they meet.** The single `banach_fixed_point`/LLN-modulus/constant-kernel
machinery is the residue-resolver for:

| | what iterates / collapses | `q=+1` fixed point / residue | Lean engine |
|---|---|---|---|
| `golden_ratio.md` (φ) | Möbius `T` on `(p,q)` | φ | `mobius_iteration_master` (built) |
| `gaussian_clt.md` (Gaussian) | `Φ`=convolve⋆rescale on a weight | the Gaussian profile | `banach_fixed_point`+`Φ_contraction` (built) |
| `differential_equations.md` (ODE) | Picard step on a function | the solution curve | `banach_fixed_point`+`picardIterate`/`orbit_eq_iter` (built) |
| `graph_theory.md` (Laplacian) | the diffusion reading `I−L` | the constant `λ₀=0` kernel | `pathLaplacian_const_kernel`/`closed_const` (built) |
| **`ergodic_theory.md`** | **`T_*` on a weight (= the measure)** | **the invariant measure + ∫f dμ (Birkhoff)** | **engine built (`banach_fixed_point`/`balanced_LLN_modulus`/`closed_const`); `T_*`/`Aₙ` object NOT built** |

So **YES** — the invariant measure = the `q=+1` fixed point of `T_*` (the Markov/Gaussian/Banach fixed
point, engine shared); the ergodic theorem time=space-average = the `q=+1` converging Birkhoff residue
(the LLN structure, `balanced_LLN_modulus`); **ergodicity = invariant functions constant = the dim-1
`q=+1` kernel = the SAME constant as `graph_theory.md`'s Laplacian `λ₀=0`** (`pathLaplacian_const_kernel`/
`closed_const`/`closed_root_determines`, all PURE); mixing = the transfer operator's contraction /
spectral gap (`disc_symmetric_nonneg`/`tr_eq_e1`). Ergodic theory **consolidates `gaussian_clt` +
`differential_equations` + `measure` + `graph_theory` + `spectral`** at one `q=+1` fixed point — the
notebook's widest single collapse. The precise missing leg is the named ergodic *object*: a
measure-preserving `T` (= weight-fixing `Aut`-element with `T_*` a `Contraction`), the Birkhoff average
`Aₙf` along its orbit, the Koopman operator, and the ergodic-decomposition simplex.

## Note for the technique — does ergodic theory force a NEW construct?

**No new primitive — EXTEND, the strongest consolidation in the notebook.** This decomposition adds
nothing to model v7.1; it *uses* existing slots and shows five `q=+1` fields are one fixed point:
- *measure-preserving `T`* = `groups.md`'s `Aut` ∩ `measure.md`'s weight ∩ `noether.md`'s `q=+1`
  invariant (no new slot — an intersection of three existing readings);
- *invariant measure* = `golden_ratio.md`'s `q=+1` fixed-point rule applied to the push-forward `T_*`
  (the reading-of-readings level, `gaussian_clt.md`);
- *Birkhoff average* = the LLN sample-mean (`countTrue_append`'s `+↦+` running character) at residue
  resolution (`derivative.md`'s dial); *space-average* = its `q=+1` modulus residue (`measure.md`'s
  interior `q=+1`);
- *ergodicity* = the dim-1 constant kernel — the SAME `closed_const`/`pathLaplacian_const_kernel`
  collapse as `graph_theory.md`'s connectivity (this is the load-bearing tie: ergodic = connected =
  `dim ker = 1` = the constant `q=+1` fixed reading);
- *mixing* = `differential_equations.md`'s contraction + `spectral.md`'s gap below eigenvalue 1;
- *ergodic decomposition* = `convex_duality.md`'s extreme-point/`q=±1` simplex.

The one sharpening for the technique: **"ergodic vs non-ergodic" IS the `dim ker = 1` vs `dim ker > 1`
bit of the invariant reading — the SAME collapse-to-the-constant the calculus already proves for the
graph Laplacian.** The Koopman/transfer operator's eigenvalue-1 eigenspace and the Laplacian's `λ₀=0`
kernel are one object; the ergodic theorem and the LLN are one `q=+1` modulus residue; the invariant
measure and the Gaussian/φ/ODE-solution are one `banach_fixed_point` fixed point. Ergodic theory is the
field where the calculus's `q=+1` corner is at its widest — five prior decompositions resolved by one
engine. The calculus thus *predicts* the ergodic theorem (orbit-mean = weight-mean as the residue
surfacing) and the ergodic/non-ergodic dichotomy (the constant-kernel collapse) from the model's slots,
not from measure-theoretic analysis added on top.

## Verified Lean anchors (file:theorem:line — all grep-verified; purity by `tools/scan_axioms.py`, re-run this session)

| Leg | Theorem (file:name:line) | Status |
|---|---|---|
| `q=+1` fixed point = modulus residue (the **engine** — shared with φ, Gaussian, ODE) | `Lib/Math/Analysis/BanachFixedPoint.lean : banach_fixed_point` (`:202`), `picard_cauchy` (`:154`), `banach_unique` (`:250`), `Contraction` (`:29`), `picard` (`:33`) | ∅-axiom ✓ (12 pure / 0 dirty) |
| the engine instantiated on a reading-of-readings (the **template** `T_*` would follow) | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean : Φ_contraction` (`:345`), `Φ_picard_cauchy` (`:399`), `center_fixed`/`orbit_to_center` (`:419`/`:471`), `dyMet` (`:311`) | ∅-axiom ✓ (20/0) |
| **Birkhoff average = the LLN sample-mean** (running count, `+↦+` character) | `Lib/Math/Probability/Limit/LLN.lean : countTrue_append` (`:29`), `LLN_unit` (`:58`), `bernoulli_LLN_exact` (`:66`), `fair_LLN` (`:72`); `Probability/Foundation/Expectation.lean : discreteNum_append` (`:62`) | ∅-axiom ✓ (LLN 7/0) |
| **time-avg → space-avg = the `q=+1` modulus residue** (reached-by-none) | `Lib/Math/Probability/Limit/CLTLimit.lean : balanced_LLN_modulus` (`:31`); `Probability/Bridge/CauchyModulus.lean : ProbCauchy` (`:39`), `absDevCross_self` (`:33`); `Probability/Limit/CLTGeneric.lean : cltModulus_of_varBound` (`:41`, a `def`), `genericCLT_balanced_collapse` (`:59`) | ∅-axiom ✓ (CLTLimit 4/0) |
| **★ ergodicity = the dim-1 constant `q=+1` kernel = graph_theory's Laplacian `λ₀=0`** (the leverage tie) | `Lib/Math/NumberSystems/Real213/Mat2/GraphLaplacian.lean : pathLaplacian_const_kernel` (`:127`); `Lib/Math/Combinatorics/GraphConnectivity.lean : closed_const` (`:61`), `closed_root_determines` (`:79`) | ∅-axiom ✓ (GraphLaplacian 16/0, GraphConnectivity 8/0) |
| **mixing = the spectral gap, `q=+1` symmetric-spectrum corner** (eigenvalue 1 = invariant; gap = rate) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean : disc_symmetric_nonneg` (`:83`); `Mat2/Mat2Spectrum.lean : tr_eq_e1` (`:115`, `tr=Σλ`), `det_eq_e2` (`:103`, `det=Πλ`) | ∅-axiom ✓ (Mat2SymmetricSpectrum 9/0) |
| `T` = the weight-fixing `Aut`-element (the groupoid + conserved character) | `Lens/Unified.lean : lensIso_refl/symm/trans` (`:46`/`:50`/`:54`); `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean : det_holonomy_eq_one` (`:136`); `Lib/Math/Algebra/Linalg213/PermGroup.lean` (Aut-as-group) | ∅-axiom ✓ (prior) |
| measure = weight, Choice-free `q=+1` corner (the measure side, from `measure.md`) | `Lib/Math/Analysis/Measure/DyadicMeasure.lean : measureNum` (`:41`), `measure_union_additive` (`:69`); `q=−1` escape `Lens/Foundations/FlatOntologyClosure.lean : object1_not_surjective` (`:61`) | ∅-axiom PURE ✓ (prior, `measure.md`) |
| flow = the reading iterated by the count (`orbit = iter`) | `Meta/OrbitIsIter.lean : orbit_eq_iter` (`:42`) | ∅-axiom ✓ (prior, `differential_equations.md`) |

**Conceptual-only / absent legs (honest — predicted, NOT built; the precise missing leg):**
- **No measure-preserving-transformation object** — no `T` with a proof `measureNum (T S) = measureNum S`,
  and no push-forward `T_*` instantiated as a `Contraction`. The `Aut`-groupoid (`LensIso`), the weight
  (`measureNum`), and the conserved character (`det_holonomy_eq_one`) exist *separately*; the weld is the
  unbuilt leg (the analogue of `differential_equations.md`'s unbuilt continuous Picard operator).
- **No Birkhoff-average object** — no `Aₙf := (1/n)Σ f∘Tⁱ` *along an orbit of `T`*, and no theorem
  "`Aₙf → ∫f dμ`". The LLN sample-mean (`countTrue_append`) + modulus (`balanced_LLN_modulus`) are the
  structurally identical objects but run over a `List`/balanced sequence, not over `f∘Tⁱ`. The Birkhoff
  theorem as one statement is the named missing leg.
- **No `Ergodic` predicate / no Koopman/transfer operator object** — "ergodic ⟺ invariant subspace =
  constants" is grounded *by the graph-Laplacian analogy* (`closed_const`/`pathLaplacian_const_kernel`),
  but there is no `Ergodic T`/`Koopman U f := f∘T`/eigenvalue-1-eigenspace object.
- **No ergodic-decomposition simplex object** — `convex_duality.md`'s extreme-point `q=±1` simplex,
  un-instantiated for invariant measures.
- **No Markov-chain `stationary` distribution** — `MarkovTree` (`MarkovTree.lean:30`) is the *Diophantine*
  Markov equation `x²+y²+z²=3xyz`, NOT a transition matrix; `stationary` exists only as Ricci-flow fixed
  points (`flat_torus_stationary`, `ricci_uniform_stationary`). The "Markov stationary = invariant measure"
  tie is conceptual (shared `q=+1` engine), not a built anchor — honest correction to the brief.
- **No ergodic/Birkhoff/Koopman/measure-preserving declaration anywhere in `lean/E213`** (grep:
  0 hits for `ergodic`, `Birkhoff`, `measurePreserving`, `Koopman`, `transferOperator`). The field's
  *objects* are absent; the calculus's *engines and consolidating ties* are present and PURE — the
  `knots.md`/`model_theory.md` profile (predicted structure is the deliverable; the named object is open).

> **Open Lean target the calculus names precisely** (a promotion target, parallel to
> `gaussian_clt.md`/`differential_equations.md`): *define a measure-preserving `T` as a weight-fixing
> `Aut`-element, lift it to `T_*` on `DyadicMeasure`-weights, show `T_*` is a `Contraction` (in
> `BanachFixedPoint`'s sense) and apply `banach_fixed_point` to obtain the invariant measure as
> `lim(picard T_* μ0)`; define the Birkhoff average `Aₙf := (1/n)Σ f∘Tⁱ` and prove `Aₙf → ∫f dμ` with
> modulus `balanced_LLN_modulus`; define the Koopman operator and prove its eigenvalue-1 eigenspace =
> the constants iff `dim ker = 1` via `closed_root_determines` — the ergodic theorem + ergodicity as the
> `q=+1` Birkhoff/constant-kernel residue, in three theorems.* This is the **fifth** instantiation of the
> `q=+1` engine after φ, the Gaussian, the ODE flow, and the graph Laplacian, and would close ergodic
> theory the way `ConvolveRescaleContraction` closed the CLT *leg*.

> Axiom-purity note: every cited engine/tie row was re-run through `tools/scan_axioms.py` from repo root
> this session and reports the pure/dirty counts shown (BanachFixedPoint 12/0, ConvolveRescaleContraction
> 20/0, LLN 7/0, CLTLimit 4/0, GraphLaplacian 16/0, GraphConnectivity 8/0, Mat2SymmetricSpectrum 9/0).
> `measure.md`'s rows rest on its fresh scan (35/0). The `Aut`/holonomy rows rest on in-file docstrings.
