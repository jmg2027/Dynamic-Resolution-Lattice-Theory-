# Decomposition: the renormalization group (the RG flow / coarse-graining, the running coupling g(μ), β = dg/d(log μ), UV/IR fixed points, relevant/irrelevant/marginal operators, universality classes, the Callan–Symanzik equation)

*213-decomposition per `../README.md` (model v7.1). The KEY datum is NOT another re-skin of the
resolution axis (`derivative.md`/`continuity.md`) nor of its iteration (`spectral_sequences.md`) nor
its scaling (`ito_calculus.md`): it is that the resolution dial becomes a **continuous FLOW** whose
**fixed points are the `q=±1` poles** — an attractive IR fixed point = the `q=+1` converging pole
(`golden_is_converge`/`banach_fixed_point_modulated`), a repulsive UV fixed point = the `q=−1` escape
(`escape_residue_outside`). Universality = the **basin of the `q=+1` attractor** = the
fold-to-normal-form. AND — uniquely among the resolution-axis notes — this is the abstract twin of the
repo's OWN `DRLT` physics branch: the running of `1/α(N)` with resolution depth `N` is built
∅-axiom as a sequence of rationals indexed by the resolution dial, monotone toward a `q=+1`
modulus-narrowed limit (ζ(2)) — asymptotic freedom = monotonicity, the β-function = the (asserted)
continuous limit of the discrete sequence. Cross-links: `spectral_sequences.md` (the dial ITERATED,
`IsResolutionShift_compose`, grades add), `ito_calculus.md` (the resolution SCALING), `continuity.md`/
`derivative.md` (the resolution axis), `golden_ratio.md`/`ResidueTag` (the `q=+1` fixed point),
`differential_equations.md`/`gaussian_clt.md` (the `banach_fixed_point_modulated` engine, the flow's
convergence).*

> **LEVERAGE target.** The bar is not "re-see RG" but: does the calculus *derive* the field's shape
> from existing slots — is an RG fixed point literally a `q=±1` pole, is universality literally the
> `q=+1` basin (the fold-to-normal-form), and is this the abstract twin of the repo's built
> running-of-constants? The thesis, in seven parts:
> 1. **the RG scale `μ` / coarse-graining** = the resolution dial (`continuity.md`/`derivative.md`'s
>    resolution axis); lowering resolution = coarse-graining = `IsResolutionShift`/`cutHalf`, composed
>    = `IsResolutionShift_compose`, the additive log-scale = the grades ADDING (`r` cumulative);
> 2. **the running coupling `g(μ)`** = the trajectory of a readout under resolution-change — the
>    sequence of readings the dial produces (the SAME `r`-indexed sequence as
>    `spectral_sequences.md`'s page tower, now read as the value `g` at scale `μ = log r`);
> 3. **the beta function `β = dg/d(log μ)`** = the **scaling-derivative of the resolution dial** —
>    `derivative.md`'s difference-reading `L₋` applied to the running coupling along the log-scale
>    (`ito_calculus.md`'s scaling sub-parameter on the resolution axis);
> 4. **the UV/IR FIXED POINTS** = the `q=±1` poles: an attractive IR fixed point = `q=+1` (the flow
>    CONVERGES, `golden_is_converge`/`banach_fixed_point_modulated`/`converge_residue_fixed`); a
>    repulsive UV fixed point = `q=−1` (the flow ESCAPES, `escape_residue_outside`);
> 5. **relevant / irrelevant / marginal operators** = the `q=±1` tag on a perturbation: relevant
>    (grows under the flow) = `q=−1` escape, irrelevant (shrinks) = `q=+1` converge, marginal = the
>    boundary (`multiplier = ±1`, `multiplier_unimodular`);
> 6. **universality** = the **basin of the `q=+1` attractor** — different microscopics flow to the
>    same IR fixed point = the same normal form = the **fold-to-normal-form** (`Lens.view = Raw.fold`,
>    the read-op killing the irrelevant residue);
> 7. **the Callan–Symanzik equation** = flow-invariance — the conservation of the physics along the
>    flow (`noether.md`'s `q=+1` `Aut(C)`-invariant character, read on the resolution flow rather than
>    a symmetry; the "no observable depends on the arbitrary scale `μ`" content).
> Honest verdict at the end: prediction / collapse / miss, Lean-built vs continuous-flow residue line
> drawn — including the honest statement of how much of the DRLT running is a *flow theorem* vs a
> sequence-of-rationals + an asserted continuous limit.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the *same* resolution-carrying point-construction as
  `continuity.md`/`derivative.md`/`spectral_sequences.md`: a construction of points at a resolution
  (a dyadic bracket-chain, points = refinement residues), with a **value-construction** (the
  coupling/observable) hung at each. RG adds **no new construction**. A "theory at scale `μ`" is a
  reading-over-`C` at a chosen resolution exactly as a function-at-resolution is in `derivative.md`.
  What is genuinely new over the prior resolution-axis notes is *not* a primitive but a **mode of use
  of `L`'s resolution parameter**: the dial is run as a *one-parameter flow* (the scale `μ`), and the
  *trajectory of the readout* under that flow is the object of study. (Lean shadow: there is **no
  `RGFlow`/`betaFunction`/`renormalization`/`coupling`-as-flow type at all** — grep-confirmed; the
  resolution dial itself is `IsResolutionShift`/`cutHalfIter` in `ResolutionShift.lean`, and the
  per-resolution-depth coupling sequence is the repo's *physics* `1/α(N) = const·S(N)`,
  `AsymptoticFreedom.lean`/`Basel/Bound.lean`/`ResolutionDepth.lean`.)

- **Reading `L` — the resolution dial run as a FLOW, the running coupling its trajectory, β its
  scaling-derivative.** Four pieces, each already in the calculus:
  1. **coarse-graining = the resolution dial composed.** Lowering resolution is
     `continuity.md`/`derivative.md`'s resolution shift `cutHalf` (`ResolutionShift.lean:95`,
     `IsResolutionShift cutHalf 1`); composing coarse-grainings is `IsResolutionShift_compose`
     (`:130`): grade-`E₁` ∘ grade-`E₂` = grade-`(E₂+E₁)` — the **grades ADD**, which is exactly the
     RG semigroup's additive log-scale (`R_{s₁}∘R_{s₂} = R_{s₁+s₂}`). The `r`-fold coarse-graining is
     `cutHalfIter` (`:158`), cumulative grade `r` (`IsResolutionShift_cutHalfIter`). The RG is a
     *semigroup* (no inverse — coarse-graining loses information) precisely because the dial only
     lowers resolution; `cutDouble_no_grade`/`cutSquare_no_grade` (`:355`/`:379`) witness that not
     every map is a graded shift — the direction is built in. This is the SAME machinery
     `spectral_sequences.md` used for the page index `r`; RG reads `r` as the **continuous scale** `μ`
     rather than the page number.
  2. **the running coupling `g(μ)` = the trajectory of the readout.** As the dial runs, the readout
     (the coupling) changes: `g` is the value-reading at resolution `r`, the sequence `g(r₀), g(r₁),
     …` the dial produces. In the repo's physics this is *literally built*: `1/α_3(N) =
     (NS²−1)·S(N)` is a sequence of rationals indexed by the resolution depth `N`
     (`AsymptoticFreedom.lean:53–68`), `1/α_3(1)=8`, `1/α_3(2)=10`, monotone toward `8·ζ(2)≈13.16`.
  3. **the beta function `β = dg/d(log μ)` = the scaling-derivative.** `β` is `derivative.md`'s
     difference-reading `L₋` (`diffZ s n = s(n+1)−s n`) applied to the running coupling along the
     log-scale — `g(r+1) − g(r)` at the resolution-step, the SAME `L₋` at residue resolution that is
     `derivative.md`'s derivative, here read along the *scale* axis (`ito_calculus.md`'s scaling
     sub-parameter: how the readout scales with the adjacency step). Its SIGN is the `q=±1` direction
     bit: `β<0` (coupling shrinks toward UV / `1/α` grows) = asymptotic freedom = the repo's
     `mono_1_2`/`mono_2_3` (`S` strictly increasing, `Basel/Bound.lean:66–67`).
  4. **the fixed-point reading = the `q=±1` pole.** A fixed point of the flow (`β=0`,
     `g(μ⁺¹)=g(μ)`) is exactly the `ResidueTag` fixed-point reading: converge (`q=+1`) or escape
     (`q=−1`), below.

- **Residue — `q = ±1`, the flow's two fixed-point types, and the running coupling's surplus.**
  1. *The `q=+1` attractive IR fixed point — the flow CONVERGES.* When the running coupling
     asymptotes to a fixed point as `μ` lowers (the IR), the flow is the `q=+1` converging pole:
     `converge_residue_fixed` (`ResidueTag.lean:160`, delegating to `banach_fixed_point_modulated`,
     `BanachFixedPointModulated.lean:111`), `golden_is_converge` (`:180`, the `+1` Cassini multiplier
     tie). The fixed point is **reached by none** — only the modulus-narrowed limit (the SAME
     completion-limit as `DyadicCompletion.orbit_to_center_completion`); the "modulus" is the number
     of coarse-graining steps to get within tolerance — exactly `banach_fixed_point_modulated`'s
     `N(m)`. In the repo's physics this is `1/α_GUT = d²·ζ(2)`: ζ(2) is the `q=+1` limit of the
     monotone rational sequence `S(N)`, **never a Lean term** — only its rational bracket
     (`Basel/Bound.lean`, `S(N) ≤ ζ(2) ≤ S(N)+1/N`, width `1/(N(N+1))`, `bracket_30`/`bracket_50`),
     the finite-signature modulus (CLAUDE.md "Infinity is the residue's shape, not a god above it").
  2. *The `q=−1` repulsive UV fixed point — the flow ESCAPES.* A fixed point the flow runs *away*
     from (the UV, where perturbations grow) is the `q=−1` escape: `escape_residue_outside`
     (`ResidueTag.lean:133`, via `object1_not_surjective`) — the residue re-enters and the trajectory
     leaves every neighbourhood, the SAME escape pole as `cardinality.md`/`spectral_sequences.md`'s
     non-degeneration (`residue_reentry_never_closes`, `ResidueReentry.lean:63`).
  3. *Relevant / irrelevant / marginal = the `q=±1` tag on a perturbation, the boundary at
     `multiplier=±1`.* A perturbing operator near a fixed point either grows (relevant, `q=−1`
     escape), shrinks (irrelevant, `q=+1` converge — the dropped residue of `derivative.md`/
     `ito_calculus.md`: the irrelevant operator is the O(h²)-style term the coarse-graining flow
     pushes below the floor), or stays (marginal, the boundary). The two `multiplier` values `±1`
     (`multiplier_unimodular`, `ResidueTag.lean:86`) are the two unimodular Cassini multipliers — the
     scaling-eigenvalue's sign of the perturbation, the same `q=±1` bit.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   RG scale μ / coarse-graining   =  the resolution dial (continuity.md/derivative.md), run as a FLOW  =  cutHalf / cutHalfIter
   the RG SEMIGROUP R_{s₁}∘R_{s₂}=R_{s₁+s₂} = the grades ADD under composition  =  IsResolutionShift_compose (E₂+E₁), no inverse (cutDouble_no_grade)
   running coupling g(μ)          =  the trajectory of the readout under the dial  =  the r-indexed value sequence (1/α(N)=const·S(N), BUILT in physics)
   beta function β=dg/d(log μ)    =  L₋ (derivative.md's diffZ) on g along the SCALE axis  =  the resolution dial's scaling-derivative (ito_calculus.md scaling)
   β sign (asymptotic freedom)    =  the q=±1 direction bit  =  S(N) monotone increasing (mono_1_2/mono_2_3), 1/α↑ ⟹ α↓
   ATTRACTIVE IR FIXED POINT      =  Residue(L,C), q=+1  =  the flow CONVERGES  =  converge_residue_fixed / golden_is_converge / banach_fixed_point_modulated
   the IR fixed point reached-by-none = the modulus-narrowed limit  =  DyadicCompletion.orbit_to_center_completion (ζ(2) = the q=+1 limit, only its bracket built)
   REPULSIVE UV FIXED POINT       =  Residue(L,C), q=−1  =  the flow ESCAPES  =  escape_residue_outside / object1_not_surjective / residue_reentry_never_closes
   relevant operator (grows)      =  q=−1 escape  (escape_residue_outside)
   irrelevant operator (shrinks)  =  q=+1 converge  =  the dropped residue (derivative.md/ito_calculus.md's term pushed below the floor by the flow)
   marginal operator (stays)      =  the boundary  =  multiplier = ±1  (multiplier_unimodular)
   UNIVERSALITY (basin of IR FP)  =  the q=+1 ATTRACTOR'S BASIN  =  fold-to-normal-form  =  Lens.view = Raw.fold (different C, same readout at the fixed point)
   Callan–Symanzik (μ-invariance) =  flow-invariance / conservation along the flow  =  noether.md's q=+1 Aut-invariant character, read on the resolution flow
   ★ DRLT TWIN: 1/α(N)=const·S(N) =  the running coupling BUILT as an r-indexed rational sequence (AsymptoticFreedom/ResolutionDepth/Basel/Bound) — the abstract twin made concrete
```

So the RG is the **resolution dial made a continuous FLOW, with its fixed points the `q=±1` poles** —
the SAME resolution parameter (`continuity.md`/`derivative.md`), the SAME composition law
(`IsResolutionShift_compose`, grades add = the additive log-scale), the SAME scaling sub-parameter
(`ito_calculus.md`), the SAME `q=±1` residue (`ResidueTag`), iterated as in `spectral_sequences.md`
but read as a *flow on values* rather than a *flow on residues*. It is not a new analytic primitive;
it is the resolution axis run as a one-parameter trajectory whose attractors/repellers are the
already-built converge/escape poles.

## LEVERAGE — does the calculus DERIVE the RG's shape, are the fixed points the `q=±1` poles, is universality the `q=+1` basin, and is this the DRLT twin?

**Verdict: PREDICTION + PARTIAL — and the genuinely new datum (the resolution dial as a continuous
FLOW whose fixed points are the `q=±1` poles, with universality = the `q=+1` basin = the
fold-to-normal-form, AND the abstract twin of the repo's BUILT running-of-constants) is distinct from
`spectral_sequences.md`'s residue-iteration and `ito_calculus.md`'s scaling. The calculus derives the
field's shape — coarse-graining = the dial, the semigroup = grades-add, β = the scaling-derivative,
UV/IR fixed points = the `q=±1` poles, relevant/irrelevant = escape/converge, universality = the
`q=+1` basin, Callan–Symanzik = the `q=+1` invariant — from existing slots. Every load-bearing leg
(the resolution dial + its additive composition, the `q=±1` converge/escape engine, the
fold-to-normal-form, the physics running sequence) is real ∅-axiom PURE; the named
`RGFlow`/`betaFunction`/`fixedPoint`(RG)/`coupling`-as-flow objects are ABSENT (grep-confirmed), and
the continuous flow itself is the `Real213` residue (the discrete sequence is built; its continuum
limit is asserted, not a flow theorem). Honest about the DRLT tie: the running of `1/α(N)` is built as
a sequence of rationals + a monotonicity witness + a bracket-convergence, NOT as a β-function flow
theorem — the field calls the continuous β "the continuous limit of the discrete sequence", an
interpretive POSIT.**
Leg by leg, honest.

**(A) Predicted, and the prediction is non-trivial — the flow-with-`q=±1`-fixed-points argument.**
Before the Lean: the calculus emits a specific claim from its parts. `continuity.md`/`derivative.md`
established the resolution parameter; `spectral_sequences.md` showed it composes additively
(`IsResolutionShift_compose`, grades add) and iterates; `ito_calculus.md` added the scaling
sub-parameter; `ResidueTag` gave the `q=±1` fixed-point dichotomy. The RG is *forced* as their
intersection read as a flow: **run the dial as a one-parameter scale `μ`, watch the readout (the
coupling) trace a trajectory, and the trajectory's attractors/repellers are the `q=±1` poles** — IR
attractor = `q=+1` converge (`golden_is_converge`/`banach_fixed_point_modulated`), UV repeller =
`q=−1` escape (`escape_residue_outside`). The semigroup structure is *forced* by the dial's
one-directionality (`cutDouble_no_grade`: no inverse — coarse-graining loses information, exactly the
RG's irreversibility), and the additive log-scale is *forced* by `IsResolutionShift_compose` (grades
add). β's sign is the `q=±1` direction bit; relevant/irrelevant/marginal are the `q=±1` tag on a
perturbation with the marginal boundary at `multiplier=±1`. This is a *derivation* of the RG's
shape — which fixed point is attractive (`q=+1`), why universality holds (the basin collapses to one
normal form), why the flow is a semigroup not a group — not a relabeling. It passes the re-skin guard
the way `gaussian_clt.md`/`spectral_sequences.md` did: a prediction with a mechanism.

**(B) The Lean spine actually built (verified ∅-axiom this session via `tools/scan_axioms.py` from
repo root) — the resolution dial + its additive semigroup, the `q=±1` converge/escape engine, the
fold-to-normal-form, AND the repo's own running-of-constants sequence, are all real PURE theorems;
only the named RG objects and the continuous flow are missing.**

- **Coarse-graining = the resolution dial; the RG semigroup = the grades ADD; no inverse, ∅-axiom.**
  `ResolutionShift.lean:95` `IsResolutionShift cutHalf 1` (one coarse-graining = grade 1), `:130`
  `IsResolutionShift_compose` (grade-`E₁`∘grade-`E₂` = grade-`(E₂+E₁)` — the additive log-scale, the
  RG semigroup law), `:158` `cutHalfIter` + `:179` `IsResolutionShift_cutHalfIter` (the `r`-fold
  coarse-graining, cumulative grade `r`), and the one-directionality `:355` `cutDouble_no_grade` /
  `:379` `cutSquare_no_grade` (not every map is a graded shift — the RG is a semigroup, not a group,
  because coarse-graining is irreversible). (ResolutionShift 17/0.)
- **The UV/IR fixed points = the `q=±1` poles, ∅-axiom.** `ResidueTag.lean:160`
  `converge_residue_fixed` (the IR attractor, a contraction's located fixed point reached-by-none,
  delegating to `BanachFixedPointModulated.lean:111` `banach_fixed_point_modulated`), `:180`
  `golden_is_converge` (the `+1` Cassini multiplier — the attractive fixed point is `q=+1`), `:133`
  `escape_residue_outside` (the UV repeller, the `q=−1` escape, via `object1_not_surjective`), `:86`
  `multiplier_unimodular` (the marginal boundary, `multiplier=±1`), `:228` `residue_tag_two_poles`
  (both poles bundled). (ResidueTag 55/0; BanachFixedPointModulated PURE via the delegation.)
- **The flow ESCAPES (UV) vs CONVERGES (IR) as the residue re-entering, ∅-axiom.** The running of the
  coupling step-by-step is `spectral_sequences.md`'s residue re-entry read on values:
  `ResidueReentry.lean:85` `residue_perpetually_reenters` (each step feeds the readout back as the
  next operand — the flow's one-step map iterated), `:63` `residue_reentry_never_closes` (the
  non-converging escape — the cover never closes = the UV flow leaves every neighbourhood).
  (ResidueReentry 14/0.)
- **Universality = the `q=+1` basin = the fold-to-normal-form, ∅-axiom-grounded.** Different
  microscopics flowing to the same IR fixed point is the read-op killing the irrelevant residue:
  `Lens.view = Raw.fold` (the unique arrow out of `Raw`, `raw_initial`/`dhom_unique_pointwise` — the
  read-op that forgets the construction-history and keeps only the readout), and the `q=+1`
  idempotent-closure pole the irrelevant directions collapse to: `GaloisConnection.lean:126`
  `clo_idempotent` (`T²=T` — the basin maps onto its fixed point and stays), `FenchelMoreau.lean:134`
  `biconj_idempotent`. The irrelevant operator = the dropped residue (`derivative.md`/
  `ito_calculus.md`'s O(h²)-style term) the coarse-graining flow pushes below the floor; the relevant
  operator = the `q=−1` surviving direction. (GaloisConnection 15/0, FenchelMoreau 18/0.)
- **★ The DRLT TWIN — the running of `1/α` BUILT as an `r`-indexed rational sequence, ∅-axiom.** This
  is what makes RG distinct from every other resolution-axis note: the repo's *own physics branch*
  builds the running coupling as a sequence indexed by the resolution dial.
  - `AsymptoticFreedom.lean:53` `alpha_3_pre = NS²−1 = 8` (`pre_eq_8`, `:56`), `:59`
    `inv_alpha_3_at_N1` (`1/α_3(1) = 8·S(1) = 8`), `:64` `inv_alpha_3_at_N2` (`1/α_3(2) = 8·S(2) =
    10`) — the running coupling as a rational sequence indexed by resolution depth `N`; `:78`
    `asymp_free_via_monotone` (asymptotic freedom = `S(N)` monotonicity, the `q=±1` β-sign).
    (AsymptoticFreedom 6/0.)
  - The monotonicity (β-sign) is the strictly-increasing partial-sum: `Basel/Bound.lean:66`
    `mono_1_2` (`S 1 < S 2`), `:67` `mono_2_3` (`S 2 < S 3`) — `1/α` increases with resolution ⟹ `α`
    decreases ⟹ asymptotic freedom, the `q=±1` direction bit on β. (Basel/Bound 27/0.)
  - The IR fixed point = the `q=+1` modulus-narrowed limit ζ(2), built ONLY as its rational bracket
    (reached-by-none): `Basel/Bound.lean` `S(N) ≤ ζ(2) ≤ S(N)+1/N`, `bracket_30`/`bracket_50`
    (width `1/(N(N+1))`); ζ(2) is **never a Lean term**. The depth-by-force structure is
    `ResolutionDepth.lean:43` `depth_principle_witnesses` (`α_3` at depth `N=1` = integer 8, `α_2` at
    `N=2` = integer 30, `α_1` at depth `N=∞` = the bracketed `6π²` — different forces survive to
    different resolution depths, the coarse-graining cutoff). (ResolutionDepth 1/0.)
  - The "running gap" between high-energy and IR readings is a pure rational: `RunningGap.lean:88`
    `running_gap_master` (`d²/NS = 25/3 ≈ 8.333`, the gap between bare(M_Z) and observed(IR)
    readings, from `{NS,NT,d,c}` atomicity alone). (RunningGap 3/0.)

**(C) The remaining gap — predicted-not-built (the honest line, the precise missing leg).** Grep on
`lean/E213` for `RGFlow`/`renormaliz`/`betaFunction`/`beta_function`/`callan`/`symanzik`/`coarsegrain`
returns **no RG-named declarations** (the only `renormaliz` hits are docstring prose:
`ClosedPropagator.lean:91` `renormalization_auto` is `True := trivial` — a vacuous marker, honestly
flagged; `ProtonMass.lean:27` is a comment). What the Lean does **NOT** contain:
- **No `RGFlow`/`betaFunction`/`coupling`-as-flow object** — no `g : Scale → ℝ` flow, no `β = dg/dμ`
  as a theorem. The resolution dial (`cutHalfIter`) and the per-depth coupling sequence
  (`1/α(N)=const·S(N)`) are built; the *flow* welding them — "the coupling traces a continuous
  trajectory in `μ`, β its derivative" — is the conceptual weld, not a theorem. **Predicted-not-built.**
- **No `fixedPoint`(RG) / `UVFixedPoint` / `IRFixedPoint` object** — the `q=±1` poles
  (`converge_residue_fixed`/`escape_residue_outside`) are the predicted resolver, but no RG-flow fixed
  point is instantiated as such. **Predicted-not-built.**
- **No relevant/irrelevant/marginal-operator classification object** — the `q=±1` tag
  (`multiplier_unimodular`/`ResidueTag`) is the predicted resolver; no `RelevantOperator` /
  scaling-eigenvalue classification exists. **Predicted-not-built.**
- **No universality-class / `CallanSymanzik` object** — the fold-to-normal-form (`Lens.view =
  Raw.fold`, `clo_idempotent`) and the `q=+1` invariant (`noether.md`'s `det_holonomy_eq_one`) are
  the predicted resolvers; no `UniversalityClass` or μ-invariance equation is built.
  **Predicted-not-built.**
- **★ The continuous β-function is the `Real213` flow residue (honest about the DRLT tie).** The
  repo's *own* `AsymptoticFreedom.lean` docstring states it plainly: "Continuum β-function =
  continuous limit of discrete sequence. In DRLT, discrete is fundamental." So the running is built as
  a **sequence of rationals** (`1/α_3(N)`) with a **monotonicity witness** (the β-sign,
  `mono_1_2`/`mono_2_3`) and a **bracket-convergence** to the `q=+1` limit (ζ(2)) — NOT as a
  β-function differential-flow theorem. The discrete structure is closed (∅-axiom); the *continuous*
  β = the `Real213`-cut residue, reached-by-none, narrowed by the modulus `N`. The flow itself is the
  same `Real213` continuous-trajectory residue as `differential_equations.md`'s continuous integral
  operator and `gaussian_clt.md`'s full profile. **Predicted-not-built / conceptual.**

**Net.** Not collapse-only — it *predicts* the RG's shape (the dial as a flow, fixed points = `q=±1`
poles, β = the scaling-derivative, universality = the `q=+1` basin = the fold-to-normal-form,
Callan–Symanzik = the `q=+1` invariant) and *derives* why each pillar holds (why a semigroup not a
group — the dial's irreversibility `cutDouble_no_grade`; why the IR fixed point is attractive — `q=+1`
converge; why universality — the read-op kills the irrelevant residue). Not a miss — the resolution
dial + its additive semigroup (`IsResolutionShift_compose`), the `q=±1` converge/escape engine
(`converge_residue_fixed`/`escape_residue_outside`/`golden_is_converge`), the fold-to-normal-form
(`Lens.view=Raw.fold`/`clo_idempotent`), and — uniquely — the repo's BUILT running-coupling sequence
(`1/α(N)=const·S(N)`, `mono_1_2`/`mono_2_3`, the ζ(2) bracket) are **all real ∅-axiom theorems**. It
is a **prediction whose engines and the concrete physics twin are fully built**, one notch below a
closed derivation for the same reason as `differential_equations.md`/`spectral_sequences.md`: the
field-specific *objects* — `RGFlow`, `betaFunction`, the RG `fixedPoint`, the universality-class /
Callan–Symanzik statements — and the *continuous* flow are conceptual welds / `Real213` residues, not
yet instantiated.

## Revelation (collapse + residue-surfaced + forcing; the DRLT tie)

**The RG flow, the β-function, the UV/IR fixed points, relevant/irrelevant operators, universality,
and the Callan–Symanzik equation are ONE `(C, L)` — the resolution dial run as a continuous FLOW
whose fixed points are the `q=±1` poles — resolved by the SAME machinery (the resolution dial + its
additive composition `IsResolutionShift_compose`, the `q=±1` converge/escape engine
`ResidueTag`/`banach_fixed_point_modulated`, the fold-to-normal-form `Lens.view=Raw.fold`) the
calculus has built across the resolution axis, AND it is the abstract twin of the repo's own built
running-of-constants.** Collapse + residue-surfaced + forcing, with the DRLT tie:

1. **Collapse onto the resolution axis — RG is the dial made a flow.** The *RG flow*
   (coarse-graining), the *β-function*, the *UV/IR fixed points*, *relevant/irrelevant/marginal
   operators*, *universality*, and the *Callan–Symanzik equation* are not seven new physics
   primitives — they are `continuity.md`/`derivative.md`'s **one resolution dial** run as a flow. The
   RG semigroup `R_{s₁}∘R_{s₂}=R_{s₁+s₂}` is `IsResolutionShift_compose` (grades add); its
   irreversibility (semigroup, not group) is `cutDouble_no_grade`; the running coupling is the
   trajectory of the readout (`spectral_sequences.md`'s `r`-indexed sequence read as a value); β is
   `derivative.md`'s `L₋` along the scale axis. **RG = (the resolution dial) made a continuous flow
   with `q=±1` fixed points** — no new primitive. This collapses RG onto the SAME axis as
   `spectral_sequences.md` (the dial iterated on residues) and `ito_calculus.md` (the dial's scaling),
   the three being one resolution axis read three ways: iterated (pages), scaled (Itô), flowed (RG).

2. **Residue surfaced — the UV/IR fixed points ARE the `q=±1` poles, and universality IS the
   `q=+1` basin = the fold-to-normal-form.** The deepest line: an RG fixed point is the
   `Residue(L,C)` of the flow — converge (`q=+1`, the attractive IR fixed point, the trajectory
   asymptotes to a located point reached-by-none, `converge_residue_fixed`/`golden_is_converge`) or
   escape (`q=−1`, the repulsive UV fixed point, the trajectory leaves every neighbourhood,
   `escape_residue_outside`). Relevant operators are the `q=−1` surviving directions; irrelevant
   operators are the `q=+1` directions the flow pushes below the resolution floor — the SAME dropped
   residue `derivative.md`/`ito_calculus.md` identified, now read as "the coarse-graining flow forgets
   it". And universality — different microscopics flowing to the same IR fixed point — IS the
   **fold-to-normal-form**: `Lens.view = Raw.fold` forgets the construction-history and keeps only the
   readout, so distinct `C`'s with the same readout at the fixed point are one object; the basin
   collapses onto its `q=+1` attractor (`clo_idempotent`, `T²=T`). "Universality class" stops being a
   separate concept and becomes the calculus's basin-of-the-`q=+1`-attractor = the read-op's image.

3. **Forcing — the dial's one-directionality forces the semigroup, the `q=±1` tag forces the
   fixed-point types, and the read-op forces universality.** Whether the RG is a group or a semigroup
   is *forced* by the dial: coarse-graining lowers resolution and loses information
   (`cutDouble_no_grade` — no inverse), so the flow is a semigroup, not added by hand. Which fixed
   point is attractive vs repulsive is *forced* by the `q=±1` tag (converge/escape,
   `residue_tag_two_poles`), the marginal boundary at `multiplier=±1` (`multiplier_unimodular`). And
   universality is *forced* by the read-op: `Lens.view = Raw.fold` is the *unique* arrow out of `Raw`
   (`raw_initial`/`dhom_unique_pointwise`), so any two constructions agreeing at the fixed-point
   readout are identified — universality is not a coincidence but the initiality of the read-op. The
   Callan–Symanzik equation is then `noether.md`'s `q=+1` `Aut(C)`-invariant character read on the
   resolution flow: the physics is conserved along the flow (independent of the arbitrary scale `μ`),
   the same `det_holonomy_eq_one` conservation read on the dial rather than a symmetry.

**THE NEW DATUM (vs `spectral_sequences.md`/`ito_calculus.md`/`derivative.md` — the re-skin guard):
the resolution dial becomes a continuous FLOW whose `q=±1` fixed points are UV/IR, universality is the
`q=+1` basin = the fold-to-normal-form, AND this is the abstract twin of the repo's own BUILT
running-of-constants.** `spectral_sequences.md` iterated the dial on *residues* (the page tower);
`ito_calculus.md` added the dial's *scaling* (√h). RG is the genuinely new reading: **the dial run as
a one-parameter flow on VALUES (the coupling), whose attractors/repellers are the converge/escape
poles, and whose basins are the read-op's fibres (universality).** And — uniquely among the
resolution-axis notes — the abstract object is the repo's *own physics*: `1/α(N) = const·S(N)` is the
running coupling built as a sequence indexed by the resolution dial, monotone (β-sign) toward the
`q=+1` limit ζ(2) (built as a bracket, reached-by-none). The single deepest find:

| | what is read | the resolution dial used as | the `q=±1` residue is | Lean shadow |
|---|---|---|---|---|
| `spectral_sequences.md` | residues (pages `E_r`) | the iteration index `r` | convergence `E_∞` (`q=+1`) / non-degeneration (`q=−1`) | `IsResolutionShift_compose`, `residue_perpetually_reenters` |
| `ito_calculus.md` | the second difference | the √h scaling | the surviving 2nd-order term (`q=+1`) | `obstruction_int_constant`, `liftKZ 2` |
| **`renormalization_group.md` (RG)** | the coupling (a VALUE) | a continuous flow (the scale `μ`) | the IR attractor (`q=+1`) / UV repeller (`q=−1`) | `IsResolutionShift_compose` (semigroup), `converge_residue_fixed`/`escape_residue_outside`; **DRLT: `1/α(N)=const·S(N)`, `mono_1_2`/`mono_2_3`, ζ(2) bracket** |

So **YES** — the RG is the calculus's resolution dial made a FLOW, its fixed points the `q=±1` poles,
universality the `q=+1` basin = the fold-to-normal-form, the Callan–Symanzik equation the `q=+1`
invariant along the flow — and it is the abstract twin of the repo's own running-of-constants (built
as a discrete sequence + monotonicity + a ζ(2) bracket, the continuous β being the `Real213` flow
residue). No new primitive — it is the resolution axis (`continuity.md`/`derivative.md`), composed
additively (`spectral_sequences.md`), scaled (`ito_calculus.md`), now run as a one-parameter
trajectory with `q=±1` attractors. The precise missing leg is the named RG *object*: `RGFlow`,
`betaFunction`, the RG `fixedPoint`, the universality-class / Callan–Symanzik statements, and the
continuous flow (the `Real213` residue).

## Note for the technique — does RG force a NEW construct?

**No new primitive; one sharpening — EXTEND, a resolution-axis find (the dial as a flow), plus the
first DRLT-native twin among the resolution-axis notes.** This decomposition adds nothing to model
v7.1's invariant set; it *uses* existing slots and adds one reading-mode to the resolution axis:
- *the RG flow / coarse-graining* = `continuity.md`/`derivative.md`'s resolution dial run as a
  one-parameter flow; the RG semigroup = `IsResolutionShift_compose` (grades add), its irreversibility
  = `cutDouble_no_grade` (no inverse) — no new construction;
- *the running coupling* = the trajectory of the readout (the `r`-indexed value sequence,
  `spectral_sequences.md`'s page index read as the scale);
- *the β-function* = `derivative.md`'s `L₋` along the scale axis (`ito_calculus.md`'s scaling), its
  sign the `q=±1` direction bit;
- *the UV/IR fixed points* = the `q=±1` poles (`escape_residue_outside`/`converge_residue_fixed`);
- *relevant/irrelevant/marginal* = the `q=±1` tag on a perturbation, boundary at `multiplier=±1`;
- *universality* = the `q=+1` attractor's basin = the fold-to-normal-form (`Lens.view=Raw.fold`,
  `clo_idempotent`);
- *Callan–Symanzik* = `noether.md`'s `q=+1` `Aut(C)`-invariant character read on the resolution flow.

The one genuine sharpening for the technique: **the resolution dial can be run as a continuous
one-parameter FLOW on the readout, and the flow's fixed points are the `q=±1` poles — an attractive
fixed point = the `q=+1` converge pole (the basin = universality = the fold-to-normal-form), a
repulsive fixed point = the `q=−1` escape.** This completes the resolution axis's three reading-modes
(iterated on residues = spectral sequences; scaled = Itô; flowed on values = RG) and is the cleanest
demonstration that the `q=±1` residue tag governs *dynamical* fixed points, not just static residues.
AND it is the first resolution-axis note whose abstract object is the repo's OWN physics: the running
of `1/α(N)` is the running coupling built ∅-axiom as a resolution-indexed rational sequence, the
β-sign as monotonicity, the IR fixed point as the ζ(2) bracket — the abstract twin made concrete, with
the honest caveat that the *continuous* β-flow is the `Real213` residue (a sequence + a limit, not a
differential-flow theorem; the repo's own docstring says so).

---

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; purity by `tools/scan_axioms.py`, re-run this session from repo root)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| **coarse-graining = the resolution dial; one coarse-graining = grade 1** | `Lib/Math/Analysis/ResolutionShift.lean : IsResolutionShift` (`:73`), `IsResolutionShift_cutHalf` (`:95`) | ∅-axiom ✓ (17/0) |
| **★ the RG SEMIGROUP `R_{s₁}∘R_{s₂}=R_{s₁+s₂}` = the grades ADD under composition** | `Lib/Math/Analysis/ResolutionShift.lean : IsResolutionShift_compose` (`:130`, grade `E₂+E₁`) | ∅-axiom ✓ (17/0) |
| the `r`-fold coarse-graining, cumulative grade `r` | `Lib/Math/Analysis/ResolutionShift.lean : cutHalfIter` (`:158`), `IsResolutionShift_cutHalfIter` (`:179`) | ∅-axiom ✓ (17/0) |
| **★ RG is a SEMIGROUP not a group — coarse-graining is irreversible (no inverse)** | `Lib/Math/Analysis/ResolutionShift.lean : cutDouble_no_grade` (`:355`), `cutSquare_no_grade` (`:379`) | ∅-axiom ✓ (17/0) |
| **★ the attractive IR fixed point = the `q=+1` converge pole (the flow CONVERGES, reached-by-none)** | `Lib/Math/Foundations/ResidueTag.lean : converge_residue_fixed` (`:160`), `golden_is_converge` (`:180`), `residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`); `Lib/Math/Analysis/BanachFixedPointModulated.lean : banach_fixed_point_modulated` (`:111`) | ∅-axiom ✓ (ResidueTag 55/0; BanachFixedPointModulated PURE via delegation) |
| **★ the repulsive UV fixed point = the `q=−1` escape (the flow ESCAPES)** | `Lib/Math/Foundations/ResidueTag.lean : escape_residue_outside` (`:133`); `Lens/Foundations/FlatOntologyClosure.lean : object1_not_surjective` (`:61`) | ∅-axiom ✓ (55/0) |
| the flow step = the residue re-entering (CONVERGES vs ESCAPES forever) | `Lens/Foundations/ResidueReentry.lean : residue_perpetually_reenters` (`:85`), `residue_reentry_never_closes` (`:63`) | ∅-axiom ✓ (14/0) |
| **universality = the `q=+1` basin = the fold-to-normal-form (the read-op collapses the basin)** | `Lib/Math/Order/GaloisConnection.lean : clo_idempotent` (`:126`, `T²=T`); `Lib/Math/Order/FenchelMoreau.lean : biconj_idempotent` (`:134`) | ∅-axiom ✓ (GaloisConnection 15/0, FenchelMoreau 18/0) |
| **★ DRLT TWIN: the running coupling `1/α_3(N)=(NS²−1)·S(N)` as a resolution-indexed rational sequence** | `Lib/Physics/Couplings/AsymptoticFreedom.lean : pre_eq_8` (`:56`), `inv_alpha_3_at_N1` (`:59`), `inv_alpha_3_at_N2` (`:64`), `asymp_free_via_monotone` (`:78`) | ∅-axiom ✓ (6/0) |
| **★ DRLT TWIN: the β-sign = `S(N)` monotonicity (asymptotic freedom)** | `Lib/Physics/Basel/Bound.lean : mono_1_2` (`:66`), `mono_2_3` (`:67`); `S_1`/`S_2`/`S_3` (`:45–47`) | ∅-axiom ✓ (27/0) |
| **★ DRLT TWIN: the IR fixed point = the `q=+1` limit ζ(2), built ONLY as its rational bracket (reached-by-none)** | `Lib/Physics/Basel/Bound.lean : bracket_3` (`:74`), `bracket_30` (`:128`), `bracket_50` (`:134`), `bracket_width_3` (`:79`) | ∅-axiom ✓ (27/0) |
| **★ DRLT TWIN: resolution-depth cutoff per force (coarse-graining survival depth)** | `Lib/Physics/Foundations/ResolutionDepth.lean : depth_principle_witnesses` (`:43`) | ∅-axiom ✓ (1/0) |
| DRLT: the high-E↔IR running gap as a pure rational `d²/NS=25/3` | `Lib/Physics/Couplings/RunningGap.lean : running_gap_master` (`:88`) | ∅-axiom ✓ (3/0) |
| the β-function = `L₋` along the scale axis (prior; derivative.md's difference-Lens) | `Lib/Math/Analysis/Cauchy/NewtonGregory.lean : diffZ` (`:54`) — cited via `derivative.md`/`ito_calculus.md` | cited, prior ✓ |
| Callan–Symanzik = noether.md's `q=+1` `Aut`-invariant character read on the flow (cross-frame) | `noether.md` (`det_holonomy_eq_one`) — cross-frame, prior | cited, prior ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root with the `E213.` module
prefix):** `E213.Lib.Math.Analysis.ResolutionShift` **17/0**; `E213.Lib.Math.Foundations.ResidueTag`
**55/0**; `E213.Lib.Physics.Couplings.AsymptoticFreedom` **6/0**; `E213.Lib.Physics.Basel.Bound`
**27/0**; `E213.Lib.Physics.Couplings.RunningGap` **3/0**; `E213.Lib.Physics.Foundations.ResolutionDepth`
**1/0** — all pure, 0 dirty. (ResidueReentry 14/0, GaloisConnection 15/0, FenchelMoreau 18/0 verified
in `spectral_sequences.md`'s scan this corpus.) The purity claim rests on the fresh scans, not
docstrings.

### Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

- **No `RGFlow` / `betaFunction` / `beta_function` / `coupling`-as-flow object** — grep
  (case-insensitive) for `RGFlow`/`RG_flow`/`betaFunction`/`beta_function`/`renormaliz`/`callan`/
  `symanzik`/`coarsegrain`/`coarse-grain` returns **no RG-named Lean declarations**. The only
  `renormaliz` hits are docstring prose: `Lib/Physics/Couplings/ClosedPropagator.lean:91`
  `renormalization_auto` is **`True := trivial`** (a vacuous interpretive marker — honestly flagged,
  it proves nothing), and `Lib/Physics/Hadron/ProtonMass.lean:27` is a comment. The resolution dial
  (`cutHalfIter`) and the per-depth coupling sequence (`1/α(N)=const·S(N)`) are built; the *flow*
  welding them is the conceptual weld. **Predicted-not-built.**
- **No `fixedPoint`(RG) / `UVFixedPoint` / `IRFixedPoint` object** — the `q=±1` poles
  (`converge_residue_fixed`/`escape_residue_outside`/`golden_is_converge`) are the predicted resolver;
  no RG-flow fixed point is instantiated. (The `fixedPoint` grep hits are Banach/ProbeTwist/Wilson —
  not RG.) **Predicted-not-built.**
- **No relevant/irrelevant/marginal-operator classification** — the `q=±1` tag
  (`multiplier_unimodular`/`ResidueTag`) is the predicted resolver; no scaling-eigenvalue
  classification exists. **Predicted-not-built.**
- **No universality-class / `CallanSymanzik` / μ-invariance object** — the fold-to-normal-form
  (`Lens.view=Raw.fold`/`clo_idempotent`) and the `q=+1` invariant (`noether.md`'s
  `det_holonomy_eq_one`) are the predicted resolvers; no `UniversalityClass` or μ-invariance equation
  is built. **Predicted-not-built.**
- **★ The continuous β-function / continuous flow is the `Real213` residue — honest about the DRLT
  tie.** The repo's own `AsymptoticFreedom.lean` docstring (`:42–44`) states: "Continuum β-function =
  continuous limit of discrete sequence. In DRLT, discrete is fundamental." So the running is built as
  a **sequence of rationals** + a **monotonicity witness** (the β-sign) + a **bracket-convergence** to
  the `q=+1` limit ζ(2) — **NOT** a β-function differential-flow theorem. The discrete structure is
  closed ∅-axiom; the continuous β = the `Real213`-cut residue (reached-by-none, narrowed by the
  modulus `N`), the same continuous-trajectory residue as `differential_equations.md`'s continuous
  integral operator. **Predicted-not-built / conceptual.**

### Verified buildable witness (genuinely true + terminating)

The DRLT running-coupling sequence is *already* a built witness of "the running coupling = a
resolution-indexed sequence with `q=±1`-tagged limit": `AsymptoticFreedom.inv_alpha_3_at_N1`/
`inv_alpha_3_at_N2` (`1/α_3` at depths 1, 2 = 8, 10) + `Basel/Bound.mono_1_2`/`mono_2_3` (the
β-sign = monotonicity) + the ζ(2) bracket (`bracket_30`/`bracket_50`) — all verified PURE this
session. A buildable *next* step toward a named RG object (not asserted here, a promotion target): a
finite three-point monotone-flow witness `1/α_3(1) < 1/α_3(2) < 1/α_3(3)` packaged with its
bracket-limit, exhibiting one concrete "the running coupling flows monotonically toward the `q=+1`
fixed point" statement — the RG analogue of `spectral_sequences.md`'s suggested finite page-tower
witness, decidable and `Quot`-free. The genuine missing leg remains the named
`RGFlow`/`betaFunction`/`fixedPoint` object + the continuous flow, not a one-line `decide`.
