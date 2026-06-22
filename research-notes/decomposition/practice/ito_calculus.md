# Decomposition: Itô / stochastic calculus (Brownian motion, [B]_t = t, the Itô integral, df = f'dB + ½f''dt, the Itô isometry, the martingale property)

*213-decomposition per `../README.md` (model v7.1). The KEY datum is NOT another weight-axis
consolidation (that is `martingales.md`, the direct neighbor) — it is a sharper find on the
**resolution axis**: Itô calculus is `derivative.md`'s **difference-reading with the second-order
residue made load-bearing**. The ordinary derivative (resolution `h→0`) drops the O(h²) term; under
**Brownian resolution the increment is O(√h)**, so its SQUARE is O(h) — first order — and the Itô
correction `½f''dt` is EXACTLY the **second-order residue** `derivative.md`'s smooth chain rule
discards but the √h resolution forces to survive. Cross-links: `derivative.md` (the difference-Lens
`L₋` + the resolution parameter; the dropped O(h²)), `martingales.md` (the `q=+1` conditional-
expectation fixed point — the Itô integral is a martingale), `gaussian_clt.md` (the convolve-rescale
`q=+1` fixed point; Brownian increments ARE Gaussian), `probability.md` (the weight axis).*

> **LEVERAGE target.** The bar is not "re-see Itô calculus" but: does the calculus *derive* the
> field's shape from existing slots — and is the Itô correction `½f''dt` literally the calculus's
> **second-order residue at a non-standard resolution scaling**? The thesis, in five parts:
> 1. **Brownian motion `B_t`** = the `q=+1` convolve-rescale fixed point (`gaussian_clt.md`'s
>    Gaussian) read **as a process** — increments are independent Gaussians; the new ingredient is
>    the resolution SCALING `ΔB ~ √(Δt)`, not the increment law;
> 2. **quadratic variation `[B]_t = t`** = the **second-order residue of the difference-reading**
>    that does NOT vanish, because the √h scaling makes `(ΔB)² ~ Δt` first-order — the
>    non-vanishing surplus of the squared-increment reading (`liftKZ 2`, the second forward
>    difference, made visible);
> 3. **the Itô formula `df = f'dB + ½f''dt`** = `⟨C | L_derivative ⟩ ⊕ Residue(L,C)` with the
>    second-order residue `½f''·[dB]² = ½f''dt` **PROMOTED to a visible term** — the same Taylor /
>    `dsq`-shape second-order term `derivative.md` drops at smooth resolution but √h keeps;
> 4. **the Itô integral `∫f dB`** = the weight axis (`probability.md`) read at this resolution; it
>    is a **martingale** = the `q=+1` conditional-expectation fixed point (`martingales.md`'s
>    `banach_fixed_point_modulated`/`golden_is_converge` pole);
> 5. **the Itô isometry `E[(∫f dB)²] = E[∫f² dt]`** = the convolution / mass-conservation character
>    (`mass_conv`/`momentNum_conv`, `gaussian_clt.md`) — the second-moment-multiplies fact carried
>    by the independence (`×↦·`) of disjoint increments.
> Honest verdict at the end: prediction / collapse / miss, Lean-built vs conceptual line drawn.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same two-layered point-construction as `derivative.md`/`integration.md`:
  a construction of points (a time-axis / dyadic bracket-chain, points = refinement residues) with a
  **value-construction hung at each**. Itô adds **no new construction**. A path `t ↦ B_t` is a
  reading-over-`C` exactly as a function `f` is in `derivative.md` — but the value at each point is
  drawn from the `gaussian_clt.md` weight (the convolve-rescale `q=+1` fixed point), and the path is
  read at the **√h resolution scaling**. What is genuinely new over `derivative.md` is *not* a new
  primitive but a **resolution-scaling parameter on `L`**: where `derivative.md` reads adjacency at
  `h` (so the increment is O(h)), Brownian resolution reads adjacency at `√h` (the increment is
  O(√h)). The scaling is the one dial-position `derivative.md` left implicit. (Lean shadow: there is
  **no `BrownianMotion`/`Wiener`/`stochastic` type at all** — grep-confirmed zero hits; the
  construction is the same dyadic point-construction `derivative.md`/`gaussian_clt.md` carry, with the
  Gaussian increment law in `Distribution/Gaussian.lean`.)

- **Reading `L`** — `derivative.md`'s difference-reading `L₋ = (m,n)↦m−n`, taken to **second order**,
  read at the **√h resolution**. Three pieces, each already in the calculus:
  1. **the difference-reading at √h resolution.** `df` is still `L₋` aimed at adjacent values
     (`Δf = f(x+h)−f(x)`, `derivative.md`, Lean-literal `diffZ s n = s(n+1)−s n`,
     `NewtonGregory.lean:54`). The Itô integrand `f'dB` is exactly `derivative.md`'s first-order term
     — the difference-Lens at residue resolution. No new reading here.
  2. **the SECOND difference — the load-bearing piece.** `derivative.md` reads `L₋` once; Itô reads
     it **twice**. The second forward difference is `liftKZ 2` (`NewtonGregory.lean:57`,
     `liftKZ (k+1) = diffZ ∘ liftKZ k`) — the discrete second-order operator. At smooth resolution
     `liftKZ 2` contributes an O(h²) term that the `h→0` limit kills (it is *below* the resolution
     floor). At Brownian √h resolution it does **not** vanish: the square of an O(√h) increment is
     O(h) — the *same order as the first difference at smooth resolution*. So the second-order reading
     crosses the resolution floor and becomes visible. **This is the whole content of Itô.**
  3. **the weight axis at this resolution.** The integrator `dB` carries the `gaussian_clt.md` weight
     (independent Gaussian increments). The Itô integral `∫f dB` is the weight-reading
     (`probability.md`'s value-weighted count, `Expectation.discreteNum`) accumulated against the
     Brownian increments — `integration.md`'s `L_Σ` (accumulation = `L₋`'s inverse) at residue
     resolution, weighted.

- **Residue** — `q = ±1`, two faces that are one — and the second-order face is **promoted to a
  visible term** (the find):
  1. *The `q=+1` second-order residue made load-bearing — `[B]_t = t` and `½f''dt`.* In
     `derivative.md` the difference-reading's residue at smooth resolution is the O(h²) term that
     the modulus discards (it sits *below* the floor — "the limit forgets it"). Under √h scaling the
     **squared-increment reading does not vanish**: `Σ(ΔB)² → t` exactly (quadratic variation
     `[B]_t = t`), a *non-zero* surplus. The Itô formula keeps it as the **`½f''·[dB]²` term**
     (`= ½f''dt`), the second-order Taylor / `dsq`-shape coefficient that the smooth chain rule
     `df = f'dx` drops. It is `q=+1` (converging): `Σ(ΔB)²` asymptotes to the deterministic value
     `t`, narrowed by a modulus, reached by no finite partition — `gaussian_clt.md`'s
     `q=+1`/`golden_is_converge` pole (the second moment is the *finite generator* the Gaussian
     fixes, `variance_master`). The quadratic variation IS this residue: the non-vanishing surplus
     of the squared-difference reading at √h resolution.
  2. *The `q=±1` direction bit — the drift vs the martingale part.* Exactly `martingales.md`'s Doob
     split read on the resolution axis: the `f'dB` part is the `q=+1` martingale (the
     conditional-expectation fixed point — re-projecting down a refinement changes nothing,
     `E[f'dB | F]=0`), the `½f''dt` part is the **directed residue** (a deterministic drift with a
     fixed sign, the `q=±1` orientation). `df = f'dB + ½f''dt` IS `⟨C|L⟩ ⊕ Residue(L,C)` with the
     martingale part `⟨C|L⟩` and the second-order drift the `Residue`.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   path B_t                   =  ⟨ point-construction | gaussian_clt weight read as a process ⟩   (gaussian_clt.md's q=+1 fixed point, as a path)
   resolution scaling ΔB~√Δt  =  the √h DIAL POSITION on L  (derivative.md's resolution parameter, the one it left implicit)
   df (smooth, classical)     =  ⟨ value-pair (f(x+h),f(x)) | L₋ ⟩  at smooth resolution  =  f'dx   (derivative.md; O(h²) DROPPED below the floor)
   QUADRATIC VARIATION [B]_t=t=  Residue(L,C), q=+1  =  the SECOND-difference reading (liftKZ 2) that does NOT vanish at √h  (Σ(ΔB)²→t)
   ITÔ FORMULA df=f'dB+½f''dt  =  ⟨C|L₋⟩ ⊕ Residue:  f'dB = the first-order reading,  ½f''dt = the second-order residue PROMOTED to a visible term
   the ½f''·[dB]² coefficient  =  the Taylor/dsq second-order term (leibniz_universal_delta4 shape)  the smooth chain rule drops, √h keeps
   ITÔ INTEGRAL ∫f dB          =  integration.md's L_Σ (accumulate = L₋⁻¹) at residue resolution, weighted by the gaussian increments
   ∫f dB is a MARTINGALE       =  the q=+1 conditional-expectation fixed point (martingales.md, banach_fixed_point_modulated / golden_is_converge)
   ITÔ ISOMETRY E[(∫f dB)²]    =  E[∫f² dt]  =  the mass/second-moment-multiplies character  (mass_conv/momentNum_conv; independence ×↦· of disjoint increments)
   drift vs martingale         =  the q=±1 direction bit on the residue  (martingales.md's Doob split, on the resolution axis)
```

So Itô calculus is **`derivative.md`'s difference-reading dialed to √h resolution, where the
second-order residue survives** — the SAME `L₋` reading, the SAME resolution parameter, the SAME
`q=±1` residue, with the one new ingredient being the **scaling** (√h not h) that lifts the
second-order term above the resolution floor. It is not a new analytic primitive; it is `derivative.md`
read at the one dial-position where its dropped O(h²) term becomes load-bearing.

## LEVERAGE — does the calculus DERIVE the Itô formula, and is ½f''dt literally the second-order residue?

**Verdict: PREDICTION + PARTIAL — and the central claim (½f''dt = the second-order residue made
load-bearing by the √h resolution scaling) is the genuinely new datum, distinct from
`martingales.md`'s weight-axis consolidation. The calculus derives the field's shape — which residue,
why `q=+1`, why the second-order term survives, why the integral is a martingale, why the isometry is
the second-moment character — from existing slots (the difference-Lens, the resolution parameter +
its scaling, the `q=±1` residue, the `gaussian_clt.md`/`martingales.md` `q=+1` fixed point). The
discrete second-order machinery (`liftKZ 2`, `dsq`/Leibniz, the convolution moments) and the `q=+1`
engine are all real PURE theorems; the named `BrownianMotion`/`ItoIntegral`/`quadraticVariation`
objects are ABSENT (grep-confirmed) and are the located missing leg.**
Three layers:

**(A) Predicted, and the prediction is non-trivial — the resolution-scaling argument.** Before
looking at the Lean, the calculus emits a specific claim from its parts. `derivative.md` established
that the difference-reading `L₋` carries a **resolution parameter** (step-1 vs `h→0` modulus) and
that at smooth resolution the second-order term is O(h²), *dropped* by the `h→0` modulus (it is below
the resolution floor — the "+C"/forgetting residue). The calculus's slots then *force* the Itô
correction: if the resolution scaling is `ΔB ~ √(Δt)` (the only scaling under which the increment is
not itself deterministic — the Gaussian's `variance_master` second moment is the finite generator),
then `(ΔB)² ~ Δt` is **first-order**, so the second-order reading `liftKZ 2`, weighted by the Taylor
coefficient `½f''`, **crosses the floor and survives**. Composing this with `gaussian_clt.md` (the
increment is the `q=+1` convolve-rescale fixed point) and `martingales.md` (the integral against a
fixed-point weight is the `q=+1` conditional-expectation martingale) *forces* the form:

> "Read `f(B)` through the difference-Lens at √h resolution; the first-order term `f'dB` is the
> `q=+1` martingale part; the second-order term `½f''·[dB]²` does NOT vanish (because √h makes
> `[dB]² = dt` first-order), so it is promoted to a visible drift `½f''dt`, the directed `q=±1`
> residue; the squared-increment reading's surplus is `[B]_t = t`; and `E[(∫f dB)²] = E[∫f² dt]`
> because disjoint increments are independent (`×↦·`) and the second moment multiplies (`mass_conv`)."

That is a *derivation* of Itô's shape — which residue, why it survives, why `q=+1`, why the integral
is a martingale, why the isometry holds — not a relabeling. The novel content over `martingales.md`:
`martingales.md` reads the weight axis at *discrete* refinement (the filtration, no scaling); Itô
adds the **resolution-scaling** that turns `derivative.md`'s dropped O(h²) term into the load-bearing
`½f''dt`. The new datum is precisely **"the Itô correction is the second-order residue
`derivative.md` discards, kept by the √h scaling."** It passes the re-skin guard the way
`gaussian_clt.md`/`entropy.md` did — a prediction with a mechanism, not a re-description.

**(B) The Lean spine that is actually built (verified ∅-axiom this session via `tools/scan_axioms.py`
from repo root) — the discrete second-order machinery, the `q=+1` engine, and the convolution moments
are all real PURE theorems; only the named Itô objects are missing.**

- **The second-order difference-reading `liftKZ 2` — the discrete operator behind `½f''` and `[B]_t`,
  ∅-axiom.** `NewtonGregory.lean:57` `liftKZ (k+1) s = diffZ (liftKZ k s)` (the `k`-fold forward
  difference; `liftKZ 2` = the second difference). The decisive witness that the second-order reading
  is **genuinely non-trivial and survives only at the faithful resolution**:
  `NewtonGregory.lean:404` `obstruction_int_constant` — `liftKZ 2 (↑vObs) 0 = 2 ∧ liftKZ 2 (↑vObs) 1
  = 2` (PURE, by `decide`), i.e. the second difference is the *constant 2*, the genuine degree-2
  structure — paired with `obstruction_nat` (`:395`, PURE) showing the *first-order* ℕ-Lens
  **cannot see it** (`¬ polyDepth 2 vObs`). This is the Lean shadow of the Itô fact exactly: the
  second-order residue is invisible to the first-order (smooth `h`) reading and visible only when the
  resolution reaches second order — the √h scaling's job. `DepthCharacterization.lean:59`
  `polyDepthZ_succ_of_diff` ("a difference drops the resolution-depth by one") + `:72`
  `diffZ_binomColZ` (`Δ` of a binomial column = the next column down) ground "applying the
  difference-reading lowers the order," so the second-order term lives exactly one resolution-level
  down — the level √h reaches. (NewtonGregory 41/0; DepthCharacterization PURE on both cited names.)
- **The Taylor / `dsq` second-order shape — `½f''·[dB]²` as the calculus's second-order residue,
  ∅-axiom.** The second-order term in `df` is the calculus's recurring **graded second-order
  residue**: `V4Capstone.lean:62` `leibniz_universal_delta4` (`δ(α⌣β) = δα⌣β ⊕ α⌣δβ`, the
  graded-product Leibniz rule, README v7.1's graded-relation slot) is the same second-order
  product-rule shape, and `V4Capstone.lean:41` `dsq_zero_universal_delta4` (`δ²=0`) is the
  second-application operator whose orientation bits propagate the `q=±1` sign. The Itô product/chain
  rule `d(fg) = f dg + g df + df·dg` is the **same Leibniz shape with the extra `df·dg` term** — the
  cross-quadratic-variation `[f,g]` correction that the smooth (first-order) Leibniz rule drops and √h
  keeps. (V4Capstone 5/0 PURE — `dsq_zero_universal_delta4` and `leibniz_universal_delta4` both PURE.)
- **Brownian motion = the `gaussian_clt.md` `q=+1` fixed point; `[B]_t = t` = the preserved second
  moment, ∅-axiom.** The increment law is the convolve-rescale `q=+1` fixed point already built:
  `ConvolveRescaleContraction.lean:345` `Φ_contraction` (convolve-rescale IS a `Contraction`), `:471`
  `orbit_to_center` (the `q=+1` fixed point reached-by-none), and the completion-limit
  `DyadicCompletion.lean:366` `orbit_to_center_completion` / `:612` `gaussian_center_fixed_via_engine`.
  The quadratic variation `[B]_t = t` is the **second moment fixed** — `Variance.lean:44`
  `variance_master` (fair-coin `Var = 1/4`, the preserved second moment) and
  `Gaussian.lean:85` `CLT_fair_variance_marker` (variance preserved = the finite generator), with
  `Gaussian.lean:74` `CLT_fair_centered` (the first moment is centered, `q=+1`). `[B]_t = t` is
  literally "the convolution's second moment accumulates linearly" — `momentNum_conv` summed over the
  partition. (ConvolveRescaleContraction 20/0, DyadicCompletion 32/0, Variance 4/0, Gaussian 9/0.)
- **The `q=+1` martingale engine — the Itô integral is a martingale, ∅-axiom.** The Itô integral's
  martingale property is `martingales.md`'s leg, the *same* engine: `ResidueTag.lean:160`
  `converge_residue_fixed` (delegating to `BanachFixedPointModulated.lean:111`
  `banach_fixed_point_modulated`), `:180` `golden_is_converge` (the `q=+1` φ-Cassini tie), `:228`
  `residue_tag_two_poles`, `:86` `multiplier_unimodular`. `∫f dB` is the conditional-expectation
  reading as the `q=+1` fixed point of refinement (the stochastic-integral-is-a-martingale fact). The
  `q=−1` escape pole (the drift / non-martingale part) is `ResidueTag.lean:133`
  `escape_residue_outside`. (ResidueTag 55/0; BanachFixedPointModulated PURE.)
- **The Itô isometry `E[(∫f dB)²] = E[∫f² dt]` = the second-moment / mass-conservation character,
  ∅-axiom.** The isometry is the second-moment-multiplies fact carried by the independence of
  disjoint increments: `ConvolveProfile.lean:190` `mass_conv` (`mass(f⋆g) = mass f · mass g`, the
  `×↦·` multiplicative character — total mass multiplies under convolution) and `:239`
  `momentNum_conv` (`momentNum(f⋆g) = momentNum f · mass g + mass f · momentNum g`, the additive
  `+↦+` moment-of-a-sum). Independence of disjoint increments is the `×↦·` character
  `Independence.lean:27` `joint` / `:87` `joint_assoc_num`; the value-weighted count is
  `Expectation.lean:27` `discreteNum` / `:62` `discreteNum_append` (linearity of expectation). The
  isometry "the second moment of the sum = the sum of the second moments" is exactly `mass_conv`'s
  multiplicativity composed over disjoint (independent) increments — the variance-adds fact
  (`CLT_fair_variance_marker`). (ConvolveProfile 20/0, Independence 12/0, Expectation 5/0.)
- **The `L¹`/finiteness control + the residue-resolution accumulation, ∅-axiom.** The Itô integral as
  accumulation at residue resolution is `integration.md`'s `L_Σ` (telescoping/Riemann at a modulus);
  the weight-bound is `Markov.lean:66` `markov_inequality` (the first-moment tail control,
  `martingales.md`'s `L¹` leg). (Markov 6/0.)

**(C) The remaining gap — predicted-not-built (the honest line, the precise missing leg).** Grep on
`lean/E213` for `BrownianMotion`/`ItoIntegral`/`quadraticVariation`/`quadratic_variation`/`stochastic`/
`brownian`/`wiener` returns **zero hits** (case-insensitive, grep-confirmed). What the Lean does
**NOT** contain — the named target:
- **No `BrownianMotion`/`Wiener` object** — no path `t ↦ B_t` with independent Gaussian increments and
  the √h scaling. The increment law exists (`gaussian_clt.md`'s convolve-rescale fixed point) but is
  **not instantiated as a process indexed by the resolution-scaled time axis**. The
  resolution-scaling parameter (√h) is the implicit dial `derivative.md` named but never built as a
  scaling on `L`. **Predicted-not-built.**
- **No `quadraticVariation`/`[B]_t = t` object** — no `Σ(ΔB)² → t` theorem. The second-difference
  operator `liftKZ 2` exists and the second moment `variance_master`/`CLT_fair_variance_marker` is
  preserved, but the weld "the squared-increment reading at √h resolution accumulates to `t`" — i.e.
  `[B]_t = t` as one statement — is **unbuilt**. The `obstruction_int_constant` witness shows the
  second-difference is genuinely non-trivial; the accumulation-to-`t` is the missing leg.
  **Predicted-not-built.**
- **No `ItoIntegral`/`∫f dB` object and no Itô-formula theorem `df = f'dB + ½f''dt`** — no integral
  against a Brownian increment, no `IsItoProcess`, no Itô-formula statement. The pieces are all
  built — the first-order reading (`derivative.md`'s `diffZ`/modulus), the second-order residue
  (`liftKZ 2`, `dsq`/Leibniz), the `q=+1` martingale (`banach_fixed_point_modulated`), the weight
  accumulation (`integration.md`'s `L_Σ`) — but the **substitution "the second-order term survives at
  √h resolution and is promoted to `½f''dt`"** is the conceptual weld, not a theorem.
  **Predicted-not-built.**
- **No Itô-isometry theorem** — no `E[(∫f dB)²] = E[∫f² dt]`. `mass_conv`/`momentNum_conv` +
  `joint_assoc_num` are the predicted resolver (second moment multiplies under independence); the
  isometry as one statement is unbuilt. **Predicted-not-built.**
- **No martingale-property-of-the-stochastic-integral theorem** — the `q=+1` engine
  (`banach_fixed_point_modulated`/`golden_is_converge`) is the predicted resolver and `martingales.md`
  reports the *same* missing `Martingale`/`condExp` objects; `E[∫f dB | F]=0` as one statement is
  unbuilt. **Predicted-not-built.**

**Net.** Not collapse-only — it *predicts* the Itô formula's shape (the second-order residue at √h
resolution) and *derives* why each pillar holds (which residue, why `q=+1`, why the second-order term
survives, why the integral is a martingale, why the isometry is the second-moment character). Not a
miss — the discrete second-order machinery (`liftKZ 2`, `obstruction_int_constant`, `dsq`/Leibniz),
the `q=+1` convolve-rescale + martingale engine (`Φ_contraction`/`orbit_to_center_completion`/
`banach_fixed_point_modulated`/`golden_is_converge`), the preserved second moment
(`variance_master`/`CLT_fair_variance_marker`), and the second-moment-multiplies character
(`mass_conv`/`momentNum_conv`/`joint_assoc_num`) are **all real ∅-axiom theorems**. It is a
**prediction whose engines and consolidating ties are fully built**, one notch below a closed
derivation for the same reason as `gaussian_clt.md`/`martingales.md`: the field-specific *objects* —
`BrownianMotion`, `ItoIntegral`, `quadraticVariation`, the Itô-formula and isometry statements — are
conceptual welds, not yet instantiated.

## Revelation (collapse + residue-surfaced + forcing)

**The Itô formula, quadratic variation, the Itô integral's martingale property, and the Itô isometry
are ONE `(C, L)` — `derivative.md`'s difference-reading dialed to √h resolution, where its
second-order residue survives — resolved by the SAME machinery (`derivative.md`'s difference-Lens +
resolution parameter, `gaussian_clt.md`'s `q=+1` convolve-rescale fixed point, `martingales.md`'s
`q=+1` conditional-expectation fixed point, the convolution moments) the calculus has built across the
resolution and weight axes.** Collapse + residue-surfaced + forcing, three at once:

1. **Collapse onto `derivative.md`'s resolution axis — Itô is the derivative at one dial-position.**
   The *Itô formula* (the second-order chain rule), *quadratic variation* (`[B]_t = t`), the *Itô
   integral* (accumulation against `dB`), its *martingale property*, and the *Itô isometry* are not
   five new analytic primitives — they are `derivative.md`'s **one difference-reading `L₋`** read at
   the **√h resolution** where the second-order term crosses the floor. The first-order part `f'dB`
   is `derivative.md`'s ordinary derivative; the second-order part `½f''dt` is the O(h²) residue
   `derivative.md` *drops* at smooth resolution, *kept* by √h. The integral is `integration.md`'s
   `L_Σ` weighted by `gaussian_clt.md`'s `q=+1` fixed point; its martingale property is
   `martingales.md`'s `q=+1` conditional-expectation fixed point. **Itô = `derivative.md` ∘
   `gaussian_clt.md` ∘ `martingales.md` at √h resolution** — no new primitive.

2. **Residue surfaced — the Itô correction `½f''dt` IS the second-order residue, and `[B]_t = t` IS
   its non-vanishing surplus.** The deepest line: `derivative.md`'s residue is the O(h²) term the
   `h→0` modulus discards (below the floor). Itô's whole content is that **the √h scaling lifts that
   exact residue above the floor**: `(ΔB)² = O(h)` is first-order, so the squared-difference reading
   `liftKZ 2`, weighted by `½f''`, does not vanish — it is promoted to the *visible* term `½f''dt`.
   `[B]_t = t` is the **non-zero surplus of the squared-increment reading** — the residue of
   `derivative.md`'s difference-quotient reading made *visible and load-bearing* by the resolution
   scaling. The `obstruction_int_constant` witness is the Lean shadow: `liftKZ 2 = 2` (the genuine
   degree-2 structure) is invisible to the first-order Lens (`obstruction_nat`) and visible only one
   resolution-level down — the level √h reaches. "The Itô correction" stops being a separate
   primitive and becomes the calculus's second-order residue at a non-standard scaling.

3. **Forcing — the √h scaling forces the ½f''dt term, and the `q=±1` bit forces the drift/martingale
   split.** Whether the second-order residue vanishes (smooth resolution, ordinary calculus — O(h²)
   below the floor) or survives (√h resolution, Itô — `[dB]² = dt` at the floor) is **forced by the
   resolution scaling alone**, not added by hand: it is the single dial-position where `derivative.md`'s
   dropped term is load-bearing. And the split `df = f'dB + ½f''dt` is `martingales.md`'s Doob split
   on the resolution axis — the `f'dB` part is the `q=+1` martingale (the fixed point of refinement;
   `E[f'dB|F]=0`), the `½f''dt` part is the **directed `q=±1` residue** (a deterministic drift with a
   fixed sign, the same orientation fold as ℤ/`det`/`∂`/the Doob compensator). The Itô isometry is
   then forced as `mass_conv`'s second-moment multiplicativity over independent (`×↦·`,
   `joint_assoc_num`) increments — the variance-adds fact (`CLT_fair_variance_marker`).

**THE NEW DATUM (vs `martingales.md`/`derivative.md` — the re-skin guard): the resolution axis carries
a SCALING, and the Itô correction is `derivative.md`'s dropped second-order residue revived by it.**
`martingales.md` consolidated the *weight* axis (the conditional-expectation `q=+1` fixed point at
discrete refinement — no scaling). `derivative.md` opened the *resolution* axis but read `L₋` only to
first order and *dropped* the O(h²) term. Itô is the genuinely new intersection: **the resolution
axis read to second order at a `√h` scaling, where `derivative.md`'s dropped residue becomes
load-bearing.** The single deepest find:

| | what is read | resolution | second-order term | Lean shadow |
|---|---|---|---|---|
| `derivative.md` (smooth `d/dx`) | `L₋` once | adjacency at `h` (increment O(h)) | O(h²), **dropped** below the floor (the "+C"/forgetting residue) | `diffZ`, modulus; `liftKZ 2` contributes nothing at the limit |
| **`ito_calculus.md` (Itô)** | `L₋` **twice** | adjacency at **√h** (increment O(√h)) | `(ΔB)²=O(h)` **first-order, SURVIVES** as `½f''dt` | `liftKZ 2`, `obstruction_int_constant` (2nd diff = 2, invisible to 1st-order Lens) |

So **YES** — Itô calculus = `derivative.md`'s difference-reading with the **second-order residue made
load-bearing by the √h Brownian resolution scaling**. The Itô formula `df = f'dB + ½f''dt` is
`⟨C|L_derivative⟩ ⊕ Residue` with `½f''dt` the residue **promoted to a visible term**; quadratic
variation `[B]_t = t` is that residue's non-vanishing surplus; the Itô integral is the weight axis
(`probability.md`) at this resolution and a `q=+1` martingale (`martingales.md`); the Itô isometry is
the second-moment / mass-conservation character (`mass_conv`/`momentNum_conv`). No new primitive — it
is `derivative.md` read at the one dial-position where its dropped O(h²) term survives. The precise
missing leg is the named Itô *object*: `BrownianMotion`, `ItoIntegral`, `quadraticVariation`, and the
Itô-formula / isometry / martingale-property statements.

## Note for the technique — does Itô force a NEW construct?

**One sharpening, no new primitive — EXTEND, a resolution-axis find.** This decomposition adds nothing
to model v7.1's invariant set; it *uses* existing slots and sharpens the resolution axis with a
**scaling parameter**:
- *Brownian motion* = `gaussian_clt.md`'s `q=+1` convolve-rescale fixed point read as a process — no
  new construction, the same point-construction `derivative.md`/`integration.md` carry;
- *the Itô formula* = `derivative.md`'s difference-reading dialed to √h resolution, where its dropped
  second-order term survives — the resolution parameter at one specific scaling;
- *quadratic variation `[B]_t = t`* = the README's `Residue(L,C)` (the second-difference reading's
  non-vanishing surplus), the residue **promoted to a visible term**;
- *the Itô integral's martingale property* = `martingales.md`'s `q=+1` conditional-expectation fixed
  point (`banach_fixed_point_modulated`/`golden_is_converge`);
- *the Itô isometry* = the second-moment / mass-conservation character (`mass_conv`/`momentNum_conv`)
  carried by the independence (`×↦·`, `joint_assoc_num`) of disjoint increments.

The one genuine sharpening for the technique: **the resolution parameter on `L` (`derivative.md`)
carries a SCALING — how the increment size scales with the adjacency step (`h` for smooth, `√h` for
Brownian) — and that scaling decides whether the second-order residue vanishes or becomes
load-bearing.** This is the cleanest demonstration to date that a *residue the calculus normally drops
below the resolution floor* can be **promoted to a primary term by changing the resolution scaling** —
the Itô correction is not a new object but `derivative.md`'s discarded O(h²) residue, revived. It
parallels `padic.md`'s lesson (the resolution axis carries a *base*: which metric is "adjacent") and
extends it: the resolution axis carries a *scaling* too (how the increment scales with the step). The
calculus thus *predicts* the Itô formula (the surviving second-order residue), quadratic variation
(the residue's surplus), the martingale property (the `q=+1` fixed point), and the isometry (the
second-moment character) from the model's slots, not from stochastic analysis added on top.

---

## Verified Lean anchors (file:line:theorem — all grep-verified; purity by `tools/scan_axioms.py`, re-run this session from repo root)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| **the SECOND difference-reading `liftKZ 2` — the discrete second-order operator behind `½f''`/`[B]_t`** | `Lib/Math/Analysis/Cauchy/NewtonGregory.lean : liftKZ` (`:57`, `liftKZ(k+1)=diffZ∘liftKZ k`), `diffZ` (`:54`) | ∅-axiom ✓ (41/0) |
| **★ the second-order residue is non-trivial and INVISIBLE to the first-order Lens** (the Itô-scaling shadow) | `Lib/Math/Analysis/Cauchy/NewtonGregory.lean : obstruction_int_constant` (`:404`, `liftKZ 2 ↑vObs = 2`), `obstruction_nat` (`:395`, `¬polyDepth 2 vObs`) | ∅-axiom ✓ (PURE, by `decide`) |
| applying the difference-reading lowers the resolution-order by one (the level √h reaches) | `Lib/Math/Analysis/Cauchy/DepthCharacterization.lean : polyDepthZ_succ_of_diff` (`:59`), `diffZ_binomColZ` (`:72`) | ∅-axiom ✓ (PURE) |
| **the Taylor/`dsq` second-order shape — `½f''·[dB]²` as the graded second-order residue; Itô product rule = Leibniz + the extra `df·dg`** | `Lib/Math/Cohomology/Delta/V4Capstone.lean : leibniz_universal_delta4` (`:62`), `dsq_zero_universal_delta4` (`:41`) | ∅-axiom ✓ (5/0) |
| **Brownian increment = the `q=+1` convolve-rescale fixed point** (the same Gaussian as `gaussian_clt.md`) | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean : Φ_contraction` (`:345`), `orbit_to_center` (`:471`), `center_fixed` (`:419`) | ∅-axiom ✓ (20/0) |
| the completion-limit (Brownian center reached-by-none) | `Lib/Math/Probability/Limit/DyadicCompletion.lean : orbit_to_center_completion` (`:366`), `gaussian_center_fixed_via_engine` (`:612`) | ∅-axiom ✓ (32/0) |
| **`[B]_t = t` = the preserved second moment** (the residue's finite generator) | `Lib/Math/Probability/Foundation/Variance.lean : variance_master` (`:44`); `Lib/Math/Probability/Distribution/Gaussian.lean : CLT_fair_variance_marker` (`:85`), `CLT_fair_centered` (`:74`) | ∅-axiom ✓ (Variance 4/0, Gaussian 9/0) |
| **the Itô integral is a martingale = the `q=+1` conditional-expectation fixed point** (the engine — shared with φ, Gaussian, ODE, the martingale) | `Lib/Math/Foundations/ResidueTag.lean : converge_residue_fixed` (`:160`), `golden_is_converge` (`:180`), `residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`), `escape_residue_outside` (`:133`); `Lib/Math/Analysis/BanachFixedPointModulated.lean : banach_fixed_point_modulated` (`:111`), `picardLim` (`:95`) | ∅-axiom ✓ (ResidueTag 55/0; BanachFixedPointModulated PURE) |
| **the Itô isometry = the second-moment / mass-conservation character** (`E[(∫fdB)²]=E[∫f²dt]`) | `Lib/Math/Probability/Limit/ConvolveProfile.lean : mass_conv` (`:190`, `×↦·`), `momentNum_conv` (`:239`, `+↦+`) | ∅-axiom ✓ (20/0) |
| independence of disjoint increments = `×↦·` character | `Lib/Math/Probability/Foundation/Independence.lean : joint` (`:27`), `joint_assoc_num` (`:87`) | ∅-axiom ✓ (12/0) |
| the value-weighted accumulation `∫f dB` + linearity | `Lib/Math/Probability/Foundation/Expectation.lean : discreteNum` (`:27`), `discreteNum_append` (`:62`) | ∅-axiom ✓ (5/0) |
| the `L¹`/finiteness control (the weight-bound) | `Lib/Math/Probability/Inequality/Markov.lean : markov_inequality` (`:66`) | ∅-axiom ✓ (6/0) |
| the first-order term `f'dB` = `derivative.md`'s difference-Lens at residue resolution (prior) | `derivative.md`/`integration.md` anchors (`diffZ`, `PolySumDerivativeModulus`, `RiemannIntegralData.limit`, `gauss_conservation_telescope`) | cited, prior ✓ |

> Axiom-purity note: every module above was re-run through `tools/scan_axioms.py` from repo root this
> session — V4Capstone 5/0 (`dsq_zero_universal_delta4`, `leibniz_universal_delta4` both PURE),
> NewtonGregory 41/0 (`obstruction_int_constant`, `obstruction_nat` both PURE), DepthCharacterization
> PURE on both cited names, ConvolveRescaleContraction 20/0, DyadicCompletion 32/0, Variance 4/0,
> Gaussian 9/0, ResidueTag 55/0, ConvolveProfile 20/0, Independence 12/0, Expectation 5/0, Markov 6/0.
> `BanachFixedPointModulated`'s headline reports PURE (its public names live under the
> `CompleteMetricModulusMod`/`CompleteMetricModulus` structures; `ResidueTag.converge_residue_fixed`
> delegates to it and is PURE in the 55/0 scan).

### Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

- **No `BrownianMotion` / `Wiener` / `stochastic` object** — grep (case-insensitive) for
  `BrownianMotion`/`brownian`/`wiener`/`stochastic` returns **0** hits. The increment law exists
  (`gaussian_clt.md`'s convolve-rescale `q=+1` fixed point) but is **not instantiated as a process**
  on the √h-scaled time axis; the resolution-scaling parameter (√h) is the implicit dial
  `derivative.md` named but never built. **Predicted-not-built.**
- **No `quadraticVariation` / `[B]_t = t` object** — grep for `quadraticVariation`/`quadratic_variation`
  returns **0** hits. The second-difference operator (`liftKZ 2`) and the preserved second moment
  (`variance_master`/`CLT_fair_variance_marker`) exist; the accumulation "`Σ(ΔB)² → t`" as one
  statement is unbuilt. The `obstruction_int_constant` witness (`liftKZ 2 = 2`, non-trivial,
  first-order-invisible) is the structural shadow. **Predicted-not-built.**
- **No `ItoIntegral` / `∫f dB` object and no Itô-formula theorem `df = f'dB + ½f''dt`** — grep for
  `ItoIntegral`/`ito` returns **0** hits. All the pieces are built (the first-order reading, the
  second-order residue `liftKZ 2`/`dsq`/Leibniz, the `q=+1` martingale, the weight accumulation); the
  substitution "the second-order term survives at √h and is promoted to `½f''dt`" is the conceptual
  weld. **Predicted-not-built.**
- **No Itô-isometry theorem `E[(∫f dB)²] = E[∫f² dt]`** — `mass_conv`/`momentNum_conv` +
  `joint_assoc_num` are the predicted resolver (second moment multiplies under independence); the
  isometry as one statement is unbuilt. **Predicted-not-built.**
- **No martingale-property-of-the-stochastic-integral theorem `E[∫f dB | F]=0`** — the `q=+1` engine
  (`banach_fixed_point_modulated`/`golden_is_converge`) is the predicted resolver; `martingales.md`
  reports the *same* missing `Martingale`/`condExp`/`Filtration` objects (grep-confirmed absent there).
  **Predicted-not-built.**

### Verified buildable witness (genuinely true + terminating, the second-order-residue shadow)

`NewtonGregory.lean:404` `obstruction_int_constant` is the existing ∅-axiom witness that **the
second-order difference-reading is non-trivial (`liftKZ 2 ↑vObs = 2`) and invisible to the first-order
Lens** (`obstruction_nat`, `¬ polyDepth 2 vObs`) — verified PURE this session, the exact structural
shadow of "the Itô correction survives only at second-order resolution." No new buildable witness is
proposed here (the genuine missing leg is the named `BrownianMotion`/`ItoIntegral` object + the √h
scaling on `L`, not a one-line `decide`; a buildable next step is a Bernoulli-random-walk
`Σ(ΔB)² = n·(step)²` exact identity at fair coin, the discrete `[B]_t` toy, paralleling
`gaussian_clt.md`'s `fair_profile_doubled` — but that is a promotion target, not asserted here).
