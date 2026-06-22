# Decomposition: distribution theory / generalized functions

*213-decomposition of distribution theory — test functions, distributions as continuous linear
functionals `T : φ ↦ ⟨T,φ⟩`, the Dirac δ, distributional derivatives (integration by parts), the
Fourier transform of tempered distributions, convolution, and weak/distributional PDE solutions, per
`../README.md` (model v7.1). The bar is **leverage / revelation, consolidating the calculus's own
reflexive core** (the "object = its readings" theme: `view_factors_through_morphism`,
`object1_injective`/`object1_not_surjective`, `raw_initial`) with three neighbour entries: `fourier.md`
(the character by duality), `measure.md` (the functional / point-mass δ), `integration.md` (integration
by parts = the telescope), and `convex_duality.md` (the dual pairing). Hypothesis: distribution theory
is not a new field — it is the calculus's reflexive **"object = its readings"** principle **made the
definition**, with the distributional derivative = the integration-by-parts telescope carrying the
`q=±1` adjoint sign.*

This entry is split into a **grounded core** (the reading-as-pairing `view_factors_through_morphism`,
the point-evaluation reading `Object1`/δ, the telescope `gauss_conservation_telescope`/Leibniz, the
`q=±1` orientation bit `dsq_zero`/`leibniz_universal_delta4`, the convolution `mass_conv`/`momentNum_conv`)
and a **flagged conceptual leg** (the named `Distribution`/`testFunction`/`Dirac`/`tempered`/
`weak_solution` *objects* — all **absent**, grep-confirmed, located precisely like `convex_duality.md`
located its missing `f*` and `knots.md` its boundary).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the SAME point-construction as `integration.md`/`measure.md`: a construction of
  points (a `Real213` cut / dyadic bracket-tree, points = refinement residues never held) with a
  value-construction hung at each. A "test function" `φ` is a reading-over-`C` (a smooth, compactly
  supported value-readout); the function-space the distribution acts on is the *family of readings* of
  the point-construction. Nothing distribution-theoretic is a primitive — there is no `Distribution`
  type, no `TestFunction` type (grep-confirmed absent, below).

- **Reading `L` — "the object IS its action on every test function," `T : φ ↦ ⟨T,φ⟩` = `Lens.view`
  promoted to the definition.** This is the central hypothesis and the calculus's deepest reflexive
  theme made literal. A distribution is *not a function*; it is the **functional that reads every test
  function**. That is exactly the calculus's `OBJECT = ⟨C|L⟩` with the reading slot made primary:
  - `view_factors_through_morphism` (`Lens/Compose/Morphism.lean:37`, PURE) is "an object's value is
    determined by reading it through `L`" — `M.view r = h (L.view r)`. The yoneda/motives theme: an
    object is recovered from its readings.
  - `object1_injective` (`FlatOntologyClosure.lean:47`, PURE): `Object1 : Raw → (Raw → Bool)` is
    **injective** — "an element is determined by the set of all its readings." This *is* the separating
    property of distribution theory (`⟨T,φ⟩ = ⟨S,φ⟩` for all `φ` ⟹ `T = S`): the functional view is
    faithful. The distribution-theoretic axiom "a distribution is determined by its action on test
    functions" is `object1_injective` read on the function-pairing.
  - `raw_initial` (`SemanticAtom.lean:412`, PURE) / `Lens.view = Raw.fold`: reading is the unique arrow
    out of the construction — the "test against everything" pairing is the universal read-op.

- **The Dirac δ = the point-evaluation reading.** `Object1 (r) := fun s => decide (s = r)`
  (`FlatOntology.lean:43`) is **the indicator/point-mass at `r`** — read a candidate `s`, return `true`
  iff it *is* `r`. This is the count-Lens point mass `measure.md` isolated (the bracket-singleton, the
  δ-spike). `⟨δ,φ⟩ = φ(0)` is the **point-evaluation reading**: the functional that reads a test
  function *at one point*. In the calculus's vocabulary δ is the simplest non-trivial member of the
  reading-family — exactly as parity is the simplest member of the character-family (`fourier.md`): δ is
  the **evaluation slot** of the pairing, `Object1` the Lean shadow (`r`'s own indicator IS the
  point-evaluation functional, `Object1 r r = true`, `Object1_self`).

- **Residue — two faces, tagged `q=±1` (the `ResidueTag`, README's load-bearing invariant B).**
  1. *The interior residue (`q=+1`, converge):* a general distribution / a convergent `⟨T,φ⟩` over an
     arbitrary `φ` is reached by no finite bracket-list — only narrowed by a Cauchy modulus, the **same
     modulus residue** as `integration.md`/`measure.md`/`continuity.md`. The finite pairing is the
     operand, the limit never is. No new residue kind.
  2. *The exterior residue (`q=−1`, escape):* the predicates **outside** the image of `Object1`
     (`object1_not_surjective`, `FlatOntologyClosure.lean:61`, PURE) — the functionals that read but are
     not represented by a point of the construction. This is *precisely* the distribution-theoretic
     gain: δ (and δ', and a non-measurable / singular distribution) is **a functional with no
     representing function** — the residue surplus of the self-cover, the same `q=−1` diagonal as
     Cantor/Gödel/Vitali. "A distribution is more general than a function" = "the reading-functional
     overshoots the image of the point-construction" = `object1_not_surjective`.

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   test function φ           =  a reading-over-C  =  a value-readout of the point-construction
   distribution T            =  ⟨ C | the pairing φ ↦ ⟨T,φ⟩ ⟩   =  Lens.view made the OBJECT
                               (object1_injective: T determined by ⟨T,·⟩ on all φ — the yoneda theme)
   "T determined by its action" =  object1_injective  (faithful self-cover; the separating axiom)
   Dirac δ,  ⟨δ,φ⟩ = φ(0)    =  the point-evaluation reading  =  Object1 r = (s ↦ decide(s=r))
                               (measure.md's point mass; Object1_self the spike)
   distributional deriv      =  ⟨T',φ⟩ = −⟨T,φ'⟩  =  integration-by-parts = the TELESCOPE
                               (gauss_conservation_telescope: interior cancels, boundary survives)
   the minus sign            =  the q=±1 orientation bit  =  the adjoint of d
                               (dsq_zero_universal_delta4; leibniz_universal_delta4's XOR)
   Fourier of tempered T     =  ⟨T̂,φ⟩ = ⟨T,φ̂⟩  =  fourier.md's character extended BY DUALITY
                               (the ×↦· character on the dual; quadratic_orthogonality the cashed leg)
   convolution (T⋆S)         =  the weight-axis Cauchy convolution
                               (mass_conv: mass multiplies ×↦· ; momentNum_conv: mean adds +↦+)
   weak / distributional soln =  solve in the READ/PAIRED sense, not pointwise = the Lens-level equation
   T with no representing fn  =  Residue(L,C), q=−1  =  object1_not_surjective (REACHED BY NONE)
```

**(1) A distribution IS the calculus's "object = its readings," made the definition.** Classical analysis
treats a function as the primary object and its integral pairings as derived. Distribution theory
*inverts* this: the pairing `φ ↦ ⟨T,φ⟩` is the object, and a locally-integrable function is recovered as
the special case `⟨T_f,φ⟩ = ∫ f·φ`. This inversion is **the calculus's founding move**
(`README` §"What it is": "every mathematical object is a construction read through a lens"), promoted from
a methodological stance to a field's definition. `object1_injective` is the certificate that the move is
sound: the reading-family is faithful, so "the functional" loses nothing. This is the yoneda/motives
reflexive theme (`SYNTHESIS.md` §2 "motives are the `⟨C|L⟩` half") instantiated as an analysis discipline.

**(2) The distributional derivative = integration by parts = the telescope, carrying the `q=±1` adjoint
sign.** `⟨T',φ⟩ = −⟨T,φ'⟩` is *defined* by integration by parts (the boundary term vanishes on compactly
supported `φ`). That is exactly `integration.md`'s telescope: `gauss_conservation_telescope`
(`TelescopingConservation.lean:152`, PURE) proves every **interior wall cancels** and only the **outer
boundary cuts survive**. Compact support kills the boundary, leaving the interior-cancellation — the
derivative is moved onto `φ` and the **sign flips**. The flip is not bookkeeping: it is the README's
**`q=±1` orientation bit**, the *adjoint of `d`*. `dsq_zero_universal_delta4` (`V4Capstone.lean:41`, PURE)
is `∂²=0` forced by opposite-order face removals carrying opposite orientation signs that cancel
(`homology.md`); `leibniz_universal_delta4` (`V4Capstone.lean:62`, PURE) is the Leibniz/product rule
`δ(α⌣β) = δα⌣β XOR α⌣δβ` — the **same shape as `(fg)' = f'g + fg'`**, the XOR being the orientation bit.
So the distributional derivative's defining minus is `derivative.md`'s difference-Lens run as the
**adjoint** of `d` on the pairing — `Σ⊣Δ` / `∫⊣d` (FTC) with the boundary discharged by compact support.

**(3) The Fourier transform of tempered distributions = `fourier.md`'s character extended by duality.**
The transform on tempered distributions is *defined* by `⟨T̂,φ⟩ = ⟨T,φ̂⟩` — move the (built, on the test
function) transform across the pairing. This is `fourier.md`'s `×↦·` character (`legendre_mul`,
`qr_pow_iff_even_exp`) reflected onto the dual via the *same* reading-as-pairing the whole entry rests
on. The cashed leg is `fourier.md`'s `quadratic_orthogonality` / the order-2,3,4,6 root-of-unity
orthogonality (`ModArith/CharacterOrthogonality`, `CayleyDickson/.../RootOfUnityOrthogonality`); the
**analytic transform kernel `ζ^x` and the full tempered-distribution transform are the `Real213`-cut
residue** `fourier.md` already located (the "Transcendental-as-residue" row). δ̂ = the constant function
is the duality-defined statement `⟨δ̂,φ⟩ = ⟨δ,φ̂⟩ = φ̂(0) = ∫φ` — the point-evaluation reading paired with
the character; combinatorially grounded only via the multiplicative-character machinery, analytically
the located cut.

**(4) Convolution = the weight-axis Cauchy convolution `mass_conv`/`momentNum_conv`.** `T⋆S` is exactly
`generating_functions.md`/`gaussian_clt.md`'s convolution, *built* and PURE: `mass_conv`
(`ConvolveProfile.lean:190`) — total mass multiplies (`×↦·`, the same arrow), `momentNum_conv`
(`:239`) — first moment adds (`+↦+`, the additive twin). "δ is the convolution identity" (`δ⋆T = T`) is
the point-evaluation reading acting as the unit of `⋆` (the `mass_conv`/`momentNum_conv` unit case,
`ConvolveProfile.lean:182-185`). No new mechanism — distributional convolution is the built weight-axis
convolution read on the functional.

**(5) Weak / distributional solutions = the Lens-level equation.** A weak solution solves a PDE *in the
paired sense* `⟨Lu,φ⟩ = ⟨f,φ⟩` for all test `φ`, rather than pointwise. This is "solve the equation at
the reading level" — the same move as `equivalence.md`'s `Lens.refines` (two objects agree *as read*)
and `measure.md`'s "equal almost everywhere = equal as weights." The PDE is read through every `φ`; by
`object1_injective` a weak solution that is regular enough *is* the classical one (the readings being
faithful), and a weak solution with no classical representative is the `q=−1` residue (a solution that
exists only as a functional — the existence-before-regularity that makes distributions indispensable for
PDE).

## LEVERAGE — the Revelation

**Verdict: PREDICTION + consolidation (a deep one) — the calculus PREDICTS that distribution theory is
its own reflexive "object = its readings" core made into an analysis discipline, with no new primitive;
one real PARTIAL, the named `Distribution`/`testFunction` objects absent, located precisely.**

Three moves, in increasing depth, all grep/scan-grounded:

1. **Collapse — distribution theory is ONE `(C,L)`: the reading-as-pairing, which is the calculus's
   founding normal form.** The whole field is `⟨ point-construction | the pairing φ↦⟨T,φ⟩ ⟩ ⊕
   Residue(q=±1)`. δ, the distributional derivative, the tempered-distribution Fourier transform,
   convolution, and weak solutions are **not five constructions** — they are five readings of one
   functional object: δ = the point-evaluation slot (`Object1`), `T'` = the telescope-adjoint
   (`gauss_conservation_telescope` + the `q=±1` sign), `T̂` = the character by duality (`fourier.md`),
   `T⋆S` = the weight-axis convolution (`mass_conv`/`momentNum_conv`), the weak solution = the
   Lens-level equation (`object1_injective`).

2. **Forcing — the functional view is forced sound, and δ's "no representing function" is forced as the
   `q=−1` residue.** "A distribution is determined by its action on all test functions" is not an
   axiom to assume — it is `object1_injective` (the self-cover is faithful), PURE. And "δ is more than a
   function" is not a paradox to manage — it is `object1_not_surjective` (the self-cover overshoots),
   PURE: the reading-functional always leaves a surplus *outside* the image of the point-construction,
   which is exactly where δ, δ', and singular distributions live. The calculus *predicts* both the
   soundness (faithful) and the necessity (never total) of generalized functions from the one
   `self_covering_closure` theorem (`FlatOntologyClosure.lean:69`).

3. **Residue surfaced + the adjoint sign derived — the distributional derivative's minus is the `q=±1`
   orientation bit, not bookkeeping.** Classical analysis introduces `⟨T',φ⟩ = −⟨T,φ'⟩` as "the only
   definition that agrees with integration by parts." The calculus re-sees the minus as the **adjoint of
   `d`** = `homology.md`/`integration.md`'s `q=±1` orientation bit (`dsq_zero_universal_delta4`,
   `leibniz_universal_delta4`'s XOR), the boundary discharged by the telescope's interior-cancellation
   (`gauss_conservation_telescope`) under compact support. So the sign is *derived* (it is the same bit
   that gives `∂²=0` and the Leibniz XOR), not relabeled — passing the re-skin guard at the highest bar.

This is genuine leverage, not re-skin: the field is *predicted* to be the calculus's reflexive core made
a definition (a prediction about what distribution theory *is*, grounded in `object1_injective` +
`object1_not_surjective` + the telescope), and the derivative's sign is *derived* from the `q=±1` bit.

## Revelation

**Distribution theory is the calculus's "object = its readings" (yoneda/motives) reflexive theme
PROMOTED FROM METHOD TO DEFINITION — a distribution IS its pairing `⟨T,φ⟩` = `Lens.view` as the primary
object — with the distributional derivative = the integration-by-parts telescope carrying the `q=±1`
adjoint sign.** This is **collapse + forcing + residue-surfaced**, three at once:

- **collapse:** δ / `T'` / `T̂` / `T⋆S` / weak-solution = five readings of one functional object;
- **forcing:** the functional view's faithfulness (`object1_injective`) and δ's non-representability
  (`object1_not_surjective`) are forced by `self_covering_closure`, not assumed;
- **residue-surfaced:** "generalized function" = the `q=−1` surplus of the reading self-cover (the
  predicates outside `Object1`'s image), the convergent-distribution limit = the `q=+1` modulus.

The deepest datum: the calculus's *founding sentence* — "every object is a construction read through a
lens" (`README` §"What it is") — has a field whose **entire content is that sentence taken as the
definition of its objects**. Where `motives.md` named the `⟨C|L⟩` half abstractly and `homological_algebra.md`
named the `Residue(L,C)` half, distribution theory is the **analysis discipline** built on the same
reflexive turn: the functional is the object, the test functions are the readings, the singular
distributions are the residue.

| pillar | 213 reading | prior entry | Lean status |
|---|---|---|---|
| `T : φ ↦ ⟨T,φ⟩` (object = readings) | `Lens.view` as the object; faithful self-cover | yoneda/motives core | **built** (`view_factors_through_morphism` 3/0; `object1_injective` 7/0) |
| Dirac δ, `⟨δ,φ⟩=φ(0)` | the point-evaluation reading / point mass | `measure.md` | **built shadow** (`Object1`, `Object1_self`; no named `Dirac`) |
| distributional derivative `⟨T',φ⟩=−⟨T,φ'⟩` | integration-by-parts telescope + `q=±1` adjoint sign | `integration.md` / `homology.md` | **built** (`gauss_conservation_telescope` 8/0; `dsq_zero`/`leibniz_universal_delta4` 5/0) |
| Fourier of tempered T `⟨T̂,φ⟩=⟨T,φ̂⟩` | the `×↦·` character by duality | `fourier.md` | **partial** (`quadratic_orthogonality`/`i_orthogonality`; analytic kernel = `Real213` cut) |
| convolution `T⋆S` | weight-axis Cauchy convolution | `generating_functions.md`/`gaussian_clt.md` | **built** (`mass_conv`/`momentNum_conv` 20/0) |
| weak solution | the Lens-level (paired) equation | `equivalence.md`/`measure.md` | **shadow** (`object1_injective`; no named `weak_solution`) |
| singular distribution (no rep. fn) | `Residue(L,C)`, `q=−1` escape | `cardinality.md`/`ResidueTag` | **built** (`object1_not_surjective` 7/0; `ResidueTag` 55/0) |

## Note for the technique — does distribution theory force a NEW construct?

**Verdict: EXTEND by consolidation — no new primitive, and one sharpening.** Every slot already exists:
- **the reading-as-object / yoneda theme** (`view_factors_through_morphism`, `object1_injective`,
  `raw_initial`) — the distribution IS its pairing;
- **the point-evaluation reading** (`Object1`, `measure.md`'s point mass) — δ;
- **the integration-by-parts telescope** (`gauss_conservation_telescope`) + **the `q=±1` orientation
  bit** (`dsq_zero`, `leibniz_universal_delta4`) — the distributional derivative and its minus sign;
- **the character by duality** (`fourier.md`) — the tempered-distribution Fourier transform;
- **the weight-axis convolution** (`mass_conv`/`momentNum_conv`) — distributional convolution;
- **the `q=±1` residue tag** (`ResidueTag.lean`) — singular vs. convergent distributions.

The one sharpening for the model: distribution theory is the clearest case yet that **the reading slot
`L` can be promoted to the primary object** (the field's defining inversion). The README's "object = its
readings" had been a *description* of how the calculus sees objects; distribution theory shows a whole
discipline takes the description *as the object's definition* — and `object1_injective`
(faithful) + `object1_not_surjective` (never total) is the exact ∅-axiom statement of *why* this both
loses nothing (the regular distributions) and gains everything (the singular residue). No new axis;
a strong consolidation of the calculus's reflexive core (`SYNTHESIS.md` §6).

## Verified Lean anchors (file:line:theorem — all grep-confirmed; purity by `tools/scan_axioms.py` this session)

| Leg | Theorem (file:line : name) | Scan |
|---|---|---|
| object = its readings (the pairing is faithful / determined by readings) | `Lens/Compose/Morphism.lean:37 : view_factors_through_morphism` (`M.view r = h(L.view r)`); `:29 IsLensMorphism`; `:60 refines_of_morphism` | **3 pure / 0 dirty** ✓ |
| "T determined by its action on all φ" (the separating axiom) | `Lens/Foundations/FlatOntologyClosure.lean:47 : object1_injective` (`Object1` injective); `:69 self_covering_closure` | **7 pure / 0 dirty** ✓ |
| Dirac δ = the point-evaluation reading (point mass) | `Lens/Foundations/FlatOntology.lean:43 : Object1` (`r ↦ fun s => decide (s=r)`); `:46 Object1_self` (`Object1 r r = true`, the spike) | (FlatOntology) ✓ |
| singular distribution = `q=−1` residue (functional with no representing function) | `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective` (Cantor self-cover overshoot) | **7 pure / 0 dirty** ✓ |
| read = the universal arrow (the "test against everything" pairing) | `Lens/Foundations/SemanticAtom.lean:412 : raw_initial`; `Lens/Foundations/UniversalDistinguishing.lean:103 : dhom_unique_pointwise` | `raw_initial` PURE ✓ |
| distributional derivative = integration-by-parts telescope (interior cancels, boundary survives) | `Lib/Math/Analysis/FluxMVT/TelescopingConservation.lean:152 : gauss_conservation_telescope` | **8 pure / 0 dirty** ✓ |
| the minus sign = the `q=±1` adjoint/orientation bit | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4` (`∂²=0`); `:62 leibniz_universal_delta4` (Leibniz `δ(α⌣β)=δα⌣β XOR α⌣δβ`) | **5 pure / 0 dirty** ✓ |
| `∫` = inverse of `d` (the pairing-side FTC) | `Lib/Math/Analysis/Integration/IntegralViaAnti.lean:47 : integral_eq_flux` (by `rfl`) | cited (per `integration.md`) ✓ |
| convolution `T⋆S` = weight-axis Cauchy convolution | `Lib/Math/Probability/Limit/ConvolveProfile.lean:190 : mass_conv` (`×↦·`); `:239 momentNum_conv` (`+↦+`); `:268 profileMean_conv` | **20 pure / 0 dirty** ✓ |
| Fourier of tempered T = the character by duality (cashed at orders 2/3/4/6) | `fourier.md` anchors: `ModArith/CharacterOrthogonality.quadratic_orthogonality`; `CayleyDickson/Integer/{RootOfUnityOrthogonality,GaussianOrthogonality}` | cited (per `fourier.md`) ✓ |
| the `q=±1` residue tag (singular vs convergent distribution) | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`; `:86 multiplier_unimodular`; `:133 escape_residue_outside`; `:160 converge_residue_fixed` | **55 pure / 0 dirty** ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):** `Lens.Compose.Morphism` =
3/0; `Lens.Foundations.FlatOntologyClosure` = 7/0; `Lens.Foundations.SemanticAtom` (`raw_initial`) =
PURE; `Lib.Math.Analysis.FluxMVT.TelescopingConservation` = 8/0; `Lib.Math.Cohomology.Delta.V4Capstone`
= 5/0; `Lib.Math.Probability.Limit.ConvolveProfile` = 20/0; `Lib.Math.Foundations.ResidueTag` = 55/0.
All cited theorems PURE.

## Dropped / flagged — the named distribution-theory objects are ABSENT (grep-confirmed)

The decisive honest datum: **distribution theory's named objects do not exist in `lean/E213`.**
- **`Distribution` / `TestFunction` / `LinearFunctional` / `Functional` (typed objects)** — grep for
  `structure Distribution|def Distribution|structure TestFunction|def testFunction|structure Functional|`
  `abbrev Distribution|: Functional|LinearFunctional` over `lean/E213` returns **zero hits**. There is no
  `T : 𝒟' → ℝ` functional type, no `𝒟` test-function space, no continuity-of-functional predicate.
  Predicted-not-built, confirmed.
- **`Dirac` / `delta_distribution` (named δ)** — no named Dirac-distribution object; the *shadow* is
  `Object1` (the point-evaluation indicator) and `measure.md`'s `measure_singleton` (the point mass).
  The δ *as a distribution* (a functional `φ↦φ(0)`) is conceptual; only the point-mass reading is built.
- **`tempered` (Schwartz space / tempered distributions)** — the `tempered` grep hits are unrelated
  (probability/CayleyDickson naming); no Schwartz-space or tempered-distribution object exists. The
  tempered-distribution Fourier transform is conceptual; the *character* it extends is built (`fourier.md`,
  orders 2/3/4/6), the analytic kernel `ζ^x` / the full transform is the `Real213`-cut residue.
- **`weak_solution` (distributional PDE solution)** — no named weak-solution object; the shadow is
  `object1_injective` (paired equality ⟹ equality where readings are faithful) and `equivalence.md`'s
  `Lens.refines`. The Lax–Milgram / Sobolev-space apparatus is absent.
- **General convergent `⟨T,φ⟩` over arbitrary `φ`** — the modulus residue (`integration.md`'s own open
  leg); only the finite pairing / telescope skeleton is built.

**Verified buildable witness the calculus names precisely.** The closest concrete weld (parallel to
`ConvolveRescaleContraction` welding the Banach engine to the CLT, and `FenchelMoreau` welding the
antitone closure to convex duality): define `diracFunctional (r : Raw) : (Raw → Bool) → Bool :=`
`fun φ => φ r` (evaluation at `r`), and prove it is **represented by `Object1 r`** —
`diracFunctional r = (· r) ∘ id` with `Object1 r` its kernel — i.e. show the point-evaluation functional
is exactly the `Object1`-row, welding "δ = the point-evaluation reading" to a real ∅-axiom statement
(`Object1_self` already gives `diracFunctional r (Object1 r) = true`, the spike). This would promote the
δ-leg from *shadow* to a closed derivation while staying inside the built `FlatOntology` corner. The
named `Distribution`/`𝒟`/tempered/weak-solution objects remain the located absence — exactly the shape
of `convex_duality.md`'s missing `f*` (the closure *structure* is present and PURE; only the
analysis-level *instance* is unwritten).

## Verdict: PREDICTION + consolidation (the reflexive core made a definition), one PARTIAL

Distribution theory **predicts and consolidates** — it does not break the model and adds no axis. The
load-bearing claim is the calculus's own founding sentence: a distribution IS its action on test
functions = `Lens.view` made the object (yoneda/motives), faithful by `object1_injective`, with the
singular distributions = the `q=−1` residue (`object1_not_surjective`). Every structural leg is grounded
∅-axiom: the reading-as-pairing (`view_factors_through_morphism` 3/0, `object1_injective` 7/0), the
point-evaluation δ (`Object1`/`Object1_self`), the integration-by-parts telescope
(`gauss_conservation_telescope` 8/0) with the **`q=±1` adjoint sign derived** (`dsq_zero`/
`leibniz_universal_delta4` 5/0), the convolution (`mass_conv`/`momentNum_conv` 20/0), and the residue tag
(`ResidueTag` 55/0). The Fourier leg is `fourier.md`'s character by duality (cashed at orders 2/3/4/6,
analytic kernel the `Real213` cut). The one PARTIAL is the **named `Distribution`/`testFunction`/`Dirac`/
`tempered`/`weak_solution` objects** — absent (grep-confirmed), located precisely: the reading-as-object
*structure* they inhabit is present and certified, only the analysis-level *instances* are unwritten.
