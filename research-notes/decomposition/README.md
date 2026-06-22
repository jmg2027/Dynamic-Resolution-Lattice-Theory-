# The 213 Decomposition Calculus — a human-facing technique for *seeing* mathematics

**Status**: new research cluster (Tier 1, actively evolving — the shape *will* change as we
practice; that is expected). This is the **originator's central direction**: not "re-derive classical
theorems in Lean" (that is scaffolding) but *create a way of doing/describing mathematics* — the way
category theory created objects/arrows/functors, type theory created types/terms/judgments — and then
**decompose existing mathematics into it**. Raw/Lens are the *Lean encoding* (the machine verifier);
**this is the form a human reads and writes.** 0-axiom is just the discipline the purpose forces.

> **★ Capstone map: [`SYNTHESIS.md`](SYNTHESIS.md)** — the whole corpus as one statement: 52 fields
> reduce to **two invariants** (the character arrow `×↦·`/`×↦+`, the `q=±1` residue tag) over four axes;
> the `q=±1` spine (escape: Cantor/Gödel/measure/quintic/… ⟷ converge: φ/Gaussian/ODE/ergodic/…); the
> Lean census (~21 ∅-axiom modules, 12 of 13 predictions closed); the recurring breaks (the
> ambient-isotopy/colimit quotient verbatim in knots + π₁; the propext ceiling; the `Real213` value-cut);
> and the self-description (the PURE/DIRTY boundary IS the Heyting/Boolean boundary = why 213 is constructive).
> Read it first for the bird's-eye; the per-field notes below are the worked detail.

## What it is

Every mathematical object is a **construction read through a lens**; every theorem is a **property of
a reading**. The calculus writes any piece of mathematics in one normal form:

```
   OBJECT   =   ⟨ C | L ⟩                 C = Construction,  L = Reading
   RESIDUE(L,C)  =  what L forces but cannot capture
   THEOREM:  P(⟨C | L⟩)                    "read C through L and property P holds"
```

- **Construction `C`** — the *distinguishing-history*: what was distinguished from what, iterated.
  The bare generative act, before any feature is chosen. (Lean shadow: a `Raw` / a generation rule.)
- **Reading `L`** — the *Lens*: which feature of the construction you project to — count, order,
  difference, divisibility, parity, ratio, …. A choice of *what to keep and what to forget*. (Lean
  shadow: a `Lens`, i.e. `Raw → α`.)
- **Residue** — what the reading *forces but does not capture*: the surplus a chosen Lens leaves
  un-pointed (often the gap that drives the next concept — e.g. the reals are the residue of the
  rational-approximation reading).

## The decomposition procedure ("to 213-decompose X")

1. **Find the construction.** Strip X to the bare distinguishings that generate the objects it talks
   about. Ask: *what is distinguished from what, and iterated how?*
2. **Name the reading.** Which feature does X actually *use*? (Often X is stated as if about "the
   objects" when it is really about *one projection* of them.)
3. **Locate the residue.** What does this reading force but not capture?
4. **Re-see the theorem, and look for collapse.** Rewrite X as `P(⟨C | L⟩)`. Then ask the
   load-bearing question: *does another, superficially different theorem have the same `(C, L)`?* If
   so they are **one theorem**; that collapse is the payoff.

## The revelation rule (the re-skin guard — non-negotiable)

A decomposition that only *re-describes* X in new words is worthless — it is exactly the
"abstract nonsense" jeer category theory survived, and this repo's own audit verdict ("genuinely new
mathematics: none"). The category theory analogy is the warning *and* the way out: CT was accepted
because its notation eventually **paid** (Yoneda, adjoints, the functor of points let you *do* new
things). So every decomposition must end with an explicit **Revelation** — one of:

- **collapse** — two/many apparently-different things shown to be one `(C, L)`;
- **forcing** — a feature shown to be *forced* by `C` (not an arbitrary choice);
- **residue surfaced** — a concept re-identified as the residue of a reading (so "irrational",
  "infinite", "continuous" stop being separate realms and become *shapes of a reading's surplus*);
- **substance/notation collapse caught** — a place where a Reading had been mistaken for a substance,
  or a Construction-tuple for its flattened readout.

If a decomposition has no Revelation, it is re-skin; drop it or dig deeper. **Lean's role**: verify
the collapse/forcing is *real* (a proven kernel-equality / homomorphism), not asserted — the
honesty-check, not the deliverable.

## Why this is not invented from nothing: the failure-mode catalog *is* this technique's shadow

The strongest evidence the calculus is real: the repo *already lives by it* — negatively. Nearly every
entry in CLAUDE.md's "Failure modes catalog" is **a botched or missed 213-decomposition** — someone
treated a *Reading* as a substance, or a *Construction-tuple* as its flattened readout, or the
*Residue* as a god above the finite. Crystallizing the positive method makes the catalog's discipline
constructive instead of corrective:

| Failure mode (the miss) | The decomposition it failed to do |
|---|---|
| "ℤ / sign as exterior import" | `ℤ = ⟨ directed count-pair `(m,n)` ∣ difference-reading `m−n` ⟩`; sign = pair-swap, not a Raw primitive (`practice/integers.md`) |
| "Equivalence-pluralism" (동치/동형/준동형 as 4 things) | one Lens-arrow `Lens.refines`; the four are facets of `⟨ two Raws ∣ a reading `L` ⟩` (`practice/equivalence.md`) |
| "Quotient promoted to ontology" (the lowest-terms fraction is "the real number") | the *tuple is the object*; `ratio` is a Reading; reduction = *applying* the Lens (flattening the kernel), never the default |
| "Limit/infinity deified" | `lim` = the *residue* of an approximation-reading; its finite signature (the modulus) is the operand, the limit never is |
| "`^`-wall diagnosed via `log`" | the log is an exterior ruler; the `^`-inverse is the **cut** reading; folding decided in the ×-count reading (`exp`) |
| "0/∞ as a stratum-value" | `0`/`∞` = one pre-Lens residue; "value" vs "limit" is a mixed-status reading error |

So the catalog is the *list of ways people fail to decompose*; the calculus is *how to decompose*.

## The practice (this is the research)

The unit of progress is **one worked decomposition with a verified Revelation**. The practice
notebook (`practice/`) decomposes existing mathematics one piece at a time, recording the Revelation
and citing the Lean theorem that certifies it. First batch (crystallizing scattered repo
decompositions into the one procedure):

- `practice/parity.md` — parity, congruence, permutation-sign, `det = ±1` as **one**
  construction-preserving finite reading (Lean: `ModArith.Zolotarev`).
- `practice/integers.md` — ℤ as the difference-reading of a directed count-pair; "negative" is not a
  substance (Lean: `Nat213.Tower.NatPairToInt.npairToInt = Int.subNatNat`).
- `practice/equivalence.md` — 동치 / 동치류 / 동형 / 준동형 = one Lens-arrow (Lean:
  `Lens.refines`, `Unified.lensIso_iff_kernel_eq`).

Then: **fresh** decompositions (math the repo has *not* pre-chewed) — where the technique must
*generate* the seeing, not recall it. That is the real test of the tool.

## Refinements from the first practice batch (the shape changed, as expected)

The first six decompositions (`practice/`) each *forced* an answer to a design question. The calculus,
refined by practice:

**`C` (Construction) carries optional read-off sub-structures — not one flat axis:**
- **direction / swap-bit** → read out as *sign* (ℤ, `integers.md`) and *orientation*; a `Bool`-style
  pair-swap, not a Raw primitive.
- **fold-height / depth** → read out as *dimension / degree / pole-order / nesting* (`dimension.md`).
  **Verdict: first-class** — it pays by collapse (four notions = one height-reading) and is *forced*
  (the well-founded measure already in `C`: `Lambek.isPart_wf`, `Factorization.acc_lt`), so the
  reading only reports what the build had to carry.
- **atom-(in)distinguishability** → the single axis whose two poles are the *scalar* +-construction
  (units indistinguishable, `UnitList.append_comm`) and the *vector* ×-construction (primes
  distinguishable, `FoldCriterion.two_three_unique`) — i.e. *why* multiplication has a per-prime axis
  and addition does not (`prime_factorization.md`).

**`L` (Reading) carries parameters — it is not just a projection:**
- a **resolution** parameter: the *same* Lens at "adjacent = step `1`" (discrete) vs "adjacent via a
  modulus, `h→0`" (residue) unifies `Δ`/`d` and `Σ`/`∫` (`derivative.md`); the limit is never the
  operand, only its finite modulus is.
- a **character / logarithmic** mode: a construction-preserving reading whose readout may *change the
  operation* (`×`↦`+`, `vp_mul`) — generalizing the finite-cyclic "character" of `parity.md` to a free
  ℕ-module readout (`prime_factorization.md`).

**Residue is first-class, and stratifies:** the normal form is really `⟨C | L⟩ ⊕ Residue(L,C)`, the
residue *generated by the reading's own self-application* (`cardinality.md`: the diagonal is `t(f a a)`
— the count-reading re-entering itself; this is §1.0′'s proof-primitive for the infinite). It
*stratifies*: a per-reading residue can be trivial/faithful (the prime-valuation reading is injective,
`vp_separation`/`eq_of_vp_eq`) even while the *global* self-cover non-surjection (`object1_not_surjective`)
is not — "no residue here" and "always a residue globally" coexist.

**One emerging map** (to test further): `C` = distinguishing + {direction, height, atom-distinguishability};
`L` = a reading + {resolution, character-mode}; `Residue` = `L`'s self-application surplus. The deepest
collapses so far sit where two of these meet — `L₋` (difference) where direction (C) meets resolution
(L) gives ℤ *and* the derivative; the count-reading + its residue gives all the limitative theorems.

## Refinements from the second batch (determinant, golden ratio, exponential, continuity)

The fresh batch sharpened the model further:

- **A *character* is a reading whose readout is itself a number-construction** carrying `C`'s own
  direction+height sub-structure (magnitude = the count it scales, sign = the orientation it
  preserves/flips). `det` is exactly this — `det(MN)=det M·det N` (`det2_mul`) is the character `×↦·`,
  with `det=±1` being `parity.md`'s `L₂` and general `det` its multiplicative-scalar extension
  (`determinant.md`). So "character" subsumes parity, sign, det, Legendre — one pattern.
- **Character-mode is *bidirectional*** — a reading `×↦+` (valuation/log) and its inverse `+↦×` (exp)
  are *one arrow with a direction toggle* (which operation is operand vs readout); the residue (the
  `^`-wall, the transcendental `e`) sits *between the two directions*, where faithfulness
  (`vp_separation`) meets the wall (`two_three_unique`) (`exponential.md`).
- **★ The Residue carries a multiplier bit `q = ±1`** — the single biggest structural find. The
  *escaping* residue (Cantor's diagonal, fixed-point-free, oscillates *outside* every reading) and the
  *converging* residue (φ, has a fixed point, asymptotes *toward* one) are **the same residue at the
  two unimodular poles** `q = −1` vs `q = +1` (`CassiniUnimodular.cassini_law_one_at_two_multipliers`,
  `OneDiagonal.no_surjection_of_fixedpointfree`). So `cardinality.md`'s diagonal and `golden_ratio.md`'s
  φ are one object: `Residue(L,C)` should be written with a **`q=±1` tag** = oscillate-outside (q=−1) /
  asymptote-to-fixed-point (q=+1). This is the calculus's deepest collapse: the limitative theorems and
  the golden ratio are one residue read at its two signs.
- **Resolution is an *organizing axis*, not just a parameter** — promoting `L`'s resolution dial to a
  *condition* gives a whole discipline: **topology = the three questions of the dial** — does it commute
  with refinement (continuous map), is its fibre refinement-stable (open set), what is its residue
  (limit point) (`continuity.md`; `IsContinuousModulus`, `uniform_limit_continuous`, `DyadicOpen`, and
  `four_way_modulus_framework` — one modulus structure carries continuity + derivative + Ricci + α_em).

**Updated map**: `C` = distinguishing + {direction, height, atom-distinguishability}; `L` = a reading +
{resolution (→ a whole discipline when made a condition), character-mode (bidirectional)}; `Residue` =
`L`'s self-application surplus, tagged `q = ±1` (escape / converge). Every deepest result sits where two
of these meet. Open Lean targets surfaced: `continuous_iff_preimage_dyadicopen`; a formal `q=±1`
residue tag uniting `object1_not_surjective` and the φ Cassini law. (See
`research-notes/frontiers/decomposition_calculus.md`.)

## Refinements from the third batch (groups, probability) — the model held, and grew

Both were chosen as potential model-breakers; both **EXTEND** with no new primitive — the model is
robust:

- **Readings COMPOSE — a reading can be a *family* closed under composition.** A **group** is
  `⟨C | the closed family of C-preserving self-readings (Aut C), under composition⟩`; the four group
  axioms are *forced* by "relabel-and-compose" (`Linalg213/PermGroup.lean`: identity/inverse/assoc/
  closure as bare list identities), and a *character* is a number-readout *of* that family
  (`mulPerm_comp` + `psign_mulPerm_hom`), one level apart. The abstract shape is the `LensIso` groupoid
  (`lensIso_refl/symm/trans`). So the reading slot must be **closable under composition**; a single
  reading is the trivial-group (`|Aut|=1`) case (`groups.md`).
- **Readings can be *composite*, and `L` gains a `weight` parameter.** **Probability** is the first
  *composite-reading* entry: `P = ratio ∘ count` (`ProbabilityCut` *is* the `QPair = Nat213×Nat213`
  ratio container + a clamp — no `Ω`/σ-algebra type). **Independence = the multiplicative character**
  `×↦·` (the same arrow as `vp_mul`/`det2_mul`/parity), **density = the resolution dial**, and
  **expectation** is the genuine extension: a *value-weighted* count, the additive twin of
  independence's multiplicative character (`Expectation.discreteNum_append` = linearity). So
  `L` = reading + {resolution, character-mode, **weight**}; general measure = weight × resolution (an
  open target the calculus *predicts*) (`probability.md`).

**Model v3**: `C` = distinguishing + {direction, fold-height, atom-distinguishability}; `L` = a reading
(possibly **composite**, possibly a **composition-closed family** = `Aut`) + {resolution, character-mode
(bidirectional), **weight**}; `Residue` = `L`'s self-application surplus, tagged `q = ±1` (escape /
converge). **Readings form a category** (they compose, they have automorphism families) — the
single biggest structural lesson of batch 3. Thirteen decompositions in; no break yet.

## Refinements from the fourth batch (homology, Galois, ordinals, entropy) — and the first leverage

All four **EXTEND**; the model held across **17 decompositions** with no break. The batch added the
deepest structure and the first clear *payoff*:

- **Fold-height is bidirectional** — `∂` (boundary) is the height axis run *downward*
  (`Cᵏ→Cᵏ⁺¹` peels a cell), the exact mirror of distinguishing's height-*raising*. `∂²=0` is **forced
  by the `q=±1` direction bit**: opposite-order face removals carry opposite orientation signs that
  cancel pairwise (`Cohomology/Delta/V4Capstone.dsq_zero_universal_delta4`). And `∂²=0` (nilpotent) vs
  `⋆⋆=id` (involutive) are the **two poles of `q=±1`** at a two-step composite — "nilpotent reading"
  is not new, it is character+direction (`homology.md`). Homology = `Residue(L↓, C)`.
- **Ordinals = the height-reading's residue past every finite stage** — `ω` is the `q=+1` (converging)
  residue of cofinal finite heights, a *third* instance of the `q=±1` residue (after Cantor `q=−1`, φ
  `q=+1`). The model **caps honestly at `ω`**: `ascent_unbounded` says no `Raw` has depth `ω`, so `ω`
  is named by its finite generator, never inhabited (`ordinals.md`). The finite-signature rule's exact
  bite point.
- **Galois = the first *non-invertible* reading-pair (an adjoint pair / order-reversing connection)** —
  `Fix ⊣ Inv` between the sub-construction lattice and the `Aut`-subfamily lattice; the fundamental
  theorem = **residue-collapse-to-closure** (`clo = Inv∘Fix = id` on closed elements, `q=+1` idempotent
  pole). `equivalence.md`'s symmetric `LensIso` is the *closed/iso special case*; a general Galois
  connection is the asymmetric generalization (`Order/GaloisConnection.lean`, `ModNat.refines⟺divides`).
  New construct: **ordered/adjoint reading-pairs, residue = the closure gap** (`galois.md`).
- **★ L-parameters COMPOSE IN SERIES — and the calculus PREDICTS (first leverage).** Entropy
  `H = E[−log p]` = the **weight-reading ∘ the log-character**: the character's output (surprise depth)
  becomes the weight's value-slot. The payoff beyond collapse: the calculus **predicts entropy's form** —
  `−log` is *forced* as the unique character turning the independence-product of weights into a sum
  (the same `×↦+` arrow as `vp_mul`), so additivity `H(X,Y)=H(X)+H(Y)` is derived, not relabeled
  (`Information/Entropy.entropy_additive`). This passes the re-skin guard at the highest level — a
  *prediction*, not a re-description (`entropy.md`).

**Model v4**: `C` = distinguishing + {direction (`q=±1`), **bidirectional** fold-height,
atom-distinguishability}; `L` = a reading — *which form a category*: they **compose in series**
(entropy = weight∘character), form **composition-closed families** (`Aut`, groups), and form
**adjoint/order-reversing pairs** (Galois) — carrying {resolution, bidirectional character-mode,
weight}; `Residue` = `L`'s self-application surplus, tagged `q=±1` (escape/nilpotent vs
converge/involutive/closure). **First genuine leverage**: entropy's form *predicted* from the parts.

## The leverage phase (batch 5: Noether, CLT/Gaussian, Fourier, adjunction) — what the calculus PREDICTS

The bar rose from *collapse* (re-see X) to *leverage* (the calculus **predicts/derives a form or
enables a result**, as entropy did). Honest verdict across the four (21 decompositions total):

- **It predicts at the structural/skeleton level — form + *why* — and each prediction names a concrete
  Lean target that would close it.** This is the honest boundary: the calculus is genuinely predictive
  on the *discrete structure*, and the *full analytic/variational machine* is, in each case, a named
  open target, not a hand-wave.
  - **Noether** — predicts the conserved quantity *must be the `Aut(C)`-invariant character* (`q=+1`);
    certified by `det_holonomy_eq_one`. Open: the continuous/variational current.
  - **CLT/Gaussian** — predicts the Gaussian = the *convolve-and-rescale fixed point* (`q=+1` residue,
    generalizing φ from `golden_ratio.md`); engine `banach_fixed_point` built. Open: "convolve-rescale
    is a contraction".
  - **Fourier** — predicts the dual `Ĉ ≅ C` (self-duality) and the order-`d` character `= L₂∘dlog`
    (`qr_pow_iff_even_exp` *derives* it). Open: character orthogonality `Σχ = 0`.

- **★ One arrow runs through everything.** The single `×↦·` / `×↦+` character is now proven (or
  proof-shaped) to be the *same arrow* in: parity `L₂`, prime-valuation `vp_mul`, determinant
  `det2_mul`, entropy additivity, Noether invariance, the Legendre/Fourier character `legendre_mul`.
  Six "different" theorems are one construction-preserving reading read six ways — the calculus's
  deepest, most reused unity.

- **★ The calculus is itself a category of readings — and so far only its `q=+1` (converging/closure)
  corner is built.** Promote to a core principle (`adjunction.md`): *readings form a category*
  (`Lens.refines` the thin category, `LensIso` its groupoid); *adjoint reading-pairs generate
  idempotent closure monads* (Galois `clo = G∘F` — `clo_extensive` = unit, `clo_idempotent` = `T²→T`,
  `gc_fgf/gc_gfg` = triangle identities, *proved before being named*); and *initiality = the read-op*
  (`raw_initial`: `Lens.view = Raw.fold` is the unique arrow out of `Raw`). The one earned prediction:
  **universal properties live on closure-algebras** (`closed_iff_image`). The honest edge: the
  *free/growing* monad corner (`Lens.bind`/Kleisli) is **not built** — the calculus has lived in the
  two `q=±1` poles (converge/closure `q=+1`, escape/diagonal `q=−1`); the free corner is open.

**Model v5 (stable enough to name)**: `C` = distinguishing + {direction `q=±1`, bidirectional
fold-height, atom-distinguishability}; readings `L` **form a category** (compose in series; `Aut`
self-families; adjoint pairs → closure monads; character-families/duals) carrying {resolution,
bidirectional character-mode, weight}; `Residue` = self-application surplus tagged `q=±1`
(escape/nilpotent vs converge/involutive/closure); `read = initiality` (`Lens.view = Raw.fold`). The
**character arrow** and the **`q=±1` residue** are the two load-bearing invariants.

Next: convert predictions to closed derivations via the named Lean targets (character orthogonality;
convolution-contraction; continuous Noether current), and probe the un-built **free/growing corner**
(does the distinguishing's *unbounded ascent* give the free monad the closure corner lacks?). Targets +
frontier: `research-notes/frontiers/decomposition_calculus.md`. The standing bar: every decomposition
ends in a Revelation, or it is dropped.

## Two predictions now CLOSED in ∅-axiom Lean (the technique paying off, verifiably)

The leverage phase made predictions; two are now machine-checked theorems, not prose — the strongest
form of "the technique pays" (the originator's bar):

- **The growing/iteration-character axis** (`free_corner.md`) — a *new axis orthogonal to `q=±1`*:
  readings have an **iteration-character** — `∂` *nilpotent* (`∂²=0`), `clo` *idempotent* (`T²=T`), `S`
  *growing* (`Tⁿ` strictly ascends). The growing pole is now proved: `Theory/Raw/MuNuMirror.`
  **`succ_not_idempotent`** (∅-axiom PURE) — the distinguishing's successor reading `S r = slashOrSelf
  a r` satisfies `S(S r) ≠ S r` (depth strictly rises), the literal mirror of `clo_idempotent`. So the
  calculus is *not* confined to the converging/closure corner; the growing (free-flavoured) endofunctor
  is real and verified. (Honest residual: a free *monad* — the Kleisli multiplication — is still
  un-built, possibly blocked Mathlib-free.)
- **Character orthogonality** (`fourier.md`) — `ModArith/CharacterOrthogonality.`
  **`quadratic_orthogonality`** (20 PURE): for a primitive root `g` mod `p`, the order-2 character sums
  to zero over the orbit *and* each summand is the Legendre symbol (`altSign k = 1 ⟺ g^k` is a QR).
  fourier.md's predicted "root-of-unity telescoping" cashed at the Legendre level. (Open: general
  order-`>2` χ needs a `Real213` cyclotomic `ζ`.)

**Model v6**: as v5, plus a second reading-axis — **iteration-character** {nilpotent `∂` / idempotent
`clo` / growing `S`}, orthogonal to the `q=±1` residue tag (the same ascent is growing yet `q=+1`).
Two of the calculus's predictions are now ∅-axiom theorems; the remaining leverage targets
(convolution-contraction → Gaussian, continuous Noether current, general-χ orthogonality, the free
monad) are recorded in the frontier.

### Batch 6 (integration, ζ/Euler) — two more predictions, two consolidations (23 decompositions)

- **Integration** (`integration.md`) — PREDICTION: `∫ = Σ` at residue resolution (inverse of the
  difference-Lens), and **FTC = "telescoping is resolution-invariant"** — `Σ⊣Δ` (discrete) and `∫⊣d`
  (FTC) are the *same adjoint pair at two resolutions* (`gauss_conservation_telescope` PURE;
  `integral_eq_flux` by `rfl`). Cashes `derivative.md`'s open Σ/∫ cell and ties the **resolution axis to
  the adjoint-pair structure** (`galois.md`/`adjunction.md`): the resolution dial is reading-agnostic
  (dials `L₋`→`d` and `L_Σ`→`∫` identically) and commutes with the inverse-pair.
- **ζ / Euler product** (`zeta_euler.md`) — PREDICTION: the Euler *product form* falls out of the UFD
  character (`Σ_n = Π_p` is the distributive law of the faithful prime-valuation coordinate;
  `summatory_mul`, `geom_sum`, `primorial_le_four_pow` — a real finite Euler product, all ∅-axiom). The
  ζ-*value* is a `Real213`-cut residue (honest). **Consolidation**: "read the whole family at once" has
  two dual faces — Fourier sums over the dual `Ĉ`, the Euler/Dirichlet generating function sums over `C`
  weighted by a multiplicative kernel — one per *direction* of the `×↦+` character arrow.

These EXTEND, no new axis: the v6 invariants (the character arrow, `q=±1` residue, resolution,
iteration-character) absorb both, and reveal two cross-ties — *resolution ⇄ adjoint-pair* (FTC) and
*family-reading ⇄ the character arrow's two directions* (Fourier/Euler). The model is stable across
**23 decompositions, no break**; four predictions, two Lean-closed.

### Batch 7 (category theory itself, curvature) — the founding question answered; one character, four readings

- **Category theory itself** (`category_theory.md`) — answers the originator's founding question
  ("is the goal to make the axiom into CT/HoTT?"): **213 IS category-theory-shaped, but *generated from
  the distinguishing*** (verdict (c) made literal, term-by-term: `Raw` = initial object,
  `fold`/`universalMorphism` = the read-op = catamorphism, readings = morphisms, `LensIso` = groupoid,
  adjoint pairs → the closure monad). HoTT is *absent and structurally opposed* (`funext`/`propext`
  forbidden). What the distinguishing **adds** beyond bare CT (which leaves these free): the `q=±1`
  residue (limit/colimit duality as one *derived* law), atom-distinguishability (why hom is vectorial
  vs scalar), the forced `(3,2,5)`. The calculus is **self-describing** (its own apparatus = the
  vocabulary it produces; a fixed point via `raw_initial` + `dhom_unique_pointwise`), and the loop stays
  open *exactly* at `q=±1` (the free/colimit corner). No new axis — consolidation + the founding answer.
- **Curvature** (`curvature.md`) — PREDICTION: flat = conserved-character = `det 1` (the *same*
  `det_holonomy_eq_one` Noether-invariant), curvature = the loop-reading's `q=±1` residue (born with the
  sign-fold `S`; Gauss–Bonnet `Σκ = 2(1−b₁)` literally identifies it with `homology.md`'s residue).

**★ The deepest unity (capstone of the leverage phase):** the single `det` / `×↦·` character is read
**four ways** — *scalar* (`determinant`), *`Aut`-invariant* (`noether`), *around a loop* (`curvature`,
holonomy), *down the height* (`homology`, `∂`) — and the curvature/homology residues are tied by
Gauss–Bonnet. Determinant, conservation, curvature, and topology are **one character read four ways**.
Together with the count-reading's residue generating all the limitative theorems (`cardinality`), and
the `×↦+` character spanning parity/valuation/entropy/Fourier/ζ, the calculus has reduced a wide swath
of mathematics to **two invariants** — the *character arrow* and the *`q=±1` residue* — read across
{direction, fold-height, resolution, iteration-character}. **25 decompositions, no break.**

### Batch 8 (Gödel, surreals, knots, p-adics) — the first honest break, a new slot, two Lean closures

A six-agent wave: four fresh decompositions probing the model's *edges* (a limitative theorem, a
number-construction the author wrote by hand, a topological invariant, a non-Archimedean completion),
plus two leverage-target Lean closures.

- **Gödel / "provable"** (`godel.md`) — PREDICTION, not collapse: incompleteness is the **same `q=−1`
  escaping diagonal** as `cardinality.md` (Cantor) and `object1_not_surjective` — a self-pointing reading
  whose residue *cannot* be in the system's image. The calculus even predicts *where* incompleteness
  vanishes (a system with no self-encoding has no diagonal residue). Same residue, new domain — the
  count-reading's `q=−1` pole now spans cardinality, the halting problem's relatives, and provability.
- **Surreal numbers** (`surreal.md`) — EXTEND, and the strongest "the author wrote our `C`" datum:
  Conway's `{L | R}` *is* the directed iterated distinguishing, term-for-term (the construction `C`
  confirmed, not re-skinned). Ceiling: the same honest ordinal cap `ordinals.md` hit (no completed νF).
- **Knots** (`knots.md`) — ★ **the first clean PARTIAL-BREAK** (26 prior decompositions, no break). The
  braid *group* `Bₙ = ⟨n strands | crossing-compositions⟩` EXTENDS with no new primitive (`groups.md`),
  but the **knot invariant BREAKS** at two points the apparatus genuinely lacks: (1) the **skein relation**
  is a *relation among distinct constructions* (not one construction's self-application residue), and (2)
  the knot itself is an **ambient-isotopy quotient** (a topological identification the count/fold reading
  has no handle on). This is the most valuable datum in the notebook — it *locates the boundary*: the
  calculus is `⟨C-self-application | reading⟩ ⊕ residue`, and skein/isotopy sit outside that shape.
- **p-adics ℚ_p** (`padic.md`) — PREDICTION + a **new reading slot**: the resolution axis gains a **base**
  parameter (*which* valuation/metric measures "close"). The calculus predicts the *shape of the family
  of completions* (one per prime `vp`, the faithful coordinate), matching the `~484 PURE / 0 DIRTY` Padic
  corpus; Ostrowski **exhaustiveness** (these are *all* the completions) is named as the open leg.

Two leverage targets closed in ∅-axiom Lean this wave (each promotes a batch-5 prediction):
- **Character orthogonality at orders 3 and 6** — `CayleyDickson/Integer/RootOfUnityOrthogonality.`
  `root_orthogonality`/`omega_orthogonality`/`zeta6_orthogonality`/`cyclotomic_orthogonality` (23 PURE,
  in ℤ[ω]) extends `fourier.md`'s order-2 `quadratic_orthogonality` to the genuine roots of unity — the
  `Σ_x χ(x)=0` prediction now built at orders 2, 3, 6.
- **Convolve-rescale is a `Contraction`** — `Probability/Limit/ConvolveRescaleContraction.`
  `Φ_contraction` + `Φ_picard_cauchy` + `center_fixed`/`orbit_to_center` (20 PURE) closes
  `gaussian_clt.md`'s keystone *leg*: the rescale is exact dyadic halving, so `picard_cauchy` forces the
  Gaussian's `q=+1` modulus-residue. Honest residual: `banach_fixed_point` itself awaits a genuine
  `CompleteMetricModulus Dy`, and convolution is on the centered statistic, not the full profile.

**Model v7**: as v6, plus —
1. **the resolution axis carries a `base`** (`padic.md`): *which* valuation/metric defines "adjacent" is
   a reading parameter, not fixed — the family of completions is one reading dialed over its bases.
2. **the calculus's boundary is now located** (`knots.md`, first break): the normal form
   `⟨C-self-application | reading⟩ ⊕ residue(q=±1)` does **not** cover (a) *relations among distinct
   constructions* (skein) or (b) *quotients by an ambient identification* (isotopy). These are named
   missing primitives, not failures — the edge of the technique, found by probing for it.

The two invariants (character arrow, `q=±1` residue) and the four axes (direction, fold-height,
resolution+base, iteration-character) are unchanged in the interior; the break adds an *exterior*
marker. **30 decompositions, one located partial-break, six predictions, four Lean-closed.**

### Refinement v7.1 (`two_cells.md`) — the break splits three ways; the calculus gains an explicit 2-cell layer

A META-decomposition attacked the knots boundary by decomposing **natural transformations** themselves.
Result: v7's break-item (a) "relations among distinct constructions" was a **conflation of three shapes**,
and the calculus's status differs on each:
- **naturality/homomorphism relations → DISSOLVE.** A natural transformation IS a **2-cell the category
  of readings already admits**, ∅-axiom: `view_factors_through_morphism` (`Lens/Compose/Morphism.lean:37`)
  is the naturality triangle `M.view = h∘L.view` *term for term*; `IsLensMorphism` (the component + the
  two naturality squares), `refines_of_morphism` (a 2-cell *induces* a 1-cell — the 2-category interlock),
  `LensIso` (invertible 2-cells, a groupoid), `dhom_unique_pointwise` (initiality forces the only 2-cell
  out of `Raw`). **So readings form a 2-CATEGORY, not just a category** (1-cells = `refines`, 2-cells =
  `IsLensMorphism`/`LensIso`) — this comes OUT of the missing list and is recorded as built structure.
- **skein/Leibniz (graded three-term) relations → REAL, partially grounded.** A genuinely new construct:
  a **graded-relation slot** — a fixed linear law `Σ cᵢ·L(Cᵢ)=0` among a *family* of distinct constructions
  under *one* reading. NOT a 2-cell (relates readings of one C; this relates one reading of many C's) and
  NOT the character arrow (its degenerate *two*-term case). In-repo instance: the cup-product Leibniz rule
  `leibniz_universal_delta4` (`Cohomology/Delta/V4Capstone.lean:62`, PURE) — `δ(α⌣β)=δα⌣β ⊕ α⌣δβ`, same
  shape as the skein relation. Grounded as a *derivation* law; the skein's crossing-resolution *move* is not.
- **isotopy quotient → REAL and ABSENT.** Not a 2-cell, not a kernel-coincidence (`lensIso_iff_kernel_eq`),
  not a closure (`clo`); a quotient by a relation no reading's kernel or self-application generates —
  located precisely at the **un-built colimit/`q=−1` corner PLUS an absent ambient-space construction**.

**Net v7→v7.1:** readings form a **2-category** (explicit, ∅-axiom); the "missing primitive" list shrinks
from two coarse items to **(i) the graded-relation slot** (a *promotion target*, partially grounded by
Leibniz) and **(ii) the isotopy/colimit quotient** (the genuine remaining absence). The two invariants and
four axes are unchanged. The first break is real but smaller and more precisely mapped than v7 recorded.

### Representation theory (`representation.md`) — the character arrow's home field; the `det`/`tr` split

A fresh decomposition of the field that is the *home* of the calculus's central object: a representation
= `groups.md`'s Aut-family read through `determinant.md`'s scalar character; a character = the `×↦·` arrow
on the Aut-family; class functions = `noether`'s `q=+1` invariant; and **Schur/character orthogonality =
the SAME `Σχ=0` theorem the repo just closed** (orders 2/3/6) — no new work, a decisive consolidation.
Verdict PREDICTION + PARTIAL with one new **located break**: the realized *character* is `det`
(multiplicative, the `×↦·` arrow); the genuine `d>1` representation character is the **trace**, which is
the *additive `×↦+` twin* and **not multiplicative** — `Mat2.tr` exists in-repo only as an order/growth
readout (φ-growth `GoldenAperiodic`, discriminant `traceDisc`), never as a character-homomorphism (there
can be no `tr(MN)=tr M·tr N`), and there is no `Rep(G)`/Maschke. So the `×↦·` arrow now provably runs
through **seven** fields (parity, valuation, det, entropy, Noether, Fourier, rep-theory characters), and
the live edge is pinned: **the `det`/`tr` split** — where the multiplicative character ends and the
additive trace-character (un-closed at `d>1`) begins. EXTEND by consolidation; interior unchanged.

### Differential equations / dynamical systems (`differential_equations.md`) — the Banach engine's third field

A fresh decomposition tied to the fixed-point work: **Picard–Lindelöf existence IS `banach_fixed_point`
applied to the integral operator**, so a flow `φ_t` = the evolution reading iterated at residue resolution
(the `dt→0` dial), and the solution = the `q=+1` converging contraction residue — reached by none, narrowed
by `picard_cauchy`'s modulus. Verdict **PREDICTION**: the same `banach_fixed_point` engine now provably
spans **three fields** — φ (`golden_ratio.md`), the Gaussian (`gaussian_clt.md`), ODE flows — one object
read across a number-pair, a probability weight, and a vector field. The repo has a real discrete ODE
corpus (`Analysis/ODE/`: `picardIterate`, `picard_exp` y'=y→y0·2ⁿ, `LinearODE`; `Foundations/MonovariantFlow`
`flow_reaches` = Lyapunov descent to an equilibrium; `Optimization/GradientFlow` `d/dt F = −‖∇F‖²≤0`). Same
honest gap as the Gaussian *profile*: the continuous integral operator `(Tf)(t)=x0+∫f` is not welded to
`banach_fixed_point` as a `Contraction` (the discrete Euler-Picard step and the engine live separately) —
a named promotion target, EXTEND only.

### Measure theory (`measure.md`) — the sharpest leverage: the repo's "no Choice" is a *derived prediction*

A fresh decomposition of measure / σ-algebra / the Lebesgue integral. A measure = `probability.md`'s
weight-reading run backward (the count/weight *before* the ratio fold); probability = the case
`denominator = 2^E`. Surprise: measure theory is **already built** Choice-free and σ-algebra-free in
`Analysis/Measure/` (35/0 PURE: `measureNum`, `measure_union_additive` via list `++`, `lebesgueStepNum`,
`lp_two_singleton`). **The leverage** (PREDICTION, the sharpest in the notebook): the calculus *predicts*
that classical measure theory's **Choice-dependence — non-measurable sets, Vitali, Banach–Tarski — is
exactly the `q=−1` escape residue** of the weight-reading's *uncountable* self-cover (a Vitali selector =
AC on an uncountable index = the forced fixed-point-free diagonal `object1_not_surjective`/`OneDiagonal`,
the *same* diagonal as Cantor and Gödel). So the repo's finite-`List` measurable set sits in the **`q=+1`
corner where the diagonal cannot arise** — "no Choice" = "stay at `q=+1`", and the design decision becomes
a **structural prediction, not a taboo**. The `q=±1` residue tag now unifies Cantor/φ/Gödel/homology AND
constructive-vs-non-measurable. Located break: `Lp` full `∀S` additivity leaks `Quot.sound` via `funext`
(the propext/funext wall, `category_theory.md`) — only the pointwise version is PURE. **Carathéodory's
outer-measure NOW CLOSED** (`Analysis/Measure/OuterMeasure.lean`, 29/0): instantiated AS the predicted
`clo` closure — a genuine Galois connection `cara_gc`, `caraClosure_idempotent` (`T²=T`), conservative
extension; the conservative-degenerate form (every finite set Carathéodory-measurable) is the *predicted*
`q=+1`-corner content, the countable-cover infimum being the omitted `q=−1` half.

### Quadratic reciprocity (`quadratic_reciprocity.md`) — a deep theorem ALREADY ∅-axiom; parity collapse on the Legendre symbol

A fresh decomposition that found the rare result: **quadratic reciprocity is already fully proved ∅-axiom**
in the repo — `QuadraticReciprocity.quadratic_reciprocity` (11/0 PURE), by exactly the Eisenstein
lattice-double-count the calculus predicts. The single permutation `σ_a` carries **five readouts** —
inversion-`psign` / matrix-`det` / Legendre-QR (`zolotarev_mu : psign σ_a = (a/p)`, `ZolotarevMuBridge`,
14/0) / Gauss least-residue sign-product / Eisenstein floor-count — all one number: `parity.md`'s "parity =
permutation-sign = `det=±1`" collapse realized *on the Legendre symbol itself*. The two symbols `(q/p)`,
`(p/q)` are the order-2 `×↦{±1}` character read in two directions, bound by one grid count `m·n`
(`floor_sum_rectangle`); `parity_sum_iff` forces their signs to agree iff `m·n` is even — the `q=±1` parity
residue, the "miracle" being the empty diagonal (`elem_tri`: no `q·x=p·y` for coprime primes). Verdict
**PREDICTION, fully Lean-closed** — the rare entry with no open deep leg. The `(−1)^…` stays a parity bit
(no `Real213` cyclotomic cut needed — the order-2 character lives in `{±1}`).

### The `q=±1` residue tag, formalized (`Lib/Math/Foundations/ResidueTag.lean`, 55/0) — the deepest collapse, ∅-axiom

The notebook's deepest open collapse is now ONE formal object: `ResidueTag` (inductive `escape | converge`)
+ `multiplier : ResidueTag → Int` (∓1, with `multiplier_unimodular`) + `TaggedResidue`, with the capstone
`residue_tag_two_poles` bundling both poles. q=−1/`escape` ⟹ `escape_residue_outside` (delegating to
`OneDiagonal.no_surjection_of_fixedpointfree` — Cantor/Gödel/measure); q=+1/`converge` ⟹
`converge_residue_fixed` (delegating to `banach_fixed_point_modulated` — φ/Gaussian/ODE), with
`golden_is_converge` tying `+1` to the literal φ Cassini multiplier. **Honest shape:** one tag, one ±1
reading, one consequence theorem *per pole* — NOT one biconditional, because the poles are genuinely
asymmetric in type (q=−1 = a universal-negation hypothesis → a *negative* theorem; q=+1 = a contraction
hypothesis → a *positive existence* theorem; collapsing them to one `Eq` would need excluded middle). The
`±1` tag is the "shared column", the asymmetry named precisely — closing the frontier's stated target.

### Topology / compactness (`topology.md`) — compactness = the finiteness-residue, `q=+1` corner

PREDICTION: an open set = a resolution-stable fibre; compactness = the `q=+1` finiteness-collapse of the
count-reading on a cover, the *contrapositive* of `cardinality.md`'s `q=−1` escape diagonal — consolidated
onto the formal `ResidueTag`. The phenomenon is built (`Geometry/Topology/`: `DyadicOpen`, `heineBorel`,
`chain_finite`; `Analysis/ExtremeValue.lean` makes it literal — `ModContOnGrid.gridMax_attained` = max
attained at every *finite* resolution (`q=+1`), `Msup` = the reached-by-none limit cut (`q=−1`)). Missing
leg located (dual to measure.md): the arbitrary-cover quantifier the finite-`List` setting can't host.
Continuity's open-set leg is now also certified — `ContinuityOpenSet.lean` (11/0): forward + pointwise
backward unconditional, uniform backward via modulus-as-data (the `AC₀,₀` wall, located).

### Generating functions / formal power series (`generating_functions.md`) — GF-product = convolution, Lean-grounded

PREDICTION, load-bearing leg fully ∅-axiom: a generating function = the family-reading (the count-reading
of a height-indexed family, the `x`-slot the grading coordinate), and **its product IS the Cauchy
convolution `⋆`** just built in `ConvolveProfile` — `mass_conv` (total mass multiplicative, `×↦·`) +
`momentNum_conv` (mean additive, `×↦+`) are literally "the GF of a sum of independents is the product of
GFs". Unifies `zeta_euler` (Dirichlet/Euler product, `summatory_mul`), `ConvolveProfile` (Cauchy product),
and recurrences (rational GFs = the `q=±1` residue, `mobius_iteration_master`/`fib`/Cassini) as three
indexings of one reading. The repo even has `Combinatorics/GeneratingFunction.lean` (`convolution`, `xVar`).
Missing leg: the two `conv` defs aren't welded into a formal-power-series **semiring** (no
associativity/homomorphism proof on `CoeffSeq`); the analytic GF-as-function is the `Real213`-cut residue.

### Character orthogonality extended to order 4 (`GaussianOrthogonality.lean`, 18/0) + the generic conditional

Extends fourier.md's orthogonality leg: `i_orthogonality : 1+i+i²+i³ = 0` in the Gaussian integers ℤ[i]
(no `Real213` needed — order 4 lives in ℤ[i]), plus `orthogonality_of_pow_one` — the **order-AGNOSTIC
conditional**: in any `CommRing213`, `ζⁿ=1 ∧ (ζ−1)` cancellable ⟹ `Σ_{k<n}ζ^k = 0`, straight from
`geomSum_telescope`. Concrete primitive-root orders now closed: **2, 3, 4, 6** ({±1}, ℤ[ω], ℤ[i]). Residual:
arbitrary `n` needs a cyclotomic ring `ℤ[ζ_n]` the repo lacks — the conditional is closed, only the witness
for general `n` is open.

### Spectral theory / eigenvalues (`spectral.md`) — the spectrum DISSOLVES the det/tr split

PREDICTION: an eigenvalue = the `q=+1` scale-residue of the linear reading (`A·v=λ·v`: `v` fixed up to the
multiplier `λ`); φ is literally the dominant eigenvalue of the Fibonacci/Möbius matrix `G` (`golden_hyperbolic`:
`tr=3,det=1,disc=5`, eigenvalues `φ²,φ⁻²`). **The det/tr split (representation.md's open edge) DISSOLVES**:
`tr = Σλ = e₁` (the additive `×↦+` character) and `det = Πλ = e₂` (the multiplicative `×↦·` character) are
the two elementary symmetric functions of *one* spectrum — the two coefficients of the characteristic
quadratic the matrix obeys by **Cayley–Hamilton** (`Mat2CayleyHamilton.cayley_hamilton`, 4/0 PURE, committed;
`char_poly_discriminant`/`dial_is_char_discriminant`). The det/tr "opposition" was degree-1-vs-degree-2 of
one Vieta factorization — **now a Lean theorem** (`Mat2Spectrum.lean`, 9/0 PURE): `tr_eq_e1`, `det_eq_e2`,
`disc_eq_gap_squared`, `det_tr_split_is_e1_e2`. Residue: eigenvalue *existence* = the `Real213`/ℂ residue,
stratified by `disc=(μ−ν)²` — real spectrum = `q=+1` (hyperbolic/φ), complex = `q=−1` escape (elliptic);
the theorem is the conditional "*if* the spectrum exists *then* tr=e₁ ∧ det=e₂", exactly what makes the
split a non-split.

### Lie theory / the bracket (`lie_theory.md`) — bracket = the q=±1 antisymmetry; Jacobi = the graded-Leibniz pole

PREDICTION (consolidation of groups + exponential + homology): a Lie algebra = the **infinitesimal of the
Aut-family**; the bracket `[X,Y]=XY−YX` = the `q=−1` antisymmetry residue — **now built ∅-axiom**
(`Mat2Bracket.lean`, 10/0): `bracket_antisymm` (`[X,Y]=−[Y,X]`, the same sign-fold as `det`/`∂`/ℤ),
`tr_bracket_zero` (forced traceless — the `sl` kernel = representation.md's det/tr split from the algebra
side), `jacobi`, and `bracket_leibniz` (the derivation pole). `exp:𝔤→G` = exponential.md's `×↦+` character
(group `×` ↦ algebra `+`); BCH's `½[X,Y]` = the `^`-wall infinitesimally. **Jacobi = the graded-Leibniz
pole** (tied to `leibniz_universal_delta4`, README v7.1's graded-relation slot), *not* naive `∂²=0`. Missing
leg located: the infinitesimal/tangent `ε` object (`T_eG`, `ε²=0`) — the discrete `Mat2` hosts the finite
commutator (= the bracket on matrix groups, so the prediction lands) but no tangent space; same cap + BCH.

### de Rham cohomology / forms (`de_rham.md`) — the strongest consolidation: Stokes is *already* built

PREDICTION (consolidation of homology + integration + curvature): de Rham is `homology.md`'s fold-height
reading run **upward** in degree. **`d²=0` = `∂²=0`** (literally one operator, `dsq_zero_universal_delta4`);
**Stokes `∫_M dω=∫_∂M ω` is ALREADY a ∅-axiom theorem** — it is `gauss_conservation_telescope` (the discrete
divergence theorem, interior walls cancel / boundary survives = the `Σ⊣Δ`/`∫⊣d` adjoint at residue
resolution); **wedge-Leibniz = `leibniz_universal_delta4`** (the graded-relation slot, with the wedge
antisymmetry = `cup1_antisymmetric` = parity's `q=−1` det sign); `H*_dR = ker d/im d` = homology's residue
read upward, tied to curvature via Gauss–Bonnet `Σκ=2(1−b₁)`. Missing leg: the smooth-manifold form complex
`Ω^k(M)` + the de Rham comparison iso (the `Real213`/`h→0` smooth-tensor gap; the agent also flagged
`Multivariable/Stokes.lean`'s "masters" as trivial skeletons — the load-bearing Stokes is the telescope).

### Information geometry (`information_geometry.md`) — KL = the entropy-character's asymmetry residue

CONSOLIDATION-PARTIAL (entropy + probability + curvature): KL divergence = entropy.md's `weight∘log`-character
eating a *ratio* `p/q` = a directed surprise-depth difference (`klBitsDyadic a b = a−b`, `kl_nonneg`,
`kl_self_zero`); the asymmetry `D(p‖q)≠D(q‖p)` = the `q=±1` direction bit; `D≥0`, `=0⟺p=q` = the `q=+1`
diagonal fixed point. Fisher metric = the second-order (Hessian-at-diagonal) of KL = curvature.md on
weight-space — the one `×↦+` character at three orders (entropy/KL/Fisher). **PARTIAL:** built at the dyadic
atom only; the full divergence *functional* `Σ p·log(p/q)` and its Hessian (the Fisher *metric tensor*) are
absent — the `weight × character` at non-power resolution (the `log₂e` `Real213` bracket, entropy.md's own gap).

### Spectral graph theory (`graph_theory.md`) — Laplacian spectrum = the q=+1 diffusion-residue

PREDICTION, central leg BUILT: a graph = `⟨V (count) | symmetric adjacency reading⟩`; the Laplacian `L=D−A`
is the symmetric diffusion reading, so its spectrum is REAL (`Mat2SymmetricSpectrum.disc_symmetric_nonneg`,
the `q=+1` corner), with `λ₀=0` the constant/all-ones fixed point. **Connectivity = dim ker L** is a PURE
theorem (`GraphConnectivity.closed_const`/`closed_root_determines`; an actual bipartite adjacency in
`KernelConstancyUniversal.bipAdj_connected`; the physics K_{3,2} Laplacian spectrum
`LaplacianSpectrum.laplacian_spectrum_master`) — Fiedler's "#components = dim ker L" = the count-reading's
`q=+1` fixed point; Matrix-Tree = the det-character. Consolidates spectral + topology + count + det.
Promotable target: the 2-vertex Laplacian `[[1,−1],[−1,1]]` is a `Mat2`, symmetric, spectrum {0,2} rational.

### Convex optimization / duality (`convex_duality.md`) — Legendre–Fenchel = galois.md's closure

PREDICTION (galois + adjunction + gradient-flow + spectral): the Legendre–Fenchel biconjugate `f**=clo(f)`
= the closed convex hull = `galois.md`'s idempotent closure monad `clo=G∘F` on the function lattice;
Fenchel–Moreau = the residue-collapse-to-closure; **duality gap = the closure residue, q=+1**. Convexity =
the `q=+1` PSD-Hessian corner (`disc≥0`); the minimum = gradient-flow's `q=+1` fixed point
(`gradient_descent_monotone`). Surprise: weak/strong duality are BUILT — `OllivierRicci.kantorovich_weak_duality`
(`max_λ min_x ≤ min_x max_λ`, LP/Kantorovich) + `ollivier_plan_optimal` (zero-gap certificate). Missing leg:
the Legendre transform *object* `f*(p)=sup_x(px−f(x))` (the one weld: instantiate `clo` at `Fix=Inv=(·)*`).

### Model theory / completeness (`model_theory.md`) — completeness = view=fold initiality; logical compactness = topology's q=+1 corner

PREDICTION+PARTIAL, the q=+1 companion of `godel.md`'s q=−1: **completeness `⊢φ⟺⊨φ` = the calculus's
`view=fold` initiality** — the term model = the initial object `Raw`, syntactic (free, `Raw.fold`) and
semantic (universal, `Lens.view`) sides are the *same unique arrow* (`raw_initial`/`universalMorphism_unique`/
`dhom_unique_pointwise`), the q=+1 syntax/semantics fixed point. **Logical compactness = topology.md's q=+1
finiteness residue** — the SAME corner (`heineBorel`/`compact_bounded_by_length`), name not a coincidence
(Stone-space compactness). Löwenheim–Skolem = the q=−1 count diagonal (`raw_at_most_countable` +
`object1_not_surjective`). Consolidates category_theory (initiality) + topology (compactness) + godel
(diagonal). Missing leg: an actual FOL `Formula`/`⊨`/`⊢` object (the structural prediction is the deliverable).

### Quantum mechanics (`quantum_mechanics.md`) — measurement = q=+1 eigenvalue, uncertainty = q=−1 bracket

PREDICTION (physics-branch math-structure, no validation claim): an observable = a symmetric operator =
the `q=+1` real-spectrum reading (`disc_symmetric_nonneg` — the Hermitian postulate IS "stay at q=+1");
measurement outcome = eigenvalue = q=+1 scale-residue. The canonical commutator `[X,P]≠0` = the q=−1
antisymmetry bracket-residue (`Mat2Bracket`); the uncertainty principle = the bracket obstructing a common
q=+1 eigenbasis. Unitary evolution = det/holonomy=1 (`det_holonomy_eq_one`). Measurement and uncertainty
are the two poles of one `ResidueTag`. Honest ceiling: the finite `Mat2` cannot host `[X,P]=iℏI`
(commutators are traceless, `tr(iℏI)≠0`) — the certified content is the trace-free antisymmetry residue,
not the `iℏ` value; Hilbert space / `⟨ψ|φ⟩` / Born rule / d>1 eigenprojector are the missing legs.

### Yoneda lemma (`yoneda.md`) — the self-describing capstone: Yoneda = the calculus's own foundation

PREDICTION, the deepest self-reference: Yoneda is not a new field but the calculus's OWN operating principle
`OBJECT = ⟨C | L⟩` ("an object is its bundle of readings") made categorical — decomposing it is a fixed
point. The Yoneda embedding `A↦Hom(−,A)` = the founding sentence; the Yoneda lemma `Nat(Hom(A,−),F)≅F(A)` =
`dhom_unique_pointwise` (an arrow out of the representable/initial object pinned by one datum) + naturality
`view_factors_through_morphism`; faithfulness = `object1_injective`; fullness/"same readings ⟹ iso" =
`lensIso_iff_kernel_eq`. ★ The sharpest line: **`self_covering_closure` (injective ∧ ¬surjective) = Yoneda
⊕ its residue in ONE ∅-axiom theorem** — faithful where the embedding succeeds (`q=+1`), un-pointable where
self-application diagonalizes out (`object1_not_surjective`, `q=−1`). Missing leg: a named `Hom(−,A)`/presheaf
object + the Yoneda bijection as a natural `Equiv` (the latter presses on `funext` — the 1-categorical ceiling).

### Galois correspondence (`galois_correspondence.md`) — subfield↔subgroup anti-iso = the order-reversing closure; solvability = the commutator tower

PREDICTION+PARTIAL (galois + convex_duality + lie_theory's bracket + orthogonality orders): the field-theoretic
Galois correspondence = `galois.md`'s `Fix⊣Inv` adjunction with `clo=Inv∘Fix=id` on the closed (q=+1 fixed)
elements — the SAME `f**=clo(f)` pattern as `convex_duality.md`, on the subgroup/subfield lattices (the repo's
`divides⟺refines` anti-iso skeleton). **Field content is partially grounded** (corrects galois/convex notes):
`CyclotomicFive.galois_group_is_C4` (`Gal(ℚ(ζ₅)/ℚ)≅C₄`) with `golden_real_subfield` (`ℚ(φ)` the order-2 fixed
subfield), and A₅ as a real object (`A5Bridge.a5_order`=60). **Solvability = the commutator tower at q=±1**: the
derived series `[G,G]⁽ⁿ⁾` terminating = q=+1 (solvable), vs the quintic's A₅-simplicity `[A₅,A₅]=A₅` = the q=−1
non-terminating commutator-escape — both endpoints PURE (`Mat2Bracket.bracket_antisymm`, A₅ built) but the
*iteration* (derived series + A₅-simplicity) is the located missing leg: promote the Lie commutator to a
group-commutator-subgroup and iterate, tagging termination q=+1 vs A₅-escape q=−1.

### Curry–Howard / proof theory (`curry_howard.md`) — the calculus is a type theory describing itself

PREDICTION, near-self-descriptive (like yoneda): Curry–Howard = the calculus recognizing its own
type-theoretic substrate. `Raw` = the free inductive type = term model = proof/construction; a `Lens` = a
type-as-reading = proposition; `Lens.view = Raw.fold` is the recursor — so `⟨C|L⟩ = ⟨proof|proposition⟩`,
and the λ↔⊢ correspondence = `view=fold` initiality (the *same* `dhom_unique_pointwise`/`raw_initial` as
model_theory's completeness). ★ Two PURE-built ties: **normalization = the fold to the unique normal form**
(pinned by `dhom_unique_pointwise`); **strong normalization = `Lambek.no_infinite_descent`'s `q=+1`
well-founded termination** (`isPart_wf` — reduction bottoms out at the atomic floor = the normal form).
Consistency = the `q=+1` converging pole vs Gödel's `q=−1` diagonal (one `residue_tag_two_poles`).
Consolidates category_theory + model_theory + yoneda + godel + MuNuMirror/Lambek. Missing leg: a named typed
λ-calculus (`Term`/β-reduction/`Γ⊢t:A`) + the bridge "β-SN = `no_infinite_descent`" (the proof-theory dual
of model_theory's absent FOL syntax — the engine is real and PURE, the typed-calculus instance is the open work).

### Sheaf theory (`sheaf_theory.md`) — gluing = q=+1 unique-amalgamation; H^{>0} = the q=−1 local-global obstruction

PREDICTION+PARTIAL (topology + de_rham + resolution + initiality): a presheaf = a restriction-compatible
reading on the resolution poset; the **sheaf gluing axiom = the q=+1 unique-amalgamation = `dhom_unique_pointwise`
initiality** (a unique global section forced by compatible local data = the catamorphism pinned by its pieces),
with overlap-compatibility = the naturality 2-cell `view_factors_through_morphism`. **H^{>0} = ker δ/im δ = the
q=−1 local-global obstruction = de_rham's coboundary residue** (`delta`, `dsq_zero_universal_delta4`); H⁰/H^{>0} =
the two poles of one `ResidueTag`; de Rham = the constant-sheaf case; stalk = the residue-resolution germ (`Msup`).
Missing leg: a named `Presheaf`/`Sheaf`/`Stalk`/Čech object (grep-confirmed absent) — same shape as topology's
arbitrary-cover and de_rham's smooth `Ω^k(M)`.

### Tropical / idempotent semiring (`tropical.md`) — (max,+) = the character arrow's idempotent T→0 limit

PREDICTION (exponential + entropy + the idempotent iteration-character + convex_duality + the max-lattice): the
tropical `(max,+)` semiring = the `×↦+` character at its idempotent `T→0` dequantization limit. ★ The repo's OWN
docstrings already classify `max` as the idempotent pole of the iteration-character axis — `max_idem` (`T²=T`),
`max_iter_trivial` ("`max` builds no tower"), the exact mirror of `succ_not_idempotent`'s growing pole. So
tropicalization = that pole armed with a `⊗`; the tropical product = the Legendre/infimal-convolution dual
(convex_duality); dequantization = the resolution-limit residue. Missing leg: the tropical semiring object +
the dequantization map `t·log(e^{x/t}+e^{y/t})→max` (the named weld: `softmax_t` on `Real213` cuts, its `t→0`
residue = `cutMax`). A sharpening: tropicalization is the calculus's first explicit *character-at-a-resolution-limit*.

### ★ Topos theory (`topos.md`) — why 213 is constructive: the PURE/DIRTY boundary IS the Heyting/Boolean boundary

PREDICTION+PARTIAL, the sharpest *foundational* leverage: a topos = the calculus's `Raw`/`Lens` variable-set
world; **Ω = the distinguishing-target `Bool`** and the characteristic map **χ = `Object1` (`decide (s=r)`) are
BUILT + PURE** (`FlatOntology.lean:43`), not conceptual; the power-object embedding `A→Ω^A` is `object1_injective`,
its residue `object1_not_surjective`. ★ The revelation is **grounded by a purity scan, not asserted**: in
`SemanticAtom.lean` the classical `Prop`-valued connectives (`canonicalTruthMap`, `canonicalIffMap`,
`propAsDistinguishing`, …) are all **DIRTY [propext]**, while the `Bool`/`decide` connectives are **PURE** — *the
PURE/DIRTY boundary IS the Heyting/Boolean boundary*. So **"213 is constructive (∅-axiom)" = "213 is the `q=+1`
PURE corner of its own topos, whose internal logic is intuitionistic (Heyting)"** — a structural account of the
repo's foundational discipline, the `measure.md`-grade payoff (there "no Choice" = `q=−1` escape; here "no
Classical/LEM" = the `q=−1` propext cost of Boolean logic). Lawvere–Tierney topology = `clo`; geometric morphism
= an adjoint pair. Consolidates category_theory + sheaf + model_theory + yoneda + the no-Classical stance.
Missing leg: a *named* `Topos`/`Ω`/Mitchell–Bénabou/`GeometricMorphism` object (the categorical twin of the
missing presheaf object — every leg built+PURE, only the bundle naming it "a topos" absent).

### Fundamental group / π₁ (`fundamental_group.md`) — π₁'s homotopy quotient recurs as knots.md's SAME break

PARTIAL: the loop *algebra* EXTENDS — π₁ = the loop-holonomy reading's `q=±1` residue (`holonomy_append` =
concatenation, `positive_loop_trivial` = simply-connected q=+1, `first_loop_is_the_fold : holonomy[S,S]=−I≠I`
= the q=−1 non-contractible loop); **H₁ = π₁ abelianized = the commutator quotient** = ONE step of
`DerivedSeries.commSet` (`derived_S3_step1`), bridged to b₁ via Gauss–Bonnet `totalCurv_eq`; covers↔subgroups =
the Galois anti-iso (`clo`). ★ But the **homotopy quotient BREAKS at exactly knots.md's located break** (the
ambient-deformation/isotopy quotient — not a self-application residue, not a kernel-coincidence, not `clo`),
recurring verbatim in an independent field. That recurrence promotes the break from a one-off to a **principled
topological-quotient limit**: the precise missing leg is a single **ambient-deformation quotient primitive**
serving both knots and π₁.

### Ergodic theory (`ergodic_theory.md`) — the q=+1 fixed point across five fields

PREDICTION, the most consolidating note (gaussian_clt + differential_equations + measure + graph_theory +
spectral, all at one `q=+1` fixed point): the **invariant measure = the q=+1 fixed point of `T_*`** (the same
`banach_fixed_point` object as φ/Gaussian/ODE); the **ergodic theorem "time-average = space-average" = the
q=+1 Birkhoff/LLN residue** (`balanced_LLN_modulus`, reached-by-none/modulus-narrowed; Birkhoff average = the
LLN sample-mean `countTrue_append`); ★ **ergodicity = invariant functions constant = the dim-1 q=+1 kernel =
graph_theory's Laplacian λ₀=0** (`pathLaplacian_const_kernel`/`closed_const`) — the load-bearing tie; mixing =
the transfer operator's contraction/spectral gap. Honest correction: the "Markov stationary" tie is conceptual
(`MarkovTree` is the Markov *Diophantine equation* `x²+y²+z²=3xyz`, not a transition matrix). Missing leg: no
`measurePreserving`/`Birkhoff`/`Koopman`/`Ergodic` object (the Birkhoff average over an orbit `f∘Tⁱ` vs the
LLN's over a `List`) — engines + ties built and PURE, the named field object open.

### Differential geometry / connections (`connections.md`) — curvature = holonomy loop AND bracket commutator (both built); a stale gap corrected

PREDICTION, the geometry cluster's strongest consolidation (curvature + holonomy + de_rham + lie_theory's
bracket). ★ Curvature is the SAME `q=−1` residue read two **provably-equal** ways, both ∅-axiom: the
*geometric* holonomy-around-a-loop (`first_loop_is_the_fold : holonomy[S,S]=−I≠I`) AND the *algebraic*
bracket-commutator of covariant derivatives — `Mat2Bracket.bracket` AND the genuine index field
`TensorCalculus.riemUp` (`R^l_{ijk}=[∇_j,∇_k]`) with `riem_antisym_jk` (the `q=−1` pair-swap). Flat = `det1`
q=+1; Bianchi = the cyclic `q=−1` cancellation (`riem_bianchi1`, same mechanism as `jacobi`/`dsq_zero`);
Gauss–Bonnet = `totalCurv_eq`. ★ **Stale-gap correction**: curvature.md/de_rham.md/lie_theory.md declared
"no Riemann tensor/Christoffel/Bianchi" — **false**; `Geometry/TensorCalculus.lean` (23/0 PURE) builds the
abstract-index Riemann tensor, Christoffel (both kinds), Levi-Civita (`∇g=0`), Ricci, Einstein, both Bianchi
identities. The genuine residue is strictly smaller: only the `Real213` **smooth metric** (`h→0`).

### Random matrix theory (`random_matrix.md`) — Wigner semicircle = the q=+1 free-convolve fixed point

PREDICTION (spectral + gaussian_clt + probability + convolution): a random matrix = the symmetric `q=+1`
real-spectrum reading (`disc_symmetric_nonneg`) ∘ the probability weight; the eigenvalue distribution = the
spectral measure. ★ The **Wigner semicircle = the q=+1 fixed point of free convolve-rescale** `Φ_free =
rescale(μ⊞μ)` — the spectral-measure twin of gaussian_clt's `Φ = rescale(weight⋆weight)` one level up:
*semicircle : free convolution :: Gaussian : classical convolution*, both the q=+1 fixed point of the SAME
`Φ_contraction` engine. Its finite generator is grounded — the semicircle's even moments ARE the Catalan
numbers (`Combinatorics/Catalan.catalan`, 17/0, the free analogue of Gaussian pairings). Missing leg: the
random-matrix/spectral-measure/free-convolution `⊞`/R-transform/semicircle objects (engines PURE, field
object absent); promotable: a 2×2 GOE toy inside `Mat2SymmetricSpectrum` (cf. the 2-vertex Laplacian).

### Algebraic geometry / Nullstellensatz (`algebraic_geometry.md`) — the THIRD order-reversing-closure instance

PREDICTION+PARTIAL: the V⊣I (variety↔ideal) correspondence = the SAME `f**=clo(f)` order-reversing closure as
field-Galois and Legendre–Fenchel — the THIRD instance. Nullstellensatz `I(V(J))=√J` = `clo(J)=√J` (radical =
closure-completion, `clo_idempotent`/`biconj_idempotent`), reduced ⟺ `closed_iff_fixed`; Zariski-closed =
V-closed; irreducible = prime = prime_factorization's ×-atom (`vp_mul`); Spec glued = sheaf gluing. Grounded
toy: `mulDiv_gc`; nearest instantiated V∘I-closure on a real set-system = `OuterMeasure.cara_gc` (29/0).
Missing leg: an actual `Ideal`/`V`/`I`/`√`/`Spec` object (grep-confirmed absent).

### Modular forms / L-functions (`modular_forms.md`) — the Eichler–Shimura period side is BUILT

PREDICTION+PARTIAL: a modular form = `connections.md`'s SL(2,ℤ) Aut-family read four ways. Modular form =
`q=+1` Aut-invariant character (Noether); L Euler product = `Σ_n=Π_p` (the UFD `×↦·` character, eigenform
multiplicativity); eigenforms = spectral's `q=+1` simultaneous eigenbasis; functional equation = the `q=±1`
reflection involution (`FenchelMoreau` antitone + the `S` involution). ★ Surprise: the Minkowski/ModularGeometry
corpus grounds the **entire Eichler–Shimura PERIOD side** ∅-axiom (30/0) — `manin_unimodular_decomposition`
(period contour = Stern–Brocot tree), `minkowski_is_markov_valued_cocycle` (the SL(2,ℤ) 1-cocycle),
`period_satisfies_relations` (weight-4 `1−X²`, the E–S relations `r|(1+S)=0 ∧ r|(1+U+U²)=0`). Missing leg: the
automorphic side (Hecke/eigenform/q-expansion + analytic `L(f,s)`) — the cohomological dual of the built period corpus.

### Frontier-reconciliation audit (`FRONTIER_AUDIT.md`) — 7 stale "missing leg" claims corrected

A repo-first sweep of all 55 notes' absence-claims (the connections.md lesson generalized): **7 stale claims
fixed across 4 notes** (lie_theory: `no jacobi/Jacobi object` → `Mat2Bracket`+`Mat2Killing`; noether:
`no ∂·j theorem` → `NoetherCurrent.noether_local`; galois + galois_correspondence: `derived series absent` →
`DerivedSeries.solvable_S3`). **~22 genuinely-absent gaps confirmed honest** (FOL, sheaf/topos, π₁/isotopy,
tropical semiring, Hilbert space, divergence functional, σ-additive measure, …). Top shared residual: a smooth
`Real213`-cut metric (geometry cluster), A₅-perfectness + general `isSolvable`, the de Rham comparison iso.

### ★ Homological algebra / derived functors (`homological_algebra.md`) — the calculus names its own residue operation

PREDICTION+PARTIAL, possibly the deepest consolidation: homological algebra doesn't add a field — it **names
the residue-taking operation itself**. A derived functor `Ext^n`/`Tor_n` = the calculus's `Residue(L,C)`
recipe with `L` = a non-exact functor ∘ the resolution dial, graded by `n`, tagged `q=±1`. **`Ext^{>0}`/
`Tor_{>0}` = the obstruction residue = de_rham's `H*_dR` = sheaf's `H^{>0}` = `ker δ/im δ`** (one Lean
residue, `reduced_betti_d4_contractible`); the connecting `δ`/long-exact-sequence/`δ²=0` = homology's `q=±1`
sign-propagation (`dsq_zero_universal_delta4`); proj/inj resolution = the resolution dial at chain level
(`IsResolutionShift`); `Ext⁰=Hom`/`Tor₀=⊗` = the `q=+1` exact part, `Ext¹` = extensions-mod-split (the
split-q=+1/non-split-q=−1 residue, `clo_idempotent`). So derived functors are the *systematic, graded* name
for the calculus's residue-of-a-reading construction — unifying homology + de_rham + sheaf under one machine.
Missing leg: the named `Ext`/`Tor`/resolution/exact-sequence objects (grep-confirmed absent); buildable
witness named — a nonzero `Ext¹` via `kerSizeDelta` on a non-exact resolution, now **BUILT**
(`NonzeroBetti.lean`, 56/0 PURE: hollow-triangle `H¹≠0`, `betti_one_cycle`, `cycle_vs_contractible_qpm`).

### ★ Combinatorial game theory / Sprague–Grundy (`game_theory.md`) — consolidates surreal + parity + normal-form under q=±1

PREDICTION (leverage) + PARTIAL. Combinatorial game theory adds **no new axis** — it fuses three
already-decomposed pieces: an impartial game = surreal.md's `C` (directed iterated distinguishing) in its
**symmetric/swap-trivial** case (`Raw.slash_comm`, so the value is a single unsigned Nat = the nim-value,
not a signed surreal); the nim-value `G(g)=mex{G(g')}` = the `Raw.fold` catamorphism to the canonical
Nim-heap (`raw_initial`/`dhom_unique_pointwise` — Sprague–Grundy **is** the fold-to-normal-form initiality
theorem); game-sum `G(g+h)=G(g)⊕G(h)` = **parity.md's character arrow in its 𝔽₂^k form**
(`psiNatPos_linear` PURE, the XOR-fold distributing over pointwise XOR; group `C2_6.mul`). P-positions
`G=0` = the q=+1 converging pole (`golden_is_converge`), N-positions `G≠0` = the q=−1 escape
(`no_surjection_of_fixedpointfree`); mex itself = a **bounded diagonal** (the diagonal read at finite
resolution = the first missing Nat). ★ Purity revelation: the nim-sum is PURE **only coordinatewise**
(`Fin 6 → Bool` pointwise XOR); the packed `Nat.xor` form is DIRTY (`AutKGroup.lean:71`, `propext`/
`Quot.sound` via `Nat.xor_assoc`) — a character is PURE exactly when read per-bit, the same PURE/DIRTY =
Heyting/Boolean boundary topos.md/SYNTHESIS §6 names as 213's constructive line, surfaced here on the
central arrow itself. Missing leg: the named `Game`/`Nim`/`Grundy` object (grep-confirmed absent) — the
identical ceiling surreal.md and knots.md hit; the `C`, character, and normal-form legs are PURE-anchored.
★ Follow-on: the **`mex` engine is now BUILT ∅-axiom** (`Mex.lean`, 12/0: `mexFrom_finds` = the scan lands
on a non-member = the bounded diagonal, `mexFrom_lt_mem` = minimality, `mex_eq_zero_iff_zero_excluded` =
P-position `G=0` ⟺ `0` excluded); the residual is only mex's *application on a `Game` type*.

### ★ Lefschetz fixed-point + Brouwer degree (`lefschetz_degree.md`) — the trace-weighted diagonal

PREDICTION + PARTIAL (EXTEND by consolidation). The central collapse holds fully: `L(f)≠0 ⟹ f has a fixed
point` **IS** the Lawvere/diagonal engine — its contrapositive "fixed-point-free ⟹ the self-cover leaves a
residue" is literally `no_surjection_of_fixedpointfree`, and Lefschetz is the **trace-weighted** refinement
of the same diagonal that runs Cantor/Gödel/`object1_not_surjective`. The Lefschetz number
`L(f)=Σ(-1)^i tr(f_*|H^i)` decomposes as: `tr` = the additive `×↦+` character (`tr=e₁`, `Mat2Spectrum`),
the `(-1)^i` = homology's q=±1 orientation bit (`dsq_zero_universal_delta4`; `L(id)=χ` = the Euler/`∂²=0`
cancellation, `simplex_face_euler_zero`), summed down the fold-height. Brouwer degree = the `×↦·`
holonomy/`det`-winding character (`det_holonomy_eq_one`, `first_loop_is_the_fold`); no-retraction/hairy-ball
= the q=−1 escape. The det/tr split recurs as the degree(`×↦·`, top-degree)/Lefschetz(`×↦+`, graded) split.
Missing leg: the named `Lefschetz`/`degree`/`f_*:H^i→H^i` objects (grep-confirmed absent; break shape =
homological_algebra's, every leg PURE, the named graded bundle open).

### ★ Martingales (`martingales.md`) — the q=+1 fixed point on the weight axis

PREDICTION + PARTIAL. A martingale `E[X_{n+1}|F_n]=X_n` = the conditional-expectation reading as the **q=+1
converging fixed point of the filtration-refinement step** (the `banach_fixed_point_modulated`/
`golden_is_converge` pole, read on the σ-algebra dial). The Doob decomposition `X=M+A` **is** the README
normal form `⟨C|L⟩⊕Residue` on the weight axis (M = the q=+1 fixed-point part, A = the predictable directed
residue; super/sub-martingale = the q=±1 direction bit on A) — a classical theorem that is literally the
calculus's split, a clean external corroboration. `E[·|F]` idempotent = the `clo`-projection
(`caraClosure_idempotent`/`biconj_idempotent`, T²=T); optional stopping = the fixed point invariant under a
weight-preserving Lens (ergodic_theory's measure-preserving tie); martingale convergence = the q=+1
completion-limit (`orbit_to_center_completion`, `DyadicCompletion`). Missing leg: every named martingale
object (`Martingale`/`condExp`/`Filtration`/`Doob`/`stoppingTime`) grep-confirmed absent.

### ★ Spectral sequences (`spectral_sequences.md`) — the residue operation ITERATED

PREDICTION + PARTIAL (EXTEND, genuinely new datum beyond homological_algebra). homological_algebra named the
residue operation applied **once** per degree; this note's new finding: the residue operation is **closed
under self-composition**, and a spectral sequence is its **orbit**. The page recursion `E_{r+1}=H(E_r)` =
the residue **re-entering as its own operand** (`residue_perpetually_reenters`, `ResidueReentry.lean` 14/0 —
a foundational theorem homological_algebra never used); the page index `r` = the resolution dial counting
iterations, grades **adding** under page-composition (`IsResolutionShift_compose`, `cutHalfIter`,
`ResolutionShift.lean` 17/0); convergence `E_∞` = the **q=+1 fixed point of the iteration**, with `r` the
convergence modulus (same modulated-completion as `golden_is_converge`/`orbit_to_center_completion`),
non-degeneration = the q=−1 escape (`residue_reentry_never_closes`); `d_r²=0` per page =
`dsq_zero_universal_delta4` repeated. Missing leg: the named `SpectralSequence`/`Page`/`E_r`/`E_∞` objects
(grep-confirmed absent; suggested witness — a finite two-page tower degenerating at E₂ on `NonzeroBetti`).

### ★ Hopf algebras / bialgebras (`hopf_algebras.md`) — the slash read in both directions at once

EXTEND + PARTIAL (one located break). A Hopf algebra is the distinguishing's **slash read co- as well as
contra-**: `m` (multiply/fold) = the ×↦· character; `Δ` (comultiply) = the *same* construction's co-fold
(`CoAppend213.mem_splits_iff`, the +-witness split), the two bridged by convolution `f⋆g=m∘(f⊗g)∘Δ` =
`Convolution213.conv` (49/0). The comultiplication is **calculus-native, not a missing primitive** — the
coalgebra axioms collapse onto the algebra axioms by cut-reversal (`conv_assoc`/`conv_comm`/`conv_delta_left`).
The antipode = the q=−1 unimodular residue (`multiplier_unimodular`; `FoldKlein.bothSwap_involutive`/
`bothSwap_no_fixed`), and the antipode axiom `m∘(S⊗id)∘Δ=η∘ε` is literally `DirichletIdentities.mu_conv_one`
(S⋆id=ε, 20/0), with the signed binomial (`IncidenceInversion.binomial_inversion_via_engine`) the +-cut twin.
★ The located break (PARTIAL): the **bialgebra compatibility** (Δ an algebra map, the `Δ_+⇄Δ_×` interlock)
is genuinely ABSENT — the repo's own frontier flags it as open target F1; the buildable witness is the
∅-axiom `Δ_+`/`Δ_×` distributive law on ℕ (object-level `vp_mul`). Named `HopfAlgebra`/`antipode` absent.

### ★ K-theory (K₀) (`k_theory.md`) — the difference-Lens of integers.md, one carrier up

EXTEND by consolidation. K₀ = `integers.md`'s group-completion difference-Lens run one level up:
`⟨ directed object-pair ([A],[B]) over (iso-classes,⊕) | [A]−[B] ⟩` + two already-built legs — the rank map
= the ×↦+ additive character (`vp_mul`, dimension.md), the short-exact relation `[B]=[A]+[C]` = the q=+1
exact pole (`reduced_betti_d4_contractible`); higher `K_n` = the q=−1 obstruction (the `Ext^{>0}` analogue).
★ The genuinely new datum (not a re-skin of integers.md): the repo's group-completion is **already
parametrized over an arbitrary `CommCancelSemigroup`** and proven `Quot`-free + choice-free with full
universal property (`PairCompletionUniversal.invert_is_the_universal_group_completion`:215, `lift_unique`:169,
19/0). So "ℤ from (ℕ,+)" and "K₀ from (iso-classes,⊕)" are *the same theorem at two carriers* — the
difference-Lens is **carrier-polymorphic** (ℤ at +, ℚ₊ at ·, K₀ at ⊕), sharpening the model with a carrier
parameter on `L₋` (parallel to padic's base parameter). Missing leg: the `(iso-classes,⊕)` carrier
(`K0`/`GrothendieckGroup`/`ShortExact` absent) — the engine is built and general, no object-monoid to feed it.

### ★ Morse theory (`morse_theory.md`) — read a space by a height function

PREDICTION + the deepest consolidation in the height/homology cluster. Morse theory = the
"read-a-space-by-a-height-function" *instance*: (fold-height = Morse index, `Raw.depth_slash`/`isPart_wf`) +
(homology residue `ker∂/im∂`, `reduced_betti_d4_contractible`/`kerSizeDelta`) + (the q=±1 alternating Euler
sum = `L(id)=χ`, `simplex_face_euler_zero`) + (critical point = where the gradient-distinguishing vanishes =
the residue at both poles: `GradientFlow.gradient_descent_monotone`/`MonovariantFlow.flow_reaches` q=+1 vs
`no_surjection_of_fixedpointfree` q=−1). New vs lefschetz/homology: the Morse *index* = a fifth word for the
`Raw.depth` grade (dimension/degree/pole-order/nesting/index), read at gradient flat-spots; `∂` is
read-agnostic (face-peel vs flow-line count, same q=±1 operator); Morse=singular = de_rham's "two complexes,
one residue." Named `criticalPoint`/`morseIndex`/`MorseComplex` absent (only Morse–Hedlund/Thue–Morse, an
unrelated field). Buildable witness: the **discrete Morse weak inequality** `b_k ≤ c_k`, which is
**dimension-level** — the naive count form `kerSizeDelta 5 k ≤ binom 5 k` is false for k≥2
(`kerSizeDelta 5 2 = 16 > 10`; `kerSizeDelta` is the cocycle cardinality `2^(dim ker)`), so it needs the
dim-extraction, not a one-line decide; the proven Euler equality `Σ(−1)^k c_k = χ` (`simplex_face_euler_zero`) is the clean count-form companion.

**Count.** 64 worked decompositions + the `two_cells.md` meta-decomposition + the formal `q=±1` tag; one
located partial-break (knots → two precise missing primitives) + the `Lp`/funext wall; the `det`/`tr` edge
is now **dissolved as a Lean theorem** (`Mat2Spectrum`: tr=e₁, det=e₂ of the spectrum); **thirteen**
predictions, **twelve Lean-closed** (orthogonality 2/3/**4**/6, growing-corner, convolve-rescale contraction +
dyadic completion-limit, discrete Noether-iff, the modulated Banach engine/wall defeat, Carathéodory-as-`clo`,
the formal `q=±1` tag, `continuous_iff_preimage_dyadicopen`, the **det/tr=e₁/e₂ Vieta resolution**, and the
**formal power-series semiring** `PowerSeriesSemiring`) + QR already-closed; plus Lean **groundings** of the
spectral note (`Mat2SymmetricSpectrum`: symmetric `disc≥0` = real spectrum, the `q=+1` corner), the Lie
note (`Mat2Bracket`: antisymmetry + traceless-sl + Jacobi), and the representation note (`Mat2Killing`: the
`d>1` trace character as the adjoint rep's Killing form `K=4·tr(XY)` on sl₂, `killing_gram` nondegeneracy).
The `q=+1` contraction residue spans
φ/Gaussian/ODE; the formal `q=±1` tag unites Cantor/Gödel/measure (escape) with φ/Gaussian/ODE (converge);
compactness is the `q=+1` finiteness corner; the spectrum dissolves det/tr; the Lie bracket is the `q=−1`
antisymmetry; **Stokes = the telescope** (de Rham); the Banach-engine "wall" is **defeated** (`wall_synthesis.md`).
