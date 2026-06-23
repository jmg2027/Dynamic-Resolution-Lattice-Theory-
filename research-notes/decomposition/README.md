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
> Lean census (~21 ∅-axiom modules, 13 of 14 predictions closed); the recurring breaks (the
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

### ★ Continued fractions / Diophantine approximation (`continued_fractions.md`) — the purest residue-doctrine instance

EXTEND (the deepest confirmation of the "infinity is the residue's shape" doctrine). A continued fraction
IS the calculus's **approximant-sequence pointing at an irrational**: the convergents `pₙ/qₙ` = the
computable *modulus* (the residue's finite signature), the irrational = the residue, *reached by none,
pointed at by all* (`object1_not_surjective`). The CF recurrence `pₙ=aₙpₙ₋₁+pₙ₋₂` = the SAME 2-term linear
fold as Fibonacci/golden (`ContinuedFractionConvergents` 23/0: `cfP_rec`/`cfQ_rec`/`cf_determinant`
`pₙ₊₁qₙ−pₙqₙ₊₁=(−1)ⁿ`, the q=±1 tag; φ=[1;1,1,…] the slowest=deepest-modulus q=+1 pole). Best-approximation
= the optimal pointing at each resolution (`BestApproximation.unimodular_best_approximation`); the modulus is
*literally built* (`ContinuedFractionModulus.cf_universal_total_modulus`/`cfCauchySeq`, 23/0 — the convergents
packaged as a `CauchyCutSeq`). Stern–Brocot/mediant = the modular-forms period contour (`Mediant` 11/0,
`manin_unimodular_decomposition`); √2=[1;2,2,…]=Pell (`Sqrt2ContinuedFraction` 12/0). Lagrange (quadratic
irrational ⟺ eventually periodic) = the q=±1 periodic/aperiodic dichotomy (`golden_aperiodic` disc>0 q−1 vs
`finite_order_divides_twelve` disc<0 q+1); the named periodicity theorem is the one predicted-not-built leg.

### ★ Optimal transport / Wasserstein (`optimal_transport.md`) — the FOURTH f**=clo instance

EXTEND + PARTIAL. Optimal transport = the **weight axis** read through the **f**=clo order-reversing
closure**, bound by the q=±1 duality-gap tag. New datum (not a re-skin of convex_duality): the
Kantorovich–Rubinstein W₁-duality `sup_f = inf_π` IS the same `f**=clo` biconjugation
(`FenchelMoreau.biconj_idempotent`/`closed_iff_fixed`) on the transport cost — the c-transform = the
c-Fenchel conjugate, c-concavity = the closed/fixed points — making OT the **fourth instance of the
order-reversing-closure family** (after Galois/Legendre/Nullstellensatz), now on the weight axis. ★ The
finite Kantorovich LP is *built* ∅-axiom: `OllivierRicci` (60/0) — `kantorovich_weak_duality` (weak duality
= adjoint inequality), `ollivier_plan_optimal` (zero-gap strong duality = the q=+1 tight optimum),
`transportCost`/`rowMarg`/`colMarg`. Located gap (PARTIAL): the coupling is built only as the finite-ℤ
instance; a coupling of two general `DyadicMeasure`s with marginal projection, and the named
`Wasserstein`/`Monge`/`cTransform`/`Brenier` objects, are absent.

### ★ Proof theory / cut-elimination (`cut_elimination.md`) — the calculus's own normalization in logic's clothing

EXTEND + PREDICTION. Cut-elimination IS the calculus's **fold-to-normal-form** (`raw_initial`/`view=fold`,
`dhom_unique_pointwise`) read on sequent proofs. New vs curry_howard: the cut rule = the 2-category's
**composition** (`refines_trans`/`view_factors_through_morphism`); cut-elimination = **admissibility of
composition** = arrow-normalization (`dhom_unique_pointwise` IS the admissibility); the **subformula
property** = the fold's no-new-atoms structural-recursion law (`Raw.fold_slash`); strong normalization = the
q=+1 terminating descent (`Lambek.no_infinite_descent`:273/`part_depth_succ_le`:245, the cut-rank measure),
and the proof-theoretic ordinal ε₀ = the **q=−1 height-escape** (`DepthHeightDiagonal.height_diagonal_escapes`/
`epsilon_direction`, tying ordinals.md's ceiling + godel.md's diagonal). ★ The repo even ships a *toy*
cut-elimination (`Combinatorics/Logic/CutElimination.lean` 10/0: proof=`List Bool`, cut=`++`, eliminate
adjacent unequal bits) — genuinely "cut=composition, cancel inverse pairs, length drops," but with no
formulas/cut-rank/subformula/ordinal. Predicted-not-built: a `Formula`/`Sequent` calculus with a
formula-induction Hauptsatz + subformula theorem (the buildable witness = `cutRank` dropping via
`part_depth_succ_le`, the formula-graded analogue of `FreeReduction.proj_val_eq_iff`).

### ★ Itô / stochastic calculus (`ito_calculus.md`) — the second-order residue made load-bearing by √h

PREDICTION + PARTIAL. Itô calculus = `derivative.md`'s difference-reading with the **second-order residue
revived by the √h Brownian resolution scaling**. New datum (sharpens the model): the resolution axis carries
a **scaling** parameter (h for smooth, √h for Brownian) that decides whether the O(h²) second-order residue
vanishes below the floor or is **promoted to a primary term** — the Itô correction ½f''dt is literally
`derivative.md`'s dropped O(h²) residue, revived. Grounded by `NewtonGregory` (41/0):
`obstruction_int_constant` (second forward difference `liftKZ 2` is non-trivial) + `obstruction_nat` (the
first-order Lens cannot see it) = the second-order-residue-invisible-to-first-order shape; the Taylor/½f''[dB]²
shape = `leibniz_universal_delta4`/`dsq_zero_universal_delta4`. The Brownian increment = the q=+1 Gaussian
(`orbit_to_center`/`gaussian_center_fixed_via_engine`, `variance_master`, [B]_t=t = `CLT_fair_variance_marker`);
the Itô integral = the q=+1 martingale (martingales.md, `banach_fixed_point_modulated`); the Itô isometry =
the second-moment character (`mass_conv`/`momentNum_conv`). Named `BrownianMotion`/`ItoIntegral`/
`quadraticVariation` absent (grep-confirmed 0 hits).

### ★ Class field theory / Artin reciprocity (`class_field_theory.md`) — the ×↦· character at maximal abelian extent

PREDICTION + located BREAK (EXTEND by consolidation). CFT = `quadratic_reciprocity.md`'s ×↦· character
pushed to its maximal abelian extent: the Artin map = QR's character with codomain widened from `{±1}` to
`Gal^{ab}` (`legendre_mul`, `zolotarev_mu`:229, `quadratic_reciprocity`:461 = the order-2 case); Artin
reciprocity = `galois_correspondence`'s `Fix⊣Inv` closure restricted to abelian subextensions
(`clo_idempotent`); `Frob_p` = the per-prime q=±1 local character (`FP2SqrtD.fp2dFrob_involution`:220 +
`fp2dFrob_mul`/`add`, the local quadratic Frobenius as ring-hom+involution, 32/0; `zpsd_frob` the ℤ_p lift);
Kronecker–Weber = the cyclotomic-character maximality the orthogonality corpus grounds
(`cyclic_orthogonality_modp`:254 all orders mod p, `galois_group_is_C4` concrete cyclotomic abelian group).
Located break: the global `ArtinMap`/`idele`/`adele`/`RayClass`/Kronecker–Weber bundle is absent (grep 0 hits;
⚠ false-friend flagged — `ModArith/Frobenius.lean` is the Chicken-McNugget Frobenius *number*, not the Galois
Frobenius). Buildable witness: the idele/ray-class group as a product of local `(ℤ/p)^×` + a general ArtinMap.

### ★ Non-standard analysis / hyperreals (`nonstandard_analysis.md`) — a CALIBRATED located boundary (the no-exterior axiom under test)

LOCATED BOUNDARY (calibrated, not fatal) — the first since knots, and it tests the **no-exterior axiom
(§5.1) directly**. Decisive find: the repo already ships `Hyper213` (7/0), built on **cofinite ("eventually
equal") equivalence, NOT an ultrafilter** (self-described as "weaker than ZFC's free ultrafilter but
framework-internal"). This splits the field at the quotient reading: **INTERNAL horn** — the
infinitesimal-as-sequence (`Nat→Raw`, no modulus) under cofinite quotient is ∅-axiom PURE, the same
"number = approximant sequence" `C` as padic/continued_fractions, with `const_equiv_iff` the faithful ℝ↪ℝ*
embedding. **BREAK horn** — the non-principal ultrafilter `𝒰`'s *maximality* (deciding every `S⊆ℕ`) does two
forbidden jobs: totalizes the order AND reifies the reached-by-none residue (`object1_not_surjective`); it has
no ∅-axiom witness. ★ Crucially it is **calibrated, not asserted**: the totalization is *exactly* the
LLPO-strength sign-decision the corpus PROVES non-constructive (`comparability_imp_llpo`:33 →
`llpo_of_realDichotomy`:525, 31/0), on the same omniscience ledger as `lpo_of_bw`. So §5.1 survives as a claim
under test: internal handle found and built; the irreducible remainder *measured at LLPO*, not posited as a
wall. Transfer/Łoś/`st`/`𝒰` all absent (require `𝒰`'s maximality).

### ★ Coding theory / error-correcting codes (`coding_theory.md`) — a linear code IS a cochain complex (and it's BUILT)

EXTEND — and *stronger* than the thesis predicted: the named field object is **BUILT ∅-axiom**, not absent.
A linear code = the parity χ-character read as a cochain complex: `H = δ₁` (parity-check = coboundary),
`G = δ₀` (generator), code `= ker δ₁ = im δ₀` (cocycles, the SAME ker δ as homology.md), syndrome `= δ₁x` =
the cohomology class (the residue of x mod the code), `H·Gᵀ=0 = δ²=0` (the q=±1 orientation cancellation),
`s=0`/`s≠0` = the q=±1 converge/escape tag (= `nonzero_cohomology_class`), ambient 𝔽₂ⁿ = the parity/game XOR
character. The repo ships a complete STRICT ∅-axiom `[10,4,4]` code: `MLDecoder` (13/0,
`ml_decoder_capstone` — Hamming bound, syndrome=0 clean / =3 under error, ML decoder recovery + 1-error
correction), `SpinGlass` (13/0, `delta0`/`delta1`/`cocycleObstruction`/`spin_glass_213_capstone` `H·Gᵀ=0`) —
the **Sourlas identity** (ML decoding = spin-glass ground state = cohomology, one ⟨C|L⟩ read three ways);
`Coding` (10/0, the Hamming metric `decodeML` minimizes); min distance = smallest nonzero cocycle
(`betti_one_cycle`). Predicted-not-built: the abstract parametric `LinearCode`, the Singleton/MDS bound, and
Reed–Solomon/BCH (need 𝔽_q, q>2 — the q>2 ceiling).

### ★ Matroid theory (`matroid_theory.md`) — the FIFTH `clo` closure-family instance

EXTEND + PREDICTION. A matroid = the calculus's idempotent closure `clo` (`GaloisConnection.clo`/
`clo_idempotent`/`clo_extensive`/`clo_monotone`, 15/0) read on a finite atom-carrier — the **fifth
`f**=clo`-family instance** after Galois/Legendre–Fenchel/Nullstellensatz/optimal-transport; a flat = a closed
set = a `clo`-fixed point (`FenchelMoreau.closed_iff_fixed`, welded via `cloAntitone_eq_gc_clo`). Two
matroid-specific legs: the **rank = dimension** height-reading (`LinearDependence.dimension_bound_is_count`:85,
7/0 — the rank ceiling as a pigeonhole count) and the **q=±1 complementation involution** (duality `M↔M*`,
`multiplier_unimodular`). Greedy=optimal = the "fold-to-normal-form gives the optimum" characterization (the
q=+1 closure corner where `clo` settles). Named `Matroid`/`independentSet`/`circuit`/`submodular` absent
(grep-confirmed; the "greedy" hits are the unrelated GRA cell-depth minimization). Buildable witness: the
matroid-closure `clo` on the 𝔽₂ span (`cl S = {v | r(S∪{v})=r(S)}`, idempotent via `clo_idempotent`).

### ★ Differential Galois / Picard–Vessiot (`differential_galois.md`) — galois's q=±1 solvability on the ∫-axis

PREDICTION. Differential Galois theory = `galois.md`'s **derived-series q=±1 solvability tag run on the
resolution/∫ axis** instead of the radical axis, with exactly two slot-swaps (field extension →
Picard–Vessiot differential extension; radicals → quadratures) and no new primitive. New datum: the
`Solvable.lean` derived-series operator is `step`-parametric (`hcong`-hypothesised), hence **axis-agnostic** —
it applies verbatim to the differential Galois group (`isSolvable`/`solvable_S3'` q+1 / `a5_not_solvable'` q−1
/ `solvability_two_poles`, 65/0). Liouville's `∫e^{-x²}`-not-elementary = the **q=−1 antiderivative escape**
(the same `object1_not_surjective`/`no_surjection_of_fixedpointfree` diagonal as Cantor/Gödel, on the
∫-reading; FTC anchor `gauss_conservation_telescope`). Named `PicardVessiot`/`Kolchin`/`quadrature` absent
(⚠ false-friend flagged: in-repo `Liouville` is the Liouville *number* of Diophantine approximation, unrelated).

### ★ Operator algebras / C*-algebras (`operator_algebras.md`) — the C*-axiom promotes spectral.md's q=+1 theorem to an axiom

PREDICTION + PARTIAL. A C*-algebra adds no construction — it consolidates spectral + representation + quantum
+ probability under the two invariants. New datum: the C*-axiom **promotes** `spectral.md`'s q=+1
`disc_symmetric_nonneg` (symmetric ⟹ real spectrum, the d=2 witness) from a *theorem* to a *defining axiom*,
and the Gelfand transform (commutative C* ≅ C(σ(A))) is the ×↦· character arrow's **eighth field** — "the
algebra IS its characters" (`det2_mul` 130/0, `legendre_mul`). The *-involution = the q=±1 conjugation bit
(`CDConjugation.cdConj_involutive` 7/0, `FoldKlein.klein_four_group`); states+GNS = the weight axis
(`mass_conv`/`momentNum_conv`, `CDNorm.cdNormSq` positivity 6/0). Located break: the C*-norm identity
`‖x*x‖=‖x‖²` is un-built (no `normSq_mul`), and `CstarAlgebra`/`GNS`/`Gelfand`/`HilbertSpace` absent — the
Hilbert/completion primitive shared with the analysis cluster. Buildable witness: a d=2 commutative C*-toy
(symmetric Mat2 sub-*-algebra, two-point spectrum, Gelfand via two evaluation characters).

### ★ Toric geometry / Newton polytopes (`toric_geometry.md`) — the multi-variable ×↦+ valuation made geometric

PREDICTION + PARTIAL (EXTEND by weld). Toric geometry = the **multi-variable ×↦+ valuation character**: the
Newton polytope IS the image of `prime_factorization.md`'s `vp` made multi-variable (monomial-multiply ↦
exponent-add, `vp_mul`/`vp_pow` 10/0, `vp_separation` faithful); the fan↔variety correspondence = `tropical.md`'s
(max,+) residue (`max_idem`, `Iterate213` 17/0); Bernstein's mixed volume = `cardinality`'s count-readout
(`countTrue_append`); the moment map = `convex_duality`'s f**=clo dual (`clo_idempotent`/`biconj_idempotent`).
New datum: the Newton polytope and the fan are the *same* valuation reading at two resolutions (full image vs
tropical residue) — the first object where the `vp` character and the (max,+) residue meet geometrically.
Named `ToricVariety`/`NewtonPolytope`/`fan`/`mixedVolume`/`momentMap` absent (grep-confirmed; "Newton" hits are
the unrelated NewtonGregory/NewtonInequalities). Buildable witness: `monVal : Monomial n → ℤⁿ` (per-axis
vp-vector) + the Newton polytope as its image.

### ★ Symplectic geometry / Hamiltonian mechanics (`symplectic_geometry.md`) — lie_theory's q−1 + noether's q+1 fused on one object

PREDICTION. Symplectic geometry = the **fusion of lie_theory's q=−1 antisymmetric bracket and noether's
q=+1 det=1 conservation on one object** (`Mat2` at det=1 = Sp(2)=SL₂), bound by ω = the antisymmetric
reading. The Poisson bracket = the Lie bracket (`Mat2Bracket.bracket_antisymm`:76/`jacobi`:118/`tr_bracket_zero`,
10/0); Liouville's phase-volume preservation = Noether's det=1 (`NoetherCurrent.density_conserved_of_det_one`
14/0, `det_holonomy_eq_one`); dω=0 = d²=0 (`dsq_zero_universal_delta4`). ★ Strong datum: the repo already
*names* ω — `SignedCup.gram_hermitian_gravity_gauge_split`:127 (14/0) splits the Hermitian Gram into
Re=metric (symmetric) ⊕ Im=`cup1_antisymmetric`=the symplectic form (antisymmetric, zero-diagonal), giving
ω's three defining properties from existing PURE theorems. The two parent files live on opposite residue
poles; symplectic geometry is where they are one object's two readings. Named symplecticForm/PoissonBracket/
Hamiltonian/Darboux absent (⚠ false-friends flagged: Liouville function/number, Hamiltonian path/cycle).

### ★ Random walks / harmonic functions (`random_walks.md`) — harmonic = Laplacian-kernel = martingale, one q=+1 object

EXTEND + PREDICTION. Random walks fuse graph_theory's Laplacian kernel and martingales' q=+1
conditional-expectation fixed point at **one q=+1 object**: harmonic function = Laplacian-kernel =
martingale-on-the-walk are **three names for one thing**, with the mean-value property the identity arrow
between them (`Δf=0 ⟺ Af=f ⟺ f(x)=avg_{y∼x}f(y) ⟺ E[f(X_{n+1})|X_n]=f(X_n)`). Maximum principle / Dirichlet
uniqueness / harmonic=hitting-probability are forced by the q=+1 pole (no interior escape; residue on the
boundary); recurrence/transience = the q=±1 tag (return vs escape-to-boundary). ★ Notable find:
`WeightedGreen.lean` (11/0) ships a *constructed* arbitrary-finite-weighted-graph ℤ-Laplacian
(`wLap`, `weighted_green` discrete Green/IBP, `wlap_mass_conservation`, gradient-flow ∇𝓕=−4Δ) — which
graph_theory.md had recorded as absent (stale gap, now corrected). Also `GraphLaplacian` 16/0,
`GraphConnectivity` 8/0. Named harmonic/Dirichlet/randomWalk objects absent. Buildable witness:
`ker(wLap)={constants}` on a connected graph.

### ★ Descriptive set theory (`descriptive_set_theory.md`) — the diagonal escape graded by ordinal height (+ a calibrated boundary)

PREDICTION + located non-constructive boundary. The Borel/projective hierarchy = the **fold-height axis
indexed by ordinals** (= the hierarchy, ordinals.md/`Lambek.isPart_wf`/`MuNuMirror.ascent_unbounded`) +
the q=±1 complementation swap (Σ↔Π) + the **q=−1 diagonal escape** (analytic⊋Borel/Suslin =
`object1_not_surjective`/`no_surjection_of_fixedpointfree` made a hierarchy theorem, projection-as-diagonal).
New datum: the diagonal-escape *graded by ordinal height on sets*. The perfect-set property = cardinality's
uncountability; determinacy = the q=±1 game tag (`Mex.mex_eq_zero_iff_zero_excluded`, ties game_theory). ★ The
higher reaches (Borel/projective determinacy, perfect-set at projective levels) are a **calibrated
non-constructive boundary** — large-cardinal/Choice-strength, located where the fold ascent leaves the finite
signature, analogous to non-standard analysis's ultrafilter at LLPO. Named Borel/analytic/Suslin/Wadge
objects absent (Borel hits are all Heine–Borel compactness).

### ★ Hodge theory (`hodge_theory.md`) — the fold-height refined to a (p,q) bigrading + the signed q=±1 star

PREDICTION + PARTIAL + genuine refinement (the `HodgeConjecture/` tree is *substantially built*). Hodge
theory = de_rham's `H*` with the single fold-height grade `n` **refined into a (p,q) bigrading** (height read
through the complex-structure Lens `J`, `J²=−1`, splitting `H^n` by the `J`-eigenvalue `i^{p−q}`) + the
**Hodge star = the q=±1 duality involution, SIGNED**: `⋆²=(−1)^{k(n−k)}` (`SignedHodgeStar.star_star_eq_sign`
12/0, `Hodge/SignedStarC4.signed_star_sq_neg_I` 10/0) — `+1`/involution on even grades = Poincaré duality
(`PoincareDuality.poincare_duality_delta4` 2/0), `−1`/complex-structure `C₄≅ℤ[i]` on odd grades
(`signed_star_ring_is_gaussian`, `cp_i_is_hodge_complex_structure`). Harmonic = q=+1 Laplacian-kernel fixed
point; unique harmonic representative = the q=+1 fold-to-normal-form. New datum: the signed `⋆` SHARPENS
homology's q=±1 two-pole story — the involutive `⋆`-pole is *itself* q=±1-graded (`⋆²=±1`), the `−1` half
being where the complex structure / CP `i` lives (`hodge_involution_universal_delta4` 5/0, `J_is_Q_isometry`/
`hodge_index_master_theorem` 5/0). Located break: no harmonic-projection iso `H^n≅ker Δ` (needs the
Real213/smooth-metric residue), and Lefschetz `sl₂`/Hard-Lefschetz absent (grep-confirmed).

### ★ Free probability (`free_probability.md`) — the R-transform = the ×↦+ character for free convolution

EXTEND + PREDICTION. Free probability = gaussian_clt's CLT structure with three substitutions, all inside
the Reading `L` (none in `C`): `⊞` for `⋆`, the R-transform (the *free log*) for `log`, the semicircle for the
Gaussian — driven by one swapped slot: the moment↔cumulant lattice restricted from ALL partitions (classical)
to **NON-CROSSING partitions = Catalan** (free). New datum: the R-transform is the ×↦+ additive linearizer of
`⊞` (`R_{μ⊞ν}=R_μ+R_ν`, the same arrow as `vp_mul`/log, the **8th field** it runs through), and
`R_μ=G_μ⁻¹−1/z` is exponential.md's `+↦×` toggle, so the R-transform is the free log by the *same arrow
structure*, not analogy. ★ Sharpest grounding: the free moment↔cumulant relation over non-crossing partitions
is literally a convolution self-square — `CatalanSegner.catSeg_succ` (`catSeg(n+1)=conv catSeg catSeg n`, 7/0;
"Catalan = the conv self-square fixed point"), `Catalan.catalan` (17/0, non-crossing chord diagrams),
`MotzkinNumbers.motzkin_catalan_table` (9/0). Semicircle = the free-CLT q=+1 fixed point = random_matrix's
spectrum. Named freeConvolution/Rtransform/semicircle/freeCumulant absent.

### ★ Percolation (`percolation.md`) — p_c as the q=±1 phase-transition point (thin / honest PREDICTION)

PREDICTION (thin — honestly the weakest of the connectivity cluster, mostly analogy). The grounded collapse:
the infinite cluster = the q=−1 escape residue (literally random_walks's transience, the same
`OneDiagonal.no_surjection_of_fixedpointfree` diagonal as Cantor/Gödel/measure; subcritical = q=+1 converge),
on top of graph_theory's static connectivity = dim-ker reading (`GraphConnectivity.closed_const` 8/0,
`KernelConstancyUniversal.bipAdj_connected` 20/0). The new element — reading the q=±1 pole *as a function of
edge-probability p*, with `p_c` the pole-transition and `θ(p)` the residue size — has **no direct Lean
witness**: the entire `p`-dependent transition layer (`p_c`/θ/infinite-cluster/FKG/Kesten self-duality/RSW) is
unbuilt (sits on the Real213 value-cut + measure.md's Choice-flavoured residual). Recorded honestly as weaker
than its neighbours: the static legs + q=±1 tag are PURE, the transition itself is analogy.

### ★ Renormalization group (`renormalization_group.md`) — the resolution dial made a FLOW (+ the DRLT tie)

PREDICTION + PARTIAL. The RG = the calculus's **resolution dial made a continuous flow** whose UV/IR fixed
points are the q=±1 poles, universality = the q=+1 attractor's basin = the fold-to-normal-form. New datum: the
dial run as a one-parameter flow on *values* (the coupling) completes the resolution axis's **three reading
modes** — iterated-on-residues (spectral sequences), scaled (Itô), **flowed (RG)**. The RG semigroup
(grades add, irreversible) = `IsResolutionShift_compose`:130 + `cutDouble_no_grade`:355 (semigroup not group);
IR attractor = `converge_residue_fixed` q+1, UV repeller = `escape_residue_outside` q−1, marginal =
`multiplier_unimodular`. ★ The DRLT tie is real (and honestly bounded): the repo's *own physics branch* builds
the running coupling `1/α_3(N)=(NS²−1)·S(N)` as a resolution-indexed rational sequence
(`AsymptoticFreedom.asymp_free_via_monotone` 6/0, β-sign = monotonicity, IR fixed point = a ζ(2) bracket
`Basel/Bound` 27/0, `RunningGap.running_gap_master` 3/0) — but the *continuous* β-function is the Real213
residue (the field's own docstring marks it an interpretive posit). Flagged a vacuous
`renormalization_auto:=True:=trivial`. Named RGflow/betaFunction objects absent.

### ★ Operads / higher algebra (`operads.md`) — the Raw.fold composition made arity-graded

PREDICTION. An operad = the calculus's `Raw.fold` composition made **arity-graded** (the multicategory above
two_cells's 2-category of readings); the operad axioms = the fold's `raw_initial`/`dhom_unique_pointwise`
coherence; Assoc/Comm/Lie = the q=±1 readings of one fold (`slash_comm` commutative q+1, `Mat2Bracket`
antisymmetric q−1); A∞ coherence = the associahedron = Catalan (`catalan_recursion_n` `Cₙ₊₁=ΣCᵢ·Cₙ₋ᵢ`, the
free-binary-operad composition recurrence, 17/0). ★ Strong in-repo find: `CombinatorialArity.lean` (5/0)
already defines an arity-graded distinguishing `rel : (Fin k → Raw k) → Raw k` and proves
`arity_2_unique_via_k_ge_3_vacuous`:180 — the calculus's operad is provably **binary-generated**. A∞
witness-carrying normal form = `FreeReduction.proj_val_eq_iff`. Named Operad/∘ᵢ/equivariance/A∞ objects
absent (the in-repo "operad level" in GRA is a grade reading `operadLens≡gradeLens`, not the substitution
structure). Buildable witness: a `fold_split = catalan_convolution` bridge (`Raw.fold_slash`:37 = split a
composition tree at the root, matching `catalan_recursion_n`).

### ★ Topological quantum field theory (`tqft.md`) — the character arrow as a monoidal functor ⊔↦⊗

EXTEND + PARTIAL. A TQFT = the character arrow (×↦·) promoted one categorical level to a symmetric monoidal
functor `⊔↦⊗` on cobordisms — `Z(M⊔N)=Z(M)⊗Z(N)` is the character's product-preservation with the
codomain swapped to Vect; gluing = the fold-composition (`raw_initial` + the 2-category); ∂ = homology's q=±1
orientation bit (`dsq_zero_universal_delta4`); the 2d-classification's Frobenius structure = hopf_algebras's
convolution (`m`+`Δ`, `Convolution213` 49/0, `mu_conv_one`). ★ Surprise built grounding: `GRA/Monoidal.lean`
(13/0) already ships a symmetric monoidal `product` with unit `trivial23` (Z(∅)=k's shadow), braiding
`productSwapIso_involutive` (23/0), and **`product_NT_NT_grade`: grade(M⊗N)=grade M+grade N** — Atiyah's ⊔↦⊗
axiom at the grade readout, the first built instance of "a monoidal product whose readout is the additive
character." Located break: the named cobordism category / ambient-isotopy quotient (recurring from knots),
and no general `Vect`/`⊗` object (the d>1 ceiling); the FP2SqrtD "Frobenius" is the number-theoretic
Frobenius (false-friend flagged). Buildable witness: bundle `product_NT_NT_grade`+`productSwapIso_involutive`+
unit homs into one `IsMonoidalGradeFunctor`.

### ★ Quantum groups (`quantum_groups.md`) — the deformation-q vs tag-q: CONTAINMENT, not identity (a precise BREAK)

PREDICTION + BREAK — the most on-theme test, and it yields a rigorous negative. A quantum group =
hopf_algebras' Hopf structure deformed by `q` on the count-reading (the q-binomial is BUILT:
`QBinomial.qbinom`/`qbinom_pascal`, `qbinom_q1` the q→1 classical limit GENERAL, 11/0; `QBinomialSymmetry`
12/0). ★ The decisive datum: evaluating the BUILT `qbinom` recurrence at q=−1 gives **not a sign-fold but the
Lucas/fermionic table** `[n,k]_{−1}=C(⌊n/2⌋,⌊k/2⌋)` (non-negative counts, zeros where n even/k odd) — whereas
the `ResidueTag` tag-q=−1 is a unimodular `multiplier=−1` swap bit (`bothSwap`). So the **deformation-q (a
continuous/integer scaling dial on the count) and the tag-q (a discrete ±1 unimodular swap bit on the
residue) are different objects**: they share the ±1 *locus* by containment (the tag's ±1 is the unimodular
boundary the deformation passes through), but the *content* read there differs — fermionic count value vs swap
bit. The naive "deformation-q IS the tag-q" is FALSE as identity, true only as containment; at q=+1 both align
(classical/converging, `qbinom_q1` + `golden_is_converge`). Named U_q/R-matrix/Yang–Baxter absent (R-matrix
at knots's located break). Buildable witness: `qbinom_qm1_lucas` (`qbinom(−1) n k = C(n/2,k/2)`, verified true
by computation) — would machine-check the BREAK.

### ★ Information theory / Shannon (`information_theory.md`) — the ×↦+ entropy character read on a channel

EXTEND (consolidation). Shannon information theory = entropy's ×↦+ character read on a channel. New datum
over entropy/coding: **mutual information `I(X;Y)=H(X)+H(Y)−H(X,Y)` is that same additive character read on
the joint-vs-conditional — the channel's preserved information = the additivity-*defect* = the channel
residue** (`MutualInfo.mutualInfoBits` 12/0, `mutualInfo_self_eq_entropy`, `entropy_subadditive`,
`mutualInfo_independent_zero`); capacity = the weight-axis variational optimum; the coding theorem = the q=±1
rate-vs-capacity threshold that **links to coding_theory's syndrome-zero achievability** (R<C/q+1/s=0 ⟷
R>C/q−1/s≠0). ★ Surprise: `Channel.lean` is BUILT (8/0) — `noiseless_capacity=1`, `bscCapacityNum/Den=k/2^k`
(capacity as exact dyadic rational), `bsc_half_capacity`; and `source_coding_optimal` (10/0,
optimalCodeLength=n=H). Capacity *values* built; the `C=max I` variational object, the noisy-channel coding
theorem (needs real-valued log = Real213 residue), data-processing inequality, and AEP object absent.

### ★ Nash equilibria / strategic game theory (`nash_equilibria.md`) — the q=+1 fixed point of best-response

PREDICTION + PARTIAL (EXTEND, no new axis). A Nash equilibrium = the calculus's **q=+1 fixed point of the
best-response self-map** — the *converge* side of the same diagonal/self-map engine (lefschetz_degree) whose
*escape* side (q=−1) is Cantor/Gödel (`lawvere_fixed_point` 11/0: q+1 a fixed point exists vs q−1
`no_surjection_of_fixedpointfree`). New datum: Nash is the strategic name for that q=+1 pole — a **third
carrier** for the central diagonal engine alongside Lefschetz (trace-weighted, topological) and combinatorial
games (mex bounded diagonal). The von Neumann minimax theorem (zero-sum: max min = min max) IS convex_duality's
LP duality made tight (`OllivierRicci.kantorovich_weak_duality`+`ollivier_plan_optimal` 60/0, the sup=inf no-gap
q=+1 optimum) — adding zero-sum games as a **sixth instance** of the LP-duality/f**=clo family. No-pure-equilibrium
= the q=−1 escape recovered by mixing (`mex_eq_zero_iff_zero_excluded`). Located/calibrated break: the
continuous Brouwer/Kakutani existence on a compact convex Real213 simplex (Brouwer is itself LLPO-strength,
SYNTHESIS §5) — only the discrete Lawvere + contraction-Banach fixed points are built. Named Nash/minimax/
strategy/payoff objects absent. Buildable witness: a 2×2 zero-sum minimax instance via OllivierRicci's LP saddle.

### ★★ Motives (`motives.md`) — the calculus recognizing its OWN engine (the deepest reflexive consolidation)

PREDICTION + the deepest reflexive consolidation. Motives ARE the calculus's **universal-factorization
mechanism** (`Lens.view = Raw.fold`, `raw_initial`) named in cohomology. Grothendieck's motive = "the universal
cohomology theory through which every Weil cohomology factors uniquely" — which is EXACTLY `raw_initial`/
`dhom_unique_pointwise` (6/0): `Lens.view = Raw.fold` is the unique arrow out of `Raw`. So the category of
motives = the universal construction `C`/`Raw` (initial object); each Weil cohomology (Betti/de Rham/ℓ-adic) =
a Lens `L` factoring through it (`view_factors_through_morphism` 3/0 — literally the realizations are different
Lenses on the SAME `C`, the same "homology/de Rham/sheaf = three outputs of one machine" as homological_algebra);
the motivic Galois group = the `Aut` of the universal Lens (`det_holonomy_eq_one`); the Tate twist/weight = the
fold-height grading (`isPart_wf`); the standard conjectures = the q=±1 **faithful** (`object1_injective`,
PROVABLE) / **total** (`object1_not_surjective`, the escape residue, CONJECTURAL) split. ★ The framing that
keeps it from re-skinning homological_algebra: that note named the `Residue(L,C)` half of the normal form;
**motives names the `⟨C|L⟩` half** — they are the two reflexive halves of `⟨C|L⟩ ⊕ Residue(L,C)`, the calculus
recognizing its own engine. Named Motive/WeilCohomology/realization/motivicGalois objects absent (the
universal-property *mechanism* is, conversely, the most-built thing in the repo — it IS the Lens framework).

### ★ Tannakian duality (`tannakian_duality.md`) — "object = its readings" promoted to a reconstruction

PREDICTION. Tannakian duality = the founding sentence `OBJECT = ⟨C|L⟩` ("an object IS its readings", yoneda)
promoted to a **reconstruction**: the group is the `Aut` of its forgetful monoidal Lens, `G ≅ Aut^⊗(ω)`. The
fiber functor ω:Rep(G)→Vect = the forgetful `Lens.view`:42; `G=Aut^⊗(ω)` = the `Aut`-invariant q=+1 character
reading (`det_holonomy_eq_one` 26/0, `AutKGroup_capstone`:210); the ⊗-structure = the monoidal grading
character (`GRA/Monoidal.product_NT_NT_grade` 13/0, tqft's anchor). Pontryagin duality = the abelian/1-dim
special case (fourier's self-dual cyclic Ĝ); neutral⟺affine-group-scheme lands on hopf_algebras. Ties motives'
motivic Galois (= Aut of the universal Lens) and the `raw_initial` universality. Named Tannakian/fiberFunctor/
Pontryagin objects absent (the located break); buildable witness: recover `Aut_K` as the ⊗-Aut of its
forgetful Lens.

### ★ Combinatorial species (`species.md`) — the EGF categorified (the count reading before cardinality)

PREDICTION (EXTEND by categorification). A combinatorial species = generating_functions' family count-reading
stopped one step *before* cardinality — a Σₙ-set `F[n]` per label-size, with cardinality (`|F[n]|/n!`) the Lens
recovering the EGF. The four species operations are the four EGF operations seen *upstream* of the count and
descend because the cardinality Lens is a functor commuting with them: species-product ↦ EGF-product = the
convolution character (`ConvolveProfile.mass_conv` 20/0, `Convolution213` 49/0); the exp formula = exponential's
`+↦×` (`vp_mul`). New datum: the **categorification (vertical) axis** on the count-reading — every cardinality-
style reading (cardinality/generating_functions/probability) has an un-counted functor above it. ★ Grounded
Burnside/cycle-index: `Sym3OctetOrbits` (28/0) is a real orbit/cycle-index instance (`sym3_burnside_arithmetic`,
`suborbit_decomposition` `60=4+0·2+28·3+28·6`), the relabel Σₙ-action via `PermGroup` (19/0). Named Species/
cycleIndex/molecular objects absent; buildable witness: a finite-label Species as a List/subtype Σₙ-set
generalizing the octet, with speciesProduct welded to `Convolution213.conv`.

### ★ Domain theory / denotational semantics (`domain_theory.md`) — the q=+1 fixed point as an order-colimit

PREDICTION. Domain theory = the calculus's q=+1 fixed-point engine reached as an **order-colimit**
(lfp f = ⊔ₙ fⁿ(⊥), the iteration ascending to a directed supremum, index n = the modulus) instead of the
metric-completion the neighbours use. ★ Strong find: the repo **already builds the order-theoretic least
fixed point** — `Order/KnasterTarski.lean` (19/0): `lfp = glb{x | f x ≤ x}`, `lfp_fixed`(f lfp = lfp),
`lfp_least`, dual `gfp` — the impredicative construction of the exact lfp denotational recursion needs (Kleene's
⊔fⁿ(⊥) is the predicative version of the *same* lfp). Scott-continuity = the resolution axis (commutes with
directed colimits). D≅[D→D] = Lawvere's diagonal **tamed to q=+1 by ⊥/partiality**: `lawvere_fixed_point` reads
as Cantor's q−1 escape on total maps but as consistent self-application q+1 when every Scott-continuous map has
its own lfp — ⊥ flips the multiplier bit. Named CPO/ScottContinuous/Kleene-iteration objects absent; buildable
witness: a Kleene lfp atop the built K–T lattice (fⁿ(⊥) ascending chain whose sup `lfp_fixed` already pins).

### ★ Galois cohomology (`galois_cohomology.md`) — the residue operation on the Galois G-action

EXTEND + PARTIAL. Galois cohomology = homological_algebra's residue-taking operation `Residue(L,C)`
instantiated at `L=(−)ᴳ` (the Galois invariants = galois's `Fix`), graded by n, tagged q=±1, fed galois's
G-action: H⁰=Mᴳ the q+1 exact part (`clo_idempotent`); H¹=crossed-homs-mod-principal the q−1 first obstruction
(`ker δ¹/im δ⁰`, the same mechanism as `NonzeroBetti`'s built nonzero H¹ 56/0); H²=Brauer the second residue;
the connecting δ/LES/Kummer = the `dsq_zero_universal_delta4` sign-propagation. ★ New datum: **Hilbert Theorem
90 (H¹(Gal,L*)=0) = the q+1 VANISHING of the ×↦· multiplicative character's first residue** — binding the
corpus's central character arrow (`det2_mul`/`legendre_mul`/`det_holonomy_eq_one`) to a cohomology-vanishing
(the empty-residue `reduced_betti_d4_contractible` shape, vs NonzeroBetti's q−1 hollow cycle). The Galois G is
`CyclotomicFive.galois_group_is_C4` (4/0); cocycle exemplar `MinkowskiCocycle` (6/0). Named GroupCohomology/
Hilbert90/Brauer objects absent; buildable witness: a cyclic H¹(Cₙ,L*) toy forcing norm-1 cocycles principal.

### ★★ Stone duality (`stone_duality.md`) — the Ω=Bool reading ⟺ its spectrum (a FOURTH calibrated boundary)

LOCATED BOUNDARY (calibrated at LLPO). Stone duality splits exactly on the calculus's own constructive line:
the **Boolean-algebra side is ∅-axiom BUILT**, the **ultrafilter Stone-space side is the calibrated
non-constructive exterior — the SAME ultrafilter nonstandard_analysis located at LLPO**, recurring verbatim
(totalize the valuation + reify the spectral point). ★ Load-bearing correction: `Order/BooleanAlgebra.lean` is
BUILT and ∅-axiom (**25/0** — `cmpl_unique`, `cmpl_cmpl`, both De Morgan laws by propext-free rewriting, the
α=Bool witness by `decide`); the algebra element/clopen = `FlatOntology.Object1 = decide(s=r)` (12/0), the
topos Boolean pole. The Stone space Spec(B) IS the points-from-readings reconstruction (yoneda/tannakian/
motives) carried to the maximal/uncountable index where it needs the BPI/LLPO exterior (`comparability_imp_llpo`
2/0 → `llpo_of_realDichotomy` 31/0, the omniscience ledger `LPO`/`LLPO`; `Hyper213.cofiniteEquiv` is the
internal horn one step below). Named Stone/Ultrafilter/Spec/clopen objects absent (the spectrum side has no
∅-axiom witness — building it would need the forbidden choice fragment). This is the **fourth calibrated
boundary**, all four converging on the one ultrafilter/LLPO point — the no-exterior axiom tested at its sharpest.

### ★ Linear logic (`linear_logic.md`) — the character split + the q=±1 involution made a logic

EXTEND + PREDICTION. Linear logic = the calculus's two invariants made into a logic, no new axis: the
**multiplicative ⊗/⅋ vs additive &/⊕** connectives = the **×↦· / ×↦+ character-mode split** (Invariant A) made
the primary logical structure; **linear negation A^⊥⊥=A = the q=±1 involution** (`multiplier_unimodular` q·q=1,
`FoldKlein.bothSwap_involutive`); ★ De Morgan `(A⊗B)^⊥=A^⊥⅋B^⊥` = the involution swapping the two character
modes, and it is *built*: `bothSwap = negQ∘recQ` (`bothSwap_eq_negQ_recQ`:40) is literally the additive fold
(negation, `negQ_involutive`) composed with the multiplicative fold (reciprocal, `recQ_involutive`),
FoldDuality 13/0. Resource-sensitivity (no weakening/contraction) = the `Raw` combine's no-duplication
(`Raw.slash x y` requires `h:x≠y`, `Raw.fold_slash`:37 uses each branch once — contraction needs x=x, blocked);
!/? exponentials = the structural-rule residue (the bridge back to the cartesian). Cut-elimination = the
fold-to-normal-form (cut_elimination.md). Named LinearLogic/⊗/⅋/!/proofNet objects absent (the TensorCalculus
tensor is the differential-geometry false-friend, flagged). Buildable witness: a `LinearFormula` inductive with
`dual_dual : dual(dual A)=A` (the `bothSwap_involutive` involution shape) + `dual_tensor` De Morgan by rfl.

### ★ Homotopy theory / model categories (`homotopy_theory.md`) — Ho(C) = the Quot-free localization

EXTEND + PARTIAL-BREAK. A model category = two_cells's 2-category of readings + equivalence's `Lens.refines`
weak-equivalence localization + a q=±1 fibration/cofibration lifting dual (`Mat2Bracket.bracket_antisymm`).
★ New datum: **Ho(C) = localization at weak-equivalence = the Quot-free `LensImage`/`FreeReduction` Σ-quotient**
(`LensImage.proj_val_eq_iff` Unified 14/0, `FreeReduction.free_group_quotient_no_quot` 26/0) — the homotopy
category, the localization, the Lens-image quotient, and the free-reduction normal form are ONE construction
named four ways, the same colimit Side-A machinery promoted from the knots/π₁ break. Weak equivalence =
`Lens.refines` (refl/trans 11/0); 2-of-3 = `refines_trans`; πₙ = fundamental_group's loop graded by
fold-height (`holonomy_append`/`first_loop_is_the_fold` 26/0); fibration LES = the residue δ
(`dsq_zero_universal_delta4`). The full homotopy quotient (maps mod a continuous ambient family) = the **third
verbatim recurrence** of the isotopy/colimit break Side B (knots/fundamental_group); the confluent-terminating
q=+1 corner IS built (FreeReduction), Side B (Novikov–Boone-grade) theorem-grade absent. Named ModelCategory/
fibration/weakEquivalence/Quillen objects absent.

### ★ Iwasawa theory (`iwasawa_theory.md`) — the p-adic resolution TOWER + the modulus as a power series

PREDICTION + located gap (the p-adic L-function). Iwasawa theory = padic's p-adic resolution **tower** (`base`=p
ascended) + the power-series modulus **Λ=ℤ_p[[T]]** + the class-number **per-level residue** + the **Main
Conjecture as the deepest character=residue tie** (the ×↦· L-function = the q=±1 residue's characteristic
signature). ★ Stronger-than-predicted at two legs: the *tower shape* is BUILT (`CompletionTower` 7/0 —
completion-of-completions returns home by rfl, modulus the only ascending datum, `tower_is_single_inner`/
`completion_idempotent`; `IsResolutionShift_compose` — level grades add (ℕ,+)), and *Λ as a power-series
semiring* is BUILT (`power_series_semiring` 33/0). The class number has a real ∅-axiom toy at the q=+1
empty-residue pole (`EisensteinClassNumber.reduced_disc_neg3_unique` h(−3)=1, 1/0). The Main Conjecture is
prose-only and the **p-adic L-function is the located gap** (the Real213-cut residue, same boundary as
modular_forms/zeta_euler/padic). All named Iwasawa objects (Iwasawa/characteristicIdeal/mainConjecture/μ,λ/
pAdicL/Λ-as-group-ring) grep-confirmed absent; buildable witness: a two-rung class-number-growth toy
(h(−3)=1 p⁰ q+1 vs a class-number-p discriminant q−1, tagged via ResidueTag, exhibiting p^(λn) with λ=1).

### ★ Ramsey theory / extremal combinatorics (`ramsey_theory.md`) — the q=±1 unavoidability threshold (strongly BUILT)

EXTEND + PARTIAL, unusually well-grounded. Ramsey theory = the **count-reading at a finite threshold**, read at
its two q=±1 poles: pigeonhole = the q+1 forced-coincidence base (the cardinality diagonal folded back at finite
size, `Pigeonhole.exists_collision` 5/0), the probabilistic lower bound = the q−1 escape (`CountExistence.deficit_exists`
10/0), the extremal corpus = the q+1 saturation pole (dual double-count). ★ New datum: Ramsey is the **flip-locus**
where the count-reading's escape has a finite ceiling and switches sign — both signs visible at once, separated by
the threshold. ★ Strongly built: `RamseyNamedBound.ramsey_lower`:174 (R(k,k)>N, named & closed, 13/0),
`SpernerChains.sperner_theorem`:534 (50/0), `Sperner` (47/0), `LymInequality` (5/0), `BollobasSetPair.bollobas`:257
(21/0), `BollobasCount` (36/0), `ErdosSzekeres.erdos_szekeres`:587 (26/0) — the proof-ISA independently records
the same split (Ramsey-lower = union-bound face, Sperner-upper = dual double-count face). Located gaps: Turán
`ex(n,K_r)` absent (the edge carrier exists; buildable, no witness asserted), van der Waerden/Szemerédi absent
(the density leg meets the calibrated infinite-quantifier residual); R(s,t) as a defined number absent (only the
inequality).

### ★ Derived / triangulated categories (`derived_categories.md`) — the residue operation's natural home

EXTEND + PREDICTION + PARTIAL-BREAK. A derived category = homological_algebra's residue-taking operation
`Residue(L,C)` placed inside homotopy_theory's Quot-free localization — the home that operation needed. D(A) =
chain complexes localized at quasi-iso = the SAME Quot-free `LensImage`/`FreeReduction` Σ-quotient as Ho(C)
(a quasi-iso = iso on all Hⁿ = "same under the cohomology reading" = `Lens.refines`). The shift `[1]` =
fold-height+1 carrying the q=±1 swap (`IsResolutionShift_compose` additive grades; differential sign-flip =
`bracket_antisymm`; `[2]≅sign-identity` = `multiplier_unimodular` q²=1). The distinguished triangle = the LES
packaged into one rotatable object (cone Z = the q−1 residue, witnessed concretely by
`NonzeroBetti.loopClass_not_coboundary` 56/0; the third map = the connecting δ into the shift; the triangle's
LES = `dsq_zero_universal_delta4`). Lf/Rf = the resolution-dial lift; octahedral axiom = a 2-cell coherence
(`refines_trans`/`view_factors_through_morphism`). Named DerivedCategory/triangulated/shift/Cone/quasiIso
objects absent (the octahedral hits are the binary octahedral group 2O, false-friend flagged); the
calculus-of-fractions/roof corner = the same Side-B located break as the homotopy/isotopy quotient.

### ★ Hyperbolic / non-Euclidean geometry (`hyperbolic_geometry.md`) — the discriminant-sign trichotomy as curvature

EXTEND (deep consolidation). ★ New datum: the three constant-curvature geometries (elliptic K>0 / Euclidean K=0
/ hyperbolic K<0) ARE the one discriminant-sign trichotomy `sign(disc=tr²−4det=(μ−ν)²)` the corpus already
proves — read as the curvature sign. This unifies spectral.md (complex/real spectrum), golden_ratio/
continued_fractions (finite/infinite order), and `CrossDetTraceField.disc_sign_is_line_cusp_curve`:248
(hyperbolic/parabolic/elliptic = G>0/T=0/U<0, 20/0) as ONE geometric trichotomy: disc>0 hyperbolic q−1
(`golden_hyperbolic`/`golden_aperiodic` escape) vs disc<0 elliptic q+1 (`finite_order_divides_twelve` 29/0,
periodic rotation) vs disc=0 flat (`signature_trichotomy` 4/0). PSL(2,ℝ) = the Möbius holonomy
(`det_holonomy_eq_one`, `mediantLens_view_reachable`); ★ Gauss–Bonnet is BUILT discretely
(`DiscreteGaussBonnet.gauss_bonnet_Kmn`:42 `totalVertexCurv = 2·eulerChar`, 12/0 — the curvature–Euler
telescope). Located break: the smooth geometric objects (HyperbolicPlane/UpperHalfPlane/PSL2R/smooth ∫K=2πχ
with 2π) absent — the Real213-cut smooth-metric residue; the angle-sum/parallel-postulate-as-named-theorem is
the PREDICTION leg (only the disc-sign number trichotomy is built).

### ★★ Étale cohomology / the Weil conjectures (`etale_cohomology.md`) — the 100th: three threads converge

PREDICTION + substantial PARTIAL. Étale cohomology + the Weil conjectures = the **convergence of three
already-grounded threads on one object** (a variety over 𝔽_q): (1) the Lefschetz trace formula
`#X(𝔽_q)=Σ(−1)ⁱtr(F*|Hⁱ)` = lefschetz_degree's trace-weighted alternating diagonal, with the arithmetic
Frobenius F the self-map (fixed points = 𝔽_q-points); (2) the zeta `Z(X,t)=∏_x(1−t^deg x)⁻¹` = zeta_euler/
modular_forms' ×↦· Euler product, re-based from primes to closed points (`summatory_mul`/`dconv_mul`/`geom_sum`);
(3) étale Hⁱ = motives' ℓ-adic realization Lens. ★ The Weil RH `|α|=q^(w/2)` = Invariant B (the q=±1 tag)
promoted to a continuous eigenvalue-magnitude constraint graded by the fold-height weight w; the functional
equation = the q=±1 Poincaré reflection. New in-repo anchor: the **arithmetic Frobenius is BUILT** at the
per-prime level — `FP2SqrtD.fp2dFrob` (32/0), Galois conjugation on 𝔽_{p²}, with `fp2dFrob_involution`:220
(σ²=id, the q=±1 bit), `fp2dFrob_mul`:267 (ring-hom), `fp2dMul_self_frob`:318 (x·σ(x)=Norm). Named étale/Weil/
zetaVariety/Deligne objects absent (the Weil-operator J=⋆ Hodge hits + Chicken-McNugget Frobenius are
false-friends, flagged); buildable witness: the Frobenius–Legendre bridge (√D)^p≡(D/p)√D welding `fp2dFrob`
to the QR character.

### ★ ∞-categories / higher category theory (`infinity_categories.md`) — the 2-category with fold-height up the cell-dimension

EXTEND + PREDICTION. An ∞-category = the calculus's 2-category of readings (two_cells) with the **fold-height
axis run up the cell-dimension** — n-cells-for-all-n = the coherence tower (`MuNuMirror.ascent_unbounded`/
`succ_not_idempotent` 8/0 applied to the cell-grading). New datum: cell-dimension = the fold-height coordinate
already in C; the 2-category is the height-≤2 truncation, removing the truncation (no finite ceiling) gives
cells at every dimension. The "∞" (never-closing tower) = the iterated-residue re-entry
(`ResidueReentry.residue_perpetually_reenters` 14/0, = spectral_sequences' residue-iterated); ∞-groupoid =
space = the all-invertible q+1 `LensIso` pole; A∞ coherence = operads' associahedron/`catalan_recursion_n`
(17/0); the level-0 unique horn filler = `dhom_unique_pointwise` (6/0). The Δ-complex simplicial *substrate* is
built (`SimplexBasis`/`Delta/Core` + `dsq_zero`), but no nerve/SimplicialSet bundle; the homotopy-coherent
inner-horn filler = the same Side-B colimit/q−1 break as homotopy_theory/knots. Buildable witness:
`unique_filler_iff_strict_truncation` (strict horns ⟺ nerve of a 1-category, the q+1/q−1 split).

### ★ Arithmetic dynamics (`arithmetic_dynamics.md`) — the canonical height as the q=±1 preperiodic detector

PREDICTION. Arithmetic dynamics = the iteration axis (golden/ergodic's self-applying orbit, `orbit_eq_iter`)
with the **canonical height ĥ = the q=±1 fixed-point/preperiodic detector made a size reading**, plus the q+1
bounded⟹finite corner for Northcott. ★ New datum: the height functional equation ĥ(fⁿP)=(deg f)ⁿ·ĥ(P) is
*structurally* `CassiniUnimodular.det_closed` (`det s n = qⁿ·det s 0`, 13/0) — the height is the orbit's Cassini
determinant read as a magnitude, with deg f in the multiplier slot. ĥ(P)=0 ⟺ preperiodic IS the q=±1 detector:
q+1 conserved/finite (`qpow_one`, `finite_order_divides_twelve`) ⟺ ĥ=0; q−1 escape (`golden_aperiodic`,
`height_diagonal_escapes`) ⟺ ĥ>0. Northcott = the q+1 finiteness corner (`heineBorel`/`gridMax_attained`), not a
separate theorem; the built height-cocycle is `minkowski_is_markov_valued_cocycle`. Named canonicalHeight/
preperiodic/Northcott/Julia objects absent; buildable witness: `multiplier_unit_magnitude_sign_order_NT`:188
(the preperiodic detector at the multiplier level).

### ★ Geometric group theory (`geometric_group_theory.md`) — the word object through a growth Lens

EXTEND (deep consolidation). GGT = the `FreeReduction` word object read through a **length/fold-height Lens**,
with the polynomial-vs-exponential growth dichotomy = the q=±1 spine and quasi-isometry = `Lens.refines`. The
Cayley graph/word metric = the FreeReduction normal-form (`free_group_quotient_no_quot` 26/0,
`freeEquiv_iff_reduce_eq`:216 the decidable word problem) with a word-length distance; growth = the count
reading graded by length. ★ New datum: Gromov's growth dichotomy (polynomial ⟺ virtually nilpotent) is the
*same q=±1 solvability spine the corpus already unified in one Lean object* (`Solvable.solvability_two_poles`
65/0), read through the growth Lens — polynomial/virtually-nilpotent = q+1 terminating derived series (ties
DerivedSeries), exponential/free = q−1 escape (growing iteration `MuNuMirror.ascent_unbounded`/rising trace
`golden_aperiodic`/perfect group `a5_not_solvable'`). Quasi-isometry = `Lens.refines` (reading-invariant).
Named CayleyGraph/wordMetric/growthRate/hyperbolicGroup/Gromov objects absent (the 228 Cayley hits are
Cayley–Dickson algebra, false-friend flagged); the general word problem = the Novikov–Boone Side-B colimit
break (recurs verbatim from free_corner). No new buildable witness (the collapse is already theorem-grade).

### ★★ Coalgebra / corecursion (`coalgebra.md`) — the dual of Raw.fold, ALREADY BUILT (the μ/ν closure)

EXTEND, with a major find overturning the predicted-not-built prior. Coalgebra = the calculus's `Raw.fold`
catamorphism **dualized** — the ν to the fold's μ. ★ The repo has **already built the dual ∅-axiom**:
`Theory/Raw/CoResidue.lean` (**140/0**) builds the final coalgebra `SlashNu`, the anamorphism `ana`:155
(`ana_unique`:315), and finality `slashNu_final`:726 — the literal dual of `raw_initial`/`dhom_unique_pointwise`,
proved by *finite-path induction* on the M-type path presentation (no coinduction primitive, closing what
MuNuMirror's docstring called the Mathlib-free-coinduction-blocked open piece). So the calculus's core fold (μ,
`raw_initial`) and its dual unfold (ν, `CoResidue`) are **both** built — it is closed under the μ/ν duality
(`MuNuMirror` the named mirror, 8/0). Streams = the coinductive modulus (`spineL_escapes`:462 the q−1 escaping
stream); bisimulation = `StateMachine.traceEq_iff_not_distinct`:262 (positive trace-eq, 21/0); coinduction = the
greatest fixed point (`KnasterTarski.gfp_greatest`:148, the dual of domain_theory's lfp); the co-fold ties hopf's
comultiplication (`CoAppend213`/`Convolution213`). Named Coalgebra/Bisimulation *structure bundles* absent
(apparatus is path-function emulation, not a typeclass record); buildable witness: weld `TraceEq = gfp Φ`.

### ★ Profinite groups / inverse limits (`profinite_groups.md`) — the resolution-tower limit, ALREADY BUILT (abelian)

PREDICTION + a BUILT surprise + a located boundary (LLPO). A profinite group = the resolution-tower inverse
limit = the modulus of finite approximations, on the Stone/ultrafilter boundary. ★ Grounded harder than padic/
iwasawa: the repo **already builds an abelian profinite inverse limit**. (1) The inverse-limit OBJECT = the
**meet of the finite-quotient Lens-family**, universal property = the meet's glb (`IndexedJoin.iProdLens`:97,
`iProdLens_is_greatest_pw`:168, 8/0; agreement `Lens/Instances/Cauchy.pointwise_limit_match`:124, 15/0). (2)
ℤ̂=lim ℤ/m is BUILT as a family-Cauchy limit (`ProfiniteSeq.factorial_seq_limit_all_zero`:131, 9/0 = the
profinite zero); ℤ₂=lim ℤ/2ᵏ quantitatively (`OdometerValue.bval_odo`:74, 16/0 = the +1 mod 2ᵏ profinite
successor); `GenericFamily` unifies profinite ↔ archimedean as two Lens-family choices. (3) The profinite=Stone
tie calibrates the **non-abelian/uncountable** boundary at LLPO (stone_duality, `comparability_imp_llpo`→
`llpo_of_realDichotomy`). Named ProfiniteGroup/inverseLimit/absoluteGalois/Krull objects absent (the non-abelian
group law on the limit, the Krull topology, the absolute-Galois tower = the located boundary); buildable
witness: a two-quotient thread `iProdLens {ℤ/2, ℤ/3}≅ℤ/6` as a worked finite-stage universal-property instance.

### ★ Synthetic differential geometry (`synthetic_differential_geometry.md`) — the derivative with ε²=0 (the Itô-dual)

PREDICTION + PARTIAL. SDG = derivative's difference-reading read as a value-derivative slot pair, with the
second-order residue **truncated to zero** (ε²=0) — the precise **dual of Itô**. ★ The three notes are one
reading at three positions of the resolution-axis *scaling* sub-parameter: smooth **drops** the O(h²) residue,
Itô **promotes** it (√h → ½f''dt), SDG **annihilates** it (ε²=0 → first-order-exact Kock–Lawvere). ★ Repo-first
surprise: the dual-number ring R[ε]/(ε²) IS genuinely BUILT (over 𝔽₂, the char-2 collapse of the
Cayley–Dickson tower) — `F2CDTower.eps_sq_is_zero`:86 (ε²=0), `has_zero_divisors`:105, `eps_has_no_inverse`:122
(17/0); the second-order residue it annihilates is `NewtonGregory.obstruction_int_constant`:404 (41/0); the
value-derivative slot pair = ℤ's difference pair (`npairToInt` 19/0). Named real-coefficient R[ε]/Kock–Lawvere/
tangentBundle M^D objects absent (M^D = lie_theory's open T_e G; the infinitesimal hits are cut-gaps/
ultrapowers, not nilpotent); buildable witness: the Real213 dual ring + Kock–Lawvere weld.

### ★ Distribution theory / generalized functions (`distribution_theory.md`) — "object = its readings" made the definition

PREDICTION + deep consolidation. A distribution T:φ↦⟨T,φ⟩ is the calculus's founding sentence ("object = its
readings", yoneda/motives) **made the definition** — `Lens.view` promoted to the primary object, faithful by
`object1_injective`:47, with singular distributions = the q−1 residue `object1_not_surjective`:61. The Dirac δ
(⟨δ,φ⟩=φ(0)) = the point-evaluation reading (`FlatOntology.Object1`:43 `r↦fun s=>decide(s=r)`, `Object1_self`).
★ The distributional derivative's minus sign is *derived*, not relabeled: ⟨T',φ⟩=−⟨T,φ'⟩ = the
integration-by-parts telescope (`gauss_conservation_telescope`:152, 8/0) + the q=±1 orientation/adjoint bit
(`dsq_zero_universal_delta4`/`leibniz_universal_delta4`). Fourier of tempered distributions = fourier's
character by duality; convolution = the weight axis (`mass_conv` 20/0). Named Distribution/TestFunction/Dirac/
tempered objects absent; buildable witness: `diracFunctional r := fun φ=>φ r`, represented by `Object1 r`
(`Object1_self` already gives the spike) — δ = the point-evaluation reading welded ∅-axiom.

### ★ Geometric measure theory (`geometric_measure_theory.md`) — currents = the de Rham dual

PREDICTION + PARTIAL (strong consolidation). GMT = the calculus's **de Rham dual**: a current T:ω↦⟨T,ω⟩ =
de_rham's forms read as the integration-against-forms pairing-functional ("object = its readings" on forms, the
motives/⟨C|L⟩ half — same reflexive theme as distribution_theory but on forms). ★ New datum: the **dualization**
— ∂T (defined by ⟨∂T,ω⟩=⟨T,dω⟩) is *forced* as the adjoint/transpose of d = homology's q=±1 boundary, with
∂²=0 dual to d²=0 (`dsq_zero_universal_delta4` 5/0; Stokes-by-duality = `gauss_conservation_telescope`:152 8/0,
whose functional is docstring-named a "current"). Mass = measure's weight (`measureNum`/`measure_union_additive`
9/0, `lebesgueStepNum` 9/0 = a current against a value-form); Hausdorff dimension = dimension's fold-height as a
scaling exponent (`Raw.depth_slash`/`isPart_wf`); non-integer dim_H / non-rectifiable = the q−1 height-escape
(`height_diagonal_escapes`); Plateau = the q+1 mass-minimizing zero-gap optimum (`ollivier_plan_optimal` 60/0).
Named Current/rectifiable/HausdorffMeasure/Plateau/varifold objects absent (the "current" hits are the physics
NoetherCurrent, false-friend); buildable witness: a dual current functional `boundaryCurrent T ω := T (delta ω)`
with `boundaryCurrent²=0` (dual to dsq_zero), mass-min via OllivierRicci's LP at cost=measureNum.

### ★ Quadratic forms / Witt ring (`quadratic_forms.md`) — the signature = the disc-sign trichotomy counted

EXTEND (deep consolidation). A quadratic form = `⟨symmetric Mat2/cup-pairing | L_sig⟩ ⊕ Residue(q=±1)`, L_sig =
"diagonalize, then count the q=±1 disc-sign per eigenvalue." ★ New datum: the **signature (p,n) IS the disc-sign
trichotomy counted over an eigenbasis** (positive λ = q+1, negative λ = q−1); the hyperbolic plane
`[[0,1],[1,0]]` IS the q+1⊕q−1 cancelling pair (the Witt-neutral, signature 0); definite/semidefinite/indefinite
= the same trichotomy as forms. ★ The repo has BUILT signature content (not just spectral): the cup-pairing on
H¹(T²) diagonalized to diag(2,−2) with explicit Sylvester invocation (`T2Minimal/Signature.signature_one_one_witness`:59
7/0), `KahlerGradeStructure.hodge_index_signature`:142 (5/0), `BalancedSignature.signature_balanced`:94
(`hirzebruch_zero` = Witt-trivial, 11/0), `EisensteinSignature.signature_dichotomy`:117 (golden indefinite vs
Eisenstein definite, 13/0). Witt ring = group-completion (`PairCompletionUniversal` 19/0) mod the hyperbolic;
Hasse–Minkowski = the local-global base-family (FP2Sqrt5 per-prime). Named QuadraticForm/WittRing/HasseMinkowski
objects absent; buildable witness: a binary-form `signatureOf (a,b,c)` reading sign(disc)+sign(a) into (p,n).

### ★ Lattices / theta functions (`lattices_theta.md`) — the count-by-norm packaged as a modular form

PREDICTION + PARTIAL. A lattice's theta series θ_Λ(τ)=Σ q^(|v|²/2) = the **count-by-norm reading packaged as
modular_forms' q+1 SL(2,ℤ)-invariant generating function**, with Poisson summation = fourier's Fourier
self-duality = the q=±1 τ↦−1/τ reflection, and even-unimodular Λ=Λ* = the q=±1 fixed point. ★ New datum: the
repo's **sums-of-squares corpus IS the theta-coefficient (count-by-norm) side**, ∅-axiom (modular_forms never
cited it): `FourSquare.four_sq_id`:122/`isSum4_mul` (multiplicative SoS count = θ_{Λ⊕Λ'}=θ_Λ·θ_Λ' = the ×↦·
character on the norm, 34/0), `Gram` (9/0 = the quadratic form), `LatticeArea.area2_unimodular`:148 (SL₂
preserves covolume = the modularity root, 18/0), `EisensteinRepresentation` (A₂ hexagonal, 27/0). Named Lattice/
thetaSeries/E8/Leech/Poisson objects absent (the geometric ℝⁿ lattice = the located break, twin of
modular_forms' automorphic break); buildable witness: θ_{Λ⊕Λ'}=convolution θ_Λ θ_Λ' on `CoeffSeq` at low degree.

### ★ Topos internal logic / Kripke–Joyal (`topos_internal_logic.md`) — Ω=Bool made forcing semantics

PREDICTION + PARTIAL. The internal logic of a topos = topos's Ω=Bool reading made the truth-value/forcing
*semantics*, same PURE/DIRTY=Heyting/Boolean line. New datum: **Kripke–Joyal forcing X⊩φ = read-at-a-stage/
resolution** (`IsResolutionShift`/`_compose` 17/0, the base/stage parameter; substitution = the naturality 2-cell
`view_factors_through_morphism`); the **internal (Mitchell–Bénabou) language = reading-through-the-Lens** (term =
Raw read by Lens.view; formula = `Type213`=Raw→Bool; higher type = `OnLens.universalMorphismLevelTwo`:242, 25/0);
**intuitionistic = PURE/Heyting q+1 (forcing decidable per stage), Boolean/LEM = DIRTY/propext q−1** — the same
line read on the forcing relation, with the DIRTY canonical Prop-connective maps (`SemanticAtom.canonicalAndMap`
etc.) the load-bearing evidence. Named Topos/KripkeJoyal/forcing(⊩)/subobjectClassifier objects absent (the
`forcing` hits are unrelated combinatorial (2,3)-atomicity forcing, flagged); buildable witness: a `Forces X φ`
relation at the Bool/q+1 corner, monotonicity from `IsResolutionShift_compose`, ∅-axiom without propext.

### ★ Max-flow / min-cut (`max_flow_min_cut.md`) — the first three-invariant fusion

EXTEND. Max-flow–min-cut = optimal_transport's Kantorovich LP duality read on a graph, where the primal
constraint is noether's **conserved current ∂·j=0** (`NoetherCurrent.continuity_eq`:97 14/0, not OT's marginals)
and the dual object is homology's **coboundary δ(𝟙_S)** (`Cohomology/Delta.delta`:54, not OT's Lipschitz
potential). ★ New datum: the first decomposition where LP duality + the conserved current + the boundary ∂ all
**fuse on one object** — max-flow≤min-cut = `kantorovich_weak_duality`:52, equality = `ollivier_plan_optimal`:106
(the q+1 zero-gap optimum, OllivierRicci 60/0); the cut = `GraphConnectivity` non-flat 0-cochain (8/0) on the
network adjacency (`bipAdj_connected` 20/0); Ford–Fulkerson augmenting = the matching-by-augment recursion
(`HallMarriage.hall_matching_two`:618 36/0, HallCond = the obstruction never hit). Named maxFlow/minCut/Menger/
FordFulkerson objects absent (the Menger hits are Cayley–Menger geometry, false-friend); buildable witness: a
tiny s→{a,b}→t network with flow instantiating continuity_eq, cut via delta(𝟙_S), maxFlow=minCut by ollivier_plan_optimal.

### ★ Characteristic classes / Chern–Weil (`characteristic_classes.md`) — the det-character OF the curvature

EXTEND (decisive consolidation). A characteristic class = the calculus's ×↦· **determinant-character OF the
curvature**, landed in cohomology. ★ New datum: the Chern classes c_i ARE the elementary-symmetric (Vieta)
functions e_i of the curvature spectrum — **generalizing the SYNTHESIS det/tr=e₁/e₂ finding from a single Mat2
to a bundle's curvature** (c₁=tr Ω=e₁, c₂=det Ω=e₂; `Mat2Spectrum.det_tr_split_is_e1_e2`:204 9/0,
`Mat2CayleyHamilton.cayley_hamilton`:37 = c(E)=det(I+Ω) char-poly). The Chern character ch(E)=tr exp(Ω) = the
×↦+ additive twin (`vp_mul`); the splitting principle = the spectral reading; naturality = the Lens-morphism
2-cell (`view_factors_through_morphism`); curvature input = `TensorCalculus.riemUp`/`riem_bianchi1` (23/0,
Bianchi = closedness); Gauss–Bonnet–Chern ∫e(TM)=χ = the built `DiscreteGaussBonnet` (12/0). Named Chern/
VectorBundle/Pontryagin objects absent (Chernoff = probability false-friend); buildable witness: Whitney
det(I+Ω_E⊕Ω_F)=det(I+Ω_E)·det(I+Ω_F) = `det2_mul` on block-diagonal curvature (already PURE).

### ★ Fusion / modular tensor categories (`fusion_categories.md`) — tqft's product, finite, with the Fourier S-matrix

EXTEND + PREDICTION + located BREAK. A fusion category = tqft's monoidal product (Invariant A) made **finite**
with a fusion-rule **count** (`GRA/Monoidal.product` 13/0, `product_NT_NT_grade`), the braiding/twist/dual the
**q=±1** residue (`productSwapIso_involutive` 23/0, `FoldKlein.bothSwap` 9/0, `QBinomial` deformation-q phase
11/0), the modular **S-matrix = fourier's character transform** diagonalizing the fusion ring
(`legendre_mul`/`quadratic_orthogonality` 20/0 / `root_orthogonality`/`cyclic_orthogonality_modp` 15/0),
**Verlinde = character-orthogonality inversion**, and the **quantum dimension = the Perron count** (φ for
Fibonacci anyons = `golden_hyperbolic`/`golden_is_converge`). The braiding-phase deformation-q vs tag-q is
containment-not-identity (inherited from quantum_groups). Named FusionCategory/Smatrix/Verlinde/anyon objects
absent (the braid hits are Coxeter physics, false-friend); the pentagon/hexagon/F-R-symbol coherence = the same
colimit/q−1 coherence break as tqft's cobordism. Buildable witnesses: `fibonacci_fusion_perron` (d_τ=φ via
golden), `verlinde_is_character_inversion` (Verlinde = inverse character transform at the abelian slice, ∅-axiom).

### ★ Higher / Milnor K-theory (`higher_k_theory.md`) — the ×↦· character climbing the degree

EXTEND (deep consolidation, the multiplicative dual of k_theory's additive K₀). K₁(R)=GL/[GL,GL] = the
abelianization = the det/×↦· character (the commutator-quotient kills the q−1 non-abelian part — `DerivedSeries`
`commSet`/`gcommP_transpositions_even`, `A5Perfect.a5_perfect` the extreme q−1 pole, 9/0). K₂/Steinberg {a,b} =
the q=±1 antisymmetric ({a,b}{b,a}=1, same swap as `bracket_antisymm`:76/`cup1_antisymmetric`:62) bimultiplicative
(×↦· in each slot) pairing. Milnor K^M = the ×↦· character tensored up, graded, mod the Steinberg cut. ★ The
Milnor conjecture / norm-residue = the deepest collapse: K^M/2 ≅ Galois cohomology (galois_cohomology) ≅ graded
Witt ring (quadratic_forms) are ONE graded object — a **three-note fusion** (det2_mul 130/0, legendre_mul,
psign_mulPerm_hom 11/0). Named K₁/K₂/Milnor/Steinberg objects absent (the Milnor hits are Milnor-exponent
dynamics, false-friend); buildable witness: `K1(S₃)=S₃/commSet≅C₂` (a decide/rfl corollary of derived_S3_step1).

### ★ Berkovich / rigid analytic geometry (`berkovich_geometry.md`) — a point = a multiplicative seminorm (a FIFTH boundary)

PREDICTION + a calibrated BREAK. A Berkovich point IS a multiplicative seminorm = the ×↦· character/valuation
made a point (`vp_mul` 7/0, `Zp.valEq_mul`:461 21/0); M(A) = the space of these readings ("object = its
readings", `object1_injective`); the Berkovich line's tree = the Stern–Brocot/mediant refinement
(`Mediant.mediant_strictly_between`:54 11/0, `manin_unimodular_decomposition`); contractibility = the tree being
a tree (q+1 no-loops, `reduced_betti_d4_contractible`/`chain_finite`). ★ M(A) completeness ("these are ALL the
seminorms") = the same LLPO/choice totalization as Stone's ultrafilter spectrum — a **fifth calibrated boundary
on the one ultrafilter/LLPO point** (twin of padic's open Ostrowski exhaustiveness); type-4 points need the
Real213 value-cut. Named Berkovich/seminorm/analytification objects absent; buildable witness: a
`seminorm_is_vp_character` bridge + `berkovich_line_tree_contractible` weld of built theorems.

### ★ Geometric invariant theory / GIT (`git_quotient.md`) — X//G = the Fix Lens, stability = q±1

PREDICTION (consolidation, fusing five corners on one G⤳X action). X//G = Spec(R^G) = galois_correspondence's
G-invariant **Fix Lens** (the ring of invariants = the `clo`-closed elements under the relabel-family,
`clo`:104/`clo_idempotent`:126 15/0, `galois_group_is_C4` a concrete Fix). ★ Stability = the q=±1 tag:
stable/closed-orbit = q+1 converge, unstable (orbit closure hits 0) = q−1 escape (`no_surjection_of_fixedpointfree`
the destabilizing direction); Hilbert–Mumford = the 1-parameter (resolution-axis) q±1 escape test. The moment
map / Kempf–Ness = the q+1 symplectic/convex optimum (`SignedCup.gram_hermitian_gravity_gauge_split`:127 14/0;
`ollivier_plan_optimal` 60/0, μ⁻¹(0) = the minimal-norm closed-orbit point). The categorical quotient = the
colimit corner, and **GIT stability IS the choice of the Side-A-good (separated, q+1) locus**
(`FreeReduction.free_group_quotient_no_quot` 26/0) — the new datum past the parent files. Named GIT/invariantRing/
momentMap/semistable objects absent; engines all PURE, the Kempf–Ness symplectic-quotient weld conceptual.

### ★ Gröbner bases / Buchberger (`grobner_bases.md`) — the colimit Side-A on polynomial ideals (the decidable corner)

EXTEND + PREDICTION. A Gröbner basis IS the calculus's confluent+terminating **Side-A rewriting normal form**
(`FreeReduction.free_group_quotient_no_quot` 26/0) applied to polynomial ideals: division = `freeReduce`/
reduction-fold; Buchberger = the **confluence completion** (S-polynomial = critical pair, criterion = "all
critical pairs join"); reduced GB = the Quot-free canonical representative (`proj_section`/`freeReduce_idempotent`);
ideal membership = the decidable word problem (`freeEquiv_iff_reduce_eq`:216); termination = the well-founded
monomial order (`Lambek.no_infinite_descent`:273/`isPart_wf`). ★ The spine: polynomial ideal membership IS
decidable = the **q=+1 confluent corner closed in full** — the decidable contrast to general groups' undecidable
Novikov–Boone Side-B (q−1). Named GrobnerBasis/Buchberger/Spolynomial objects absent; buildable witness: a
`Monomial:=List Nat` + well-founded monomialOrder (via isPart_wf) + reduceMod with order-drop (part_depth_succ_le)
and idempotence (mirroring freeReduce_idempotent) — the polynomial-ideal analogue of proj_val_eq_iff.

### ★ Index theory / Atiyah–Singer (`index_theory.md`) — the third "two readings of one object coincide"

EXTEND (decisive consolidation). ★ Atiyah–Singer is the corpus's **third and deepest "two readings of one
object coincide"** equality — after det/tr=e₁/e₂ (two Vieta readings of one spectrum) and Lefschetz
fixed-point=trace. The **analytic index** ind(D)=dim ker − dim coker = the q=±1 alternating residue count
(homological_algebra's ker/coker residue signed by the tag: ker=q+1 `converge_residue_fixed`, coker=q−1
`escape_residue_outside`; = McKean–Singer's Σ(−1)ⁱ = lefschetz_degree's L(id)=χ, `simplex_face_euler_zero` 10/0)
is shown EQUAL to the **topological index** ∫ch·Td (the ×↦·/×↦+ curvature character integrated,
characteristic_classes' `det_tr_split_is_e1_e2` 9/0). McKean–Singer's heat-kernel proof = that collapse made a
deformation (the resolution dial at t→0 vs t→∞). Gauss–Bonnet (ind(d+d*)=χ) = the built special case
(`DiscreteGaussBonnet` 12/0). The three neighbors are revealed as the analytic residue count, its trace-weighted
alternating form, and the topological character integral — Atiyah–Singer welds them. Named Fredholm/Atiyah/
McKean/Todd/RiemannRoch objects absent (the smooth elliptic D + ∫ch·Td = the Real213-cut break); buildable
witness: wire `multiplier .converge·dim ker + multiplier .escape·dim coker` to `eulerChar` as one decide lemma.

### ★ Markov chains (`markov_chains.md`) — the stationary distribution = the q+1 Perron eigenvector

EXTEND + PREDICTION. A Markov chain folds random_walks + martingales + ergodic_theory at one spectrally-pinned
q+1 fixed point. ★ New datum: the stationary distribution π = the q+1 converging fixed point = the **Perron
eigenvector**, the q+1 pole *made spectral* — the top eigenvalue pinned to the q+1 fixed VALUE 1 by
row-stochasticity (P·𝟙=𝟙); the spectral gap = the convergence MODULUS / mixing time; reversibility = the q±1
time-symmetry (real spectrum via `disc_symmetric_nonneg`); periodicity vs mixing = q−1 escape vs q+1 converge.
★ Strong find: the repo's discrete heat equation (`Analysis/ODE/HeatEq/Discrete.lean` 30/0) is a concrete
row-stochastic reversible walk — the lazy step (¼,½,¼) preserves the stationary constant (`lazyHeatStep_const`:214)
and **collapses the checkerboard period-2 / eigenvalue-(−1) mode to the constant in one step**
(`lazy_checker_collapses`:335), while the non-lazy step oscillates forever (`nonlazy_checker_hot`:324) — a
machine-checked aperiodicity/mixing (q−1→q+1) witness, the "make it lazy to mix" move as a theorem. Named
MarkovChain/stationary/Perron/mixing objects absent (the Real213/Markov tree is the Diophantine x²+y²+z²=3xyz,
not transitions); buildable witness: `markov2_perron` (2×2 doubly-stochastic, spec={1,1−2p} via Mat2Spectrum).

### ★ Additive combinatorics / sum-product (`additive_combinatorics.md`) — the ×↦·/×↦+ character incompatibility made combinatorial

EXTEND + PREDICTION. ★ The load-bearing new datum: the **sum-product phenomenon IS Invariant A's ×↦·/×↦+
character incompatibility made a combinatorial theorem**. The two doubling counts |A+A| and |A·A| are the two
readings of the *one* character arrow prime_factorization already proved non-collapsible (the wall
`two_three_unique`:158 8/0); sum-product is that non-trade read at finite cardinality — the one set can't be
tight for both because being a +-subgroup and a ·-subgroup at once is the field/trivial case the wall forbids
(`vp_mul`/`vp_separation` ×↦+, `det2_mul`/`legendre_mul` ×↦·). Freiman = the ×↦+ structured-sets normal form
(AP/GAP = the additive twin of unique factorization); Plünnecke–Ruzsa = ×↦· on the doubling (`mass_conv`
convolution multiplicativity 20/0); Szemerédi = Ramsey q+1 density-unavoidability on the additive sub-family
(`ramsey_lower`:174 13/0 — the cell ramsey_theory flagged absent); Cauchy–Davenport = the additive saturation
twin of `sperner_theorem`:534 (50/0). Named sumset/Freiman/Plünnecke/Szemerédi objects absent (the only AP hit
is the Lambert-poly coefficient list, false-friend); predicted-buildable on existing infra.

### ★ Noncommutative geometry / spectral triples (`noncommutative_geometry.md`) — geometry = its spectral readings

EXTEND (decisive). NCG = "geometry = its spectral readings" — operator_algebras' Gelfand ("the commutative
algebra IS its characters/spectrum") **pushed past commutativity** (`markovGen_noncommutative`:2433 a built
witness that mul is noncommutative; `det2_mul`/`legendre_mul` = the Gelfand ×↦· character). ★ New datum: the
Dirac operator D = the resolution/metric reading, and the distance formula d(p,q)=sup{|f(p)−f(q)|:‖[D,f]‖≤1}
reads the metric **off the q−1 commutator [D,f]** — the same antisymmetric bracket as `Mat2Bracket.bracket_antisymm`
(10/0), which is a derivation (`bracket_leibniz`:135, so [D,f]=df, ‖[D,f]‖≤1 = unit gradient). So the NC metric =
the q=±1 bracket + the resolution dial (`IsResolutionShift_compose`). Cyclic cohomology = the NC de Rham residue
(`dsq_zero_universal_delta4`); the local index formula = index_theory's analytic=topological collapse in the NC
setting; NC tori = the deformation-q (`qbinom`, the *other* q, q=1 = commutative limit). Named SpectralTriple/
Dirac/Connes/cyclicCohomology objects absent (the Hilbert-space/C*-norm completion = the Real213 break, shared
with operator_algebras); buildable witness: a d=2 discrete commutator-metric toy (traceless symmetric D, [D,M]
via bracket, two characters χᵢ(M)=Mᵢᵢ, a finite Connes distance).

### ★★ Homotopy type theory / univalence (`homotopy_type_theory.md`) — univalence is the calculus's proven faithfulness

EXTEND + PREDICTION. ★ The striking new datum: **univalence-the-axiom (A≃B)≃(A=B) IS the calculus's PROVEN
faithfulness** `object1_injective`/`lensIso_iff_kernel_eq` — where HoTT must *posit* univalence (independent of
MLTT, needing the simplicial model), the calculus *derives* the same "equivalent-under-all-readings ⟹ equal"
content as an ∅-axiom theorem (`object1_injective` 8/0, proof uses `of_decide_eq_true` avoiding propext;
`lensIso_iff_kernel_eq` Unified 14/0). The calculus already HAS univalence — it is the type-theoretic face of
the whole reflexive "object = its readings" framework. Honest caveat: at the 1-categorical/setoid altitude
(kernel coincidence), not higher-coherent propositional univalence (the propext/funext ceiling). The rest:
Id_A(x,y) = the refinement/equality reading (equivalence's one Lens-arrow as paths); refl/·/⁻¹ = the `LensIso`
groupoid; types-as-∞-groupoids = infinity_categories' cell-dimension tower; transport = the Lens 2-cell
`view_factors_through_morphism`; path-induction J = refl + `dhom_unique_pointwise` initiality; the truncation
hierarchy = the fold-height with its (-1)-floor = the PURE Bool/decide propext corner; HITs = the Quot-free
`LensImage`/`FreeReduction` quotient-with-paths. Named univalence/IdentityType/HIT objects absent (GRA/HoTT.lean
is the numerical (2,3)-grade false-friend, flagged); buildable witness: `univalence_setoid` wiring
lensIso_iff_kernel_eq to object1_injective ("(A≃B)⟺(Id_A=Id_B)" at the 1-categorical altitude).

### ★ O-minimality / stability theory (`ominimality_stability.md`) — the q±1 tame/wild dividing line

PREDICTION. Model-theoretic tameness = the calculus's **q=±1 dividing line read on definable-set counts**
(extends model_theory one layer up, from sentences to definable sets): o-minimality / cell decomposition = the
**q+1 finite-cell terminating normal form** (the count bottoms out; cell decomposition = the fold-to-normal-form,
`Lambek.no_infinite_descent`:273/`isPart_wf`); stability = q+1 bounded type-count vs the **order property = the
q−1 escaping diagonal** (the same diagonal as cardinality/godel, `object1_not_surjective`:61/
`no_surjection_of_fixedpointfree`:51, and a Ramsey-type *unavoidable* order tying `erdos_szekeres`:587 29/0);
Morley rank = the fold-height on types (`MuNuMirror.ascent_unbounded`); Shelah hierarchy = the stratified q−1
escape. Named oMinimal/stable/Morley/NIP objects absent (the stability hits are Ricci-flow numerical
false-friends); buildable witness: a toy OrderProperty/Stable predicate on a finite Lens-family wired to
object1_not_surjective + residue_tag_two_poles.

### ★ Perverse sheaves / intersection cohomology (`perverse_sheaves.md`) — the residue machine re-truncated

EXTEND + PREDICTION + PARTIAL-BREAK. Perverse sheaves = derived_categories' residue machine **re-truncated** by
a perverse t-structure (a fold-height re-grading = a different reading of the SAME resolution axis
`IsResolutionShift` 17/0). ★ IC = j!* the intermediate extension = the **q+1 self-dual canonical fixed point**
(`FenchelMoreau.closed_iff_fixed`:152 18/0 + the involution `multiplier_unimodular`); the **Decomposition
Theorem** (proper pushforward = ⊕ shifted IC) = the residue's **semisimple q+1 splitting** into IC summands
(`reduced_betti_d4_contractible` + `converge_residue_fixed` = the spectral-degeneration / Ext¹=0 case, vs the
q−1 non-split `loopClass_not_coboundary` 56/0); Verdier/Poincaré duality = the q=±1 reflection (`bracket_antisymm`,
𝔻²=id = `multiplier_unimodular`). Named Perverse/IC/tStructure/Verdier objects absent (the Verdier hits are the
ScalingOrbit spiral false-friend); located break = the stratified-space/constructible ambient + the
calculus-of-fractions Side-B (same as sheaf_theory/derived_categories).

### ★ Tropical geometry (`tropical_geometry.md`) — the ×↦+ valuation made a degeneration

PREDICTION + PARTIAL. Tropical geometry = the calculus's ×↦+ valuation reading made a degeneration (extends
tropical's (max,+) semiring + toric's Newton polytope). New data: (1) **tropicalization = the valuation image
of a whole VARIETY** (trop(V)=val(V)) — toric's "Newton polytope = valuation image on monomials" extended past
monomials to the solution set; the tropical variety = the q+1 combinatorial skeleton (`vp_mul`:165 10/0,
`vp_separation` faithful, `max_idem` 17/0); (2) ★ **the balancing condition Σ w_e·u_e=0 = a conservation law
∂·j=0 at each vertex** = *the same* `NoetherCurrent.continuity_eq`:97 (14/0) that max-flow identified as flow
conservation — the sharpest new tie; (3) the fundamental theorem = the valuation reading commutes
(`view_factors_through_morphism`); tropical Bézout = the count (`countTrue_append`). Named TropicalVariety/
tropicalize/balanced(geometric) objects absent (false-friends: rBalanced/BalancedSignature); buildable witness:
`tropV` as the per-axis vp-vector image + a `balanced` field proved equal to continuity_eq's ∂·j=0.

### ★ Cluster algebras (`cluster_algebras.md`) — the Markov mutation structure, ALREADY BUILT

EXTEND (consolidation — the calculus recognizes its own built object as a cluster algebra). ★ The load-bearing
instance — the **rank-3 Markov cluster algebra — is already built and PURE** (`SternBrocotMarkov` 130/0, the
largest tally in the corpus): the exchange relation/mutation is a machine-checked theorem `markov_vieta_int`:265
(the Vieta jump (x,y,z)↦(x,z,3xz−y) preserving x²+y²+z²=3xyz), with `markoff_vieta`:169 the SL₂ form and
`mInterval_markov` the tree generating Markov triples. Mutation μ²=id = the q=±1 involution
(`bothSwap_involutive`/`multiplier_unimodular`); the exchange matrix = the q−1 antisymmetric det-1 SL₂ form
(`det2_mul`/`bracket_antisymm`); the Laurent phenomenon = a q+1 no-residue normal-form analogue
(`FreeReduction.proj_val_eq_iff` + integer positivity `markovNum_pos`); finite-type/Dynkin = q+1 finite-order
orbit (`finite_order_divides_twelve` 29/0) vs infinite-type = q−1 escape (`golden_aperiodic`,
`markovNum_children_ne`:2702); the Stern–Brocot mediant tree = the seed graph (`Mediant`/`manin_unimodular_decomposition`).
Named ClusterAlgebra/mutation/Laurent objects absent (the mutation hits are code comments); the exchange
relation is the rank-3 Markov instance, not a general B-parametrized one. Buildable witness already PURE:
`markov_vieta_int` (the cluster mutation as a machine-checked theorem).

### ★ Khovanov homology / categorification (`khovanov_homology.md`) — the residue on knots' resolution cube

PREDICTION + PARTIAL. Khovanov homology = the residue-taking operation applied to knots' resolution cube: the
cube of resolutions = the {0,1}ⁿ bit-cube (game_theory's `BoolXORFold` hypercube, `psiNatPos_linear` 6/0); the
chain complex / δ²=0 / ker δ/im δ = homological_algebra's residue machine, now bigraded (two fold-heights,
`dsq_zero_universal_delta4`, `BettiKernel` 11/0). ★ New datum: **the graded Euler characteristic = the Jones
polynomial** = the corpus's decategorify=q±1-alternating-count pattern (the same Σ(−1)ⁱ as
`simplex_face_euler_zero`/McKean–Singer); the residue strictly DOMINATES the count (carries the q−1 obstruction
the alternating cancellation erases) — `NonzeroBetti` (56/0) the concrete ∅-axiom model "categorification
detects what decategorification cancels" (nonzero H¹: cycle=escape vs contractible=converge). Lee/s = the
deformation dial; functoriality = the 2-cell. Named Khovanov/Jones/Kauffman/Frobenius objects absent; the break
is INHERITED from knots (the isotopy/Reidemeister-invariance Side B), not new.

### ★ Conformal field theory / VOAs (`conformal_field_theory.md`) — fusion + modular + the centrally-extended bracket

EXTEND + PREDICTION + located BREAK. 2d CFT = lie_theory's Aut-family read three ways: the centrally-extended
q±1 bracket (Virasoro = Witt + a central term, `Mat2Bracket.bracket_antisymm` 10/0), the fusion product (OPE =
fusion_categories/hopf convolution, `Convolution213` 49/0), and the SL(2,ℤ)-invariant character (partition
function = a modular form, `ModularElliptic.modular_generator_orders`:58 7/0, `manin_unimodular_decomposition`).
★ New datum: the central charge c = the conformal anomaly = the **unique q±1 2-cocycle = galois_cohomology's H²
obstruction class** on the Witt algebra (`MinkowskiCocycle` 6/0 the cocycle, `OmegaH2Trace.omega_h2_trace_master`:113
7/0 the unique nontrivial 2-cocycle b₂=1) — c=0 the q+1 exact pole, c≠0 the q−1 anomaly residue, the same
Theorem-90-vs-Brauer pattern as galois_cohomology. Named Virasoro/CFT/OPE/centralCharge objects absent (the
conformal hits are differential-geometry curvature, false-friend); located break = the bootstrap crossing
equation (the graded-relation slot) + the infinite-mode Virasoro tower vs finite Mat2 (inherited from lie_theory).

### ★ Gauge theory / Yang–Mills (`gauge_theory.md`) — curvature + Chern character, instantons = Hodge q±1

EXTEND. Yang–Mills = curvature's loop-residue (connection/holonomy `HolonomyLattice` 26/0) + noether's
Aut-invariant det character (gauge invariance) + de_rham's d²=0 (Bianchi) + characteristic_classes' Chern
character (∫tr(F∧F)=c₂=`det=e₂`). ★ New datum: **instantons (F=±⋆F) = the q±1 eigenspaces of the Hodge star
involution** (`SignedHodgeStar.star_sq_pos_one_grade2`:98 ⋆²=+1 at grade 2 = the curvature-2-form seat on a
4-manifold ⟹ F=F⁺⊕F⁻, the same q±1 split as symmetric/antisymmetric, 12/0); the gauge field = the antisymmetric/
q−1 cup half of `gram_hermitian_gravity_gauge_split` (gravity=symmetric metric, gauge=cup). ★★ The surprise: the
YM **mass gap is already BUILT ∅-axiom** — `YangMills/Gap.mass_gap_master`:168 (24/0: exact spectrum {0,4,4,6,10},
unique vacuum, gap = c·min(NS,NT) = 4>0, eigenbasis-independent), and the spectral confinement face
`ColoredGap.colored_confinement_master` (4/0) — far stronger than a prediction. Named connection/instanton/
WilsonLoop objects absent (Wilson = Wilson's theorem number-theory false-friend); the Wilson-loop area law is
the honest open wall (no embedding on abstract K_{3,2}); smooth G-bundle/instanton moduli = the Real213 break.

### ★ Floer homology (`floer_homology.md`) — Morse's residue machine on an ∞-dim functional

PREDICTION + the deepest homology-cluster consolidation. Floer homology = morse_theory's residue machine lifted
verbatim to an infinite-dimensional functional (the symplectic action / Chern–Simons), fused with symplectic's
q+1 conserved-orbit sector. Every leg is a prior ∅-axiom theorem reused: CZ/Maslov index = Morse index =
`Raw.depth` (relative-not-absolute, absorbed by the finite-signature rule); ∂𝒜²=0 = `dsq_zero`; HF≅singular =
the two-readings-one-residue; Arnold conjecture = HF≅singular + the Morse weak inequality c_i≥b_i; critical
points = periodic orbits / flat connections = symplectic's conserved sector (`GradientFlow.gradient_descent_monotone`
9/0, `MonovariantFlow.flow_reaches` 19/0). ★ New datum: the first field where the Morse + symplectic
consolidations meet on one ∞-dim object. Located break: the ∞-dim moduli ℳ(x,y) of J-holomorphic curves/ASD
instantons (Banach/Fredholm = the Real213-cut corner); the finite count #ℳ is the operand, the moduli
reached-by-none. Named Floer/Arnold/Maslov/JHolomorphic objects absent.

### ★ Persistent homology / TDA (`persistent_homology.md`) — the homology residue across the resolution axis

PREDICTION + PARTIAL. Persistent homology = the homology residue ker∂/im∂ read as a **function of the resolution
axis** (the filtration = `IsResolutionShift`, the inclusion maps = the shift, grades add `IsResolutionShift_compose`
17/0). The barcode = each residue-class's lifetime-modulus (long bars = q+1 stable features, short = q−1 noise);
the structure theorem = the residue splitting into interval modules (semisimple over the resolution line); stability
= the q+1 continuity in scale (`ContinuityOpenSet` 11/0). ★ New datum: where spectral_sequences iterates the
residue on its OWN output (page recursion), persistent homology reads the SAME residue across an **external scale
parameter** — two distinct uses of the resolution dial on the homology residue, both q±1-tagged; and the modulus
becomes a **per-class** object (the barcode), not one global bracket. Named persistence/barcode/filtration
objects absent; buildable witness: a two-step filtration (hollow triangle b₁=1 ⊂ filled Δ² b₁=0 = one q−1 short
bar [1,2)), both endpoints' Betti data already PURE (NonzeroBetti 56/0, BettiKernel 11/0).

### ★★ Symmetric functions / λ-rings (`symmetric_functions.md`) — Λ = the universal home of the `eᵢ`

EXTEND (consolidating capstone). The ring of symmetric functions Λ is the **universal home of the elementary-symmetric
`eᵢ`** the corpus keeps independently rediscovering: `det/tr = e₁/e₂` of a 2×2 spectrum (`Mat2Spectrum.det_tr_split_is_e1_e2`
9/0), the 3-var `e₁=a+b+c, e₂=ab+bc+ca, e₃=abc` named in `NewtonInequalities` with Newton's log-concavity inequalities
proved ∅-axiom (`newton1`/`newton2` 5/0), Chern `cᵢ=eᵢ` (curvature), signature/discriminant. The `eᵢ` = the coefficients of
`∏(1+xⱼt)` = the ×↦· character's coefficient ring (universal `det`/char-poly). Newton's identities = the ×↦·↔×↦+ character
bridge (`eᵢ` det-reading ↔ `p_k` trace-power additive twin). Schur `s_λ` = `representation.md`'s `d>1` trace-character on the
`q=±1` alternant ratio; Hopf structure = `hopf_algebras.md`'s built `conv`/Δ/antipode (20/0). New datum: Λ is the field that
NAMES the scattered `eᵢ` as ONE universal object. ABSENT (grep-confirmed): named Λ, the `e/h/p/m/s_λ` bases, Jacobi–Trudi, the
alternant `∏(xᵢ−xⱼ)` (Schur denominator), λ-ring — the same `d>1`-character break `representation.md` located. Flagged name-collisions
NOT cited: `Combinatorics/PowerSums` (Faulhaber, not `p_k`), `Combinatorics/Vandermonde` (binomial convolution, not the alternant),
`Foundations/SchurInequality` (Schur's *inequality*, not Schur *functions*). **Newton's identities already built for the 2-element
spectrum at ALL degrees:** `Mat2TraceRecurrence.trace_recurrence` (6/0) = `p_{n+2} = e₁p_{n+1} − e₂p_n` (trace powers `p_k=tr(Mᵏ)`,
`e₁=tr`, `e₂=det`, Cayley–Hamilton iterated), plus the explicit base case `trace_sq : tr(M²) = tr² − 2·det`. **Witness BUILT this session
(3-variable degrees):** `newton_id_p2 : p₂ = e₁p₁ − 2e₂`, `newton_id_p3 : p₃ = e₁p₂ − e₂p₁ + 3e₃`, `newton_id_p4 : p₄ = e₁p₃ − e₂p₂ + e₃p₁`,
each one `ring_intZ` lemma in `NewtonInequalities`, `#print axioms`-clean — module 5/0 → **8/0** (and `Mat2TraceRecurrence` 5/0 → **6/0**).

### ★ Optimal control / Bellman (`optimal_control.md`) — the value function = the q+1 Bellman-contraction fixed point

EXTEND (consolidation) + PREDICTION. No new primitive. The Bellman operator `T[V]=min_u[c+γ·V∘f]` is a `BanachFixedPoint.Contraction`
(discount `γ` = the modulus), `V` = its q+1 converging fixed point (the SAME engine as φ/Gaussian/ODE/stationary-π,
`converge_residue_fixed` 55/0, `banach_fixed_point`/`banach_unique` 12/0), value iteration = the Picard orbit (`orbit_eq_iter` 1/0,
`PicardIterate` 8/0), the principle of optimality = the recursive fold self-reference, HJB = the Bellman equation at residue
resolution (`IsResolutionShift`), Pontryagin = the conserved Hamiltonian character (`NoetherCurrent` `noether_local`/`density_conserved_of_det_one`
14/0; `det_holonomy_eq_one` 26/0), the optimal-transport leg via `OllivierRicci.kantorovich_weak_duality`/`ollivier_plan_optimal` 60/0.
A weld of the Banach-engine family with the Noether family that no single neighbour carries. ABSENT (grep-confirmed, zero hits):
`Bellman`, `valueFunction`, `dynamic_programming`, `HJB`, `Pontryagin`, `value_iteration`, `policy_iteration`, `costate`. Buildable
witness: a discrete-state Bellman operator on a finite value vector shown to be a `Contraction` with modulus `γ`, then
`banach_fixed_point`+`banach_unique` ⇒ `value_iteration_converges` (the fifth Banach-engine instantiation after φ/Gaussian/ODE/Markov-π).

### ★ Quantum information (`quantum_information.md`) — no-cloning = the q−1 diagonal, ⊗ = the monoidal grade

EXTEND + PREDICTION (consolidation), no break. No new construction — consolidates the tensor `⊗` (monoidal/Hopf,
`GRA/Monoidal.product`/`product_NT_NT_grade` 13/0, grade adds), the q−1 diagonal (no-cloning = a forbidden point-surjection, the SAME
Cantor/Lawvere obstruction `no_surjection_of_fixedpointfree`/`cantor_via_lawvere` 11/0 as cardinality/Gödel/measure;
`object1_not_surjective` 7/0), the ±1 parity (Bell/CHSH `chsh_bound_value : chsh_bound = 12` 5/0), the ×↦+ character
(von Neumann entropy = additivity, `Entropy.entropy_additive`/`surprise_additive` 14/0), the qubit atomic count (`Qubit` `NT=2` 4/0),
and the unimodular tag (`multiplier_unimodular`/`residue_tag_two_poles` 55/0; `det_holonomy_eq_one` 26/0). New datum (re-skin guard
passes): no-cloning = the q−1 no-surjection; entanglement = the ⊗-reading's non-factorizability residue (same residue as prime
non-factoring) — not a re-description of `quantum_mechanics.md` (operator algebra). ABSENT (grep-confirmed): named `noCloning`,
`entanglement`/Schmidt, `densityMatrix`, `vonNeumannEntropy`, `teleportation`; the Tsirelson `2√2` is a `Real213`-cut distinct from
the built atomic integer 12; the complex Hilbert amplitude `|·|²` ABSENT (inherited from `quantum_mechanics.md`). Witness caveat: the Cantor
diagonal at `Qubit := Bool` is buildable but is a *no-universal-realizer* fact (= Cantor), NOT no-cloning —
basis states ARE clonable (CNOT `U(b,0)=(b,b)`); genuine no-cloning needs the amplitude residue and stays predicted-not-built.

### ★★ Prime distribution (`prime_distribution.md`) — the dual of prime factorization; Bertrand = the q=+1 residue bound

EXTEND + RESIDUE-SURFACING (the genuinely-213 re-read of the Bertrand build). Where `prime_factorization.md`
reads a *number* via `L_vp` (residue NONE = unique factorization), this reads the **basis** `L_vp` presupposes:
the ×-atoms (primes) as **positions on the +-line**. The ×-construction fixes *which* numbers are atoms (a
×-fact) but says nothing about *where* they land (a +-fact) — that mismatch is the **residue** (the prime-gap
structure), genuinely non-trivial and never-terminating (`exists_prime_gt:689`). Residue carries the `q=±1` tag:
**Bertrand** = "a prime always in `(n,2n]`" = the gap bounded by a factor 2 = the `q=+1` converge side
(`golden_is_converge:180` analogue); arbitrary gaps (`n!+2..n!+n` composite) = the `q=−1` escape side
(`escape_residue_outside:133`). Erdős's proof = the character arrow `×↦+` (`vp_mul:165`) turned into a residue
constraint: read `C(2n,n)` via the ×-count-Lens (`central_binom_factorization`, an instance of
`prod_prime_pow_eq`), bound it (`central_binom_upper_bound` `≤ 4^{2n/3}·(2n)^{√(2n)}`), collide with its +-size
(`four_pow_le_succ_mul_central_binom:507`) ⟹ the gap bound (`exists_prime_in_window`). This re-reads the entire
vp/Bertrand Lean layer (PrimePowFactorization 10/0, CentralBinomFactorization 8/0, this session) **not as a
formalization of Erdős but as the surfacing of the `L_vp`-residue** — the dual half of `prime_factorization.md`.
Collapse: "multiplicative vs additive number theory" = `⟨C|L_vp⟩` vs its residue, one object. ABSENT: the crossover
asymptotic + finite chain (pure-Nat, frontier `bertrand_postulate.md`), the `q=−1` arbitrary-gap theorem, PNT
(`π(x)∼x/ln x`, a `Real213`-limit = the residue's fine pointing).

### ★★ Modular arithmetic (`modular_arithmetic.md`) — the residue Lens = 213's count-Lens, named; the q=±1 tag's origin

EXTEND + SELF-PORTRAIT. The operation classical math calls "reduction mod m" IS 213's count-Lens (§6): C = ℕ
under count, L_m = `n ↦ n%m` (the prototype count-Lens), Residue = the dropped quotient `⌊n/m⌋`. Reconstruction
= `div_add_mod_pure` (`n = m·(n/m) + n%m`, NatDiv213:126) = `⟨C|L⟩ ⊕ Residue` as an arithmetic identity. **Name
disambiguation (the new datum):** classical "residue" (remainder) = the Lens *image* (kept); 213 Residue =
the quotient (dropped) — opposite halves of one division. **CRT** = the coprime residue-Lens *family* is jointly
faithful (`crt_unique` CRTReconstruction 12/0) — the count-Lens analogue of `vp_separation`. **The q=±1 tag's
origin:** the Legendre symbol `(a/p)∈{±1}` IS the residue tag on `(ℤ/p)*` — `a` a quadratic *residue* (q=+1,
square) or not (q=−1); `euler_dichotomy` (EulerCriterion 2/0) = the dichotomy, `legendre_mul` (5/0) = the tag is
multiplicative (`×↦·` into {±1}), `multiplier_unimodular:86`/`residue_tag_two_poles:228` (ResidueTag 55/0) = the
abstract tag (q²=1, two poles) it instantiates. So the q=±1 spine the whole corpus runs on has its NAME and first
instance here — quadratic residues. Also Wilson (50/0), Euler. Collapse: "the residue" (remainder) and "the
Residue" (213) = Lens image vs dropped quotient, one division. ABSENT: Dirichlet (residue-class distribution,
sibling of `prime_distribution.md`), general `(ℤ/m)*` cyclicity, higher-power residue symbols (q^k=1).

### ★★ gcd / Euclidean algorithm (`gcd_euclidean.md`) — the residue Lens iterated to its q=+1 fixed point

EXTEND (the residue-Lens triptych's keystone). C = a pair of counts (a,b); L = the Euclidean step
(a,b)↦(b, a%b) = the residue Lens (`modular_arithmetic.md`) fed back + swap — verbatim `gcdFuel` (NatHelper:618,
`gcdFuel n (b%(a+1)) (a+1)`); the **q=+1 fixed point** (residue hits 0) is gcd, dropped part = the coprime
cofactors a/g,b/g. **Dynamic = static, one object**: gcd computed as the terminating fixed point (well-founded
modulus `M(a,b)=max a b + a` strictly decreases, fuel `2(a+b)+1`, total ∅-axiom) IS the **divisibility-lattice
meet** (`gcd213_greatest` Gcd213 33/0: GLB universal property), and **that lattice = the count-Lens refinement
lattice** (`leavesModNat_lcm` LensLcmMeet 4/0: refines=∣, meet=lcm; CRT = coprime case). **Forcing**: gcd
(terminate, q=+1) and prime distribution (`exists_prime_gt`, never-terminate, q=−1) are the **two faces of
iterating the residue Lens** — the descent modulus forces q=+1; its absence (no top atom) is the q=−1 prime
side. Completes the triptych `modular_arithmetic` (the Lens) → `gcd_euclidean` (terminating iteration) →
`prime_distribution` (non-terminating iteration). ABSENT: packaged Bézout `gcd=ax−by` identity; the CF bridge
(Euclidean quotients = continued fraction of a/b, `continued_fractions.md`).

### ★★ Computability / halting (`computability_halting.md`) — the q=±1 termination tag's residue IS the diagonal

EXTEND (unifies the two corpus spines). The meeting point of the **iterated residue-Lens engine** (SYNTHESIS §2
(iii): q=±1 = does the descent terminate?) and the **one diagonal** (cardinality/godel). C = programs as Raws,
Gödel-coded (`Raw.toNat_injective` Godel:118); L_halt = the termination reading a↦(x↦halts?(a,x)) = a self-cover
`f:A→(A→Bool)` (same shape as count/provability, feature = "halts"); Residue = the diagonal: no total
halt-decider (`no_surjection_of_fixedpointfree` OneDiagonal 11/0 at B=Bool, `object1_not_surjective` 7/0, the
q=−1 escape pole). **Decidability of the q=±1 termination tag is GRADED by the well-founded modulus**: gcd (modulus
`M=max a b+a` exists → decidable & always +1, `gcdFuel` total) → Collatz (no known modulus → open) → halting
(no modulus → undecidable = the diagonal). The modulus is the boundary between a *readable* q and the *diagonal*
q. **Collapse**: Cantor/Gödel/Turing = count-Lens/provability-Lens/termination-Lens of ONE residue
(`one_diagonal_generates`:101). **Forcing**: the dynamic q=±1 tag (finding iii) and the one-diagonal are one
object — deciding the termination tag of an arbitrary descent IS the self-cover whose residue is the diagonal;
static face = Legendre `(a/p)` (finding i), dynamic face = Euclidean termination (iii), meta face = its
undecidability (the diagonal). ABSENT: named TuringMachine/halts/Collatz + the packaged undecidability statement
(only the abstract diagonal built, as in godel.md).

### ★★ Cayley–Dickson tower (`cayley_dickson.md`) — iterated doubling; residue = the law lost each step; BOTH invariants

EXTEND (the cleanest place both invariants are load-bearing in one object). C = iterated doubling α↦CDDouble α
(CDDouble:44, dim 1,2,4,8,16…) — ℝ/ℂ/ℍ/𝕆 are ONE construction at four depths, not four objects. L = conjugation
`conj` (CDDouble:63), the **q=±1 involution** (fixed=reals q=+1/trace; anti-fixed=imaginaries q=−1, doubling each
step), defining the norm N(x)=x·x̄. Residue = the law LOST per doubling: order (ℝ→ℂ) → commutativity (ℂ→ℍ) →
associativity (ℍ→𝕆) → alternativity+composition (𝕆→𝕊, zero divisors). **What survives = the q=+1 kept laws,
proved ∅-axiom**: alternativity/flexibility through 𝕆 (`cd_alt_left`:26/`cd_alt_right`:111/`cd_flexible`:131,
CDDoubleAlternative 3/0) + **the multiplicative norm character N(xy)=N(x)N(y)** (`diag_collapse`:80,
`hurwitz_cross`:119, CDDoubleMoufang 23/0) = **Invariant A (×↦·) on norms**. **Hurwitz** (normed division algebras
only dim 1,2,4,8) = the q-tagged TERMINATION: the ×↦· norm character survives 4 doublings (q=+1, depths 0–3) then
breaks (q=−1, 𝕊). Collapse: four number systems = one ⟨double|conj⟩, the differences = the residues (lost laws).
Forcing: BOTH invariants meet — conj (q=±1, drives doubling) + norm (×↦·, preserved only to depth 3). ABSENT:
named terminus (𝕊 zero divisors / norm fails at depth 4) + packaged Hurwitz statement (survivors built, terminus
predicted-not-built).

### ★★ Frobenius endomorphism `x↦xᵖ` (`frobenius_endomorphism.md`) — where the character arrow COLLAPSES

EXTEND (Invariant A's collapse point; sharpens finding (iv)). C = the p-power x↦xᵖ; L = reduction mod p
(characteristic). **The content = the collapse**: in char p, x↦xᵖ is a RING ENDOMORPHISM — multiplicative always
`(xy)ᵖ=xᵖyᵖ`, AND additive `(x+y)ᵖ≡xᵖ+yᵖ` (the **freshman's dream**, every middle binomial ≡0 mod p,
`freshman_binom` LucasTheorem 18/0). So Frobenius is the **unique coincidence of A's two arrows**: ×↦· and +↦+ are
the *same self-map* `(·)ᵖ`. Where `prime_factorization` collapsed × and + into one construction at two resolutions
(vp_mul ×↦+), Frobenius is sharper — at char p the separating resolution *vanishes* and one map IS both
operations. **Residue = the fixed set**: Fermat's little (`fermat` MulOrder 13/0, `a^(p−1)%p=1`; equiv aᵖ≡a)
fixes exactly 𝔽_p (q=+1 core); the moved part = the proper extension 𝔽_{pⁿ}∖𝔽_p (q=−1), Frobenius generating
Gal(𝔽_{pⁿ}/𝔽_p) (order n, `ord_dvd_p_sub_one`:181). Sharpens finding (iv): where A is a full endomorphism, B's
fixed pole = the fixed field. **False-friend flagged**: `Frobenius.lean` = the Frobenius *number* (coin problem),
NOT this endomorphism (CLAUDE.md row). ABSENT: named ring-endo `frobenius`, the Galois generation, aᵖ≡a corollary.

### ★★ Axiom of choice / LLPO (`axiom_of_choice.md`) — choice is a free Lens parameter σ, not an axiom

EXTEND + CORRECTION of finding (vii) (the originator's push: "refused" is a cop-out, dig deeper). C = an
inhabited family X:I→Type; **L_σ = a section (choice function) = a Lens**; different choices (σ_left/σ_right/none)
= different Lenses; Residue = the σ-dependence. **Dissolution**: applying a Lens is an ACT not an existence claim,
so 213 never asserts "a section exists" — it applies a rule (σ) and reads; the non-constructivity = NO σ is
forced/canonical (no exterior dialer §5.1), i.e. **σ is a FREE Lens parameter** (like the p-adic base / resolution
dial). "AC true" (any L_σ applicable) and "AC refused" (no L_σ canonical) jointly say **σ is free**; compute
per-σ (constructive — sections are explicit data, no AC). **Deep tie**: over a binary fiber σ∈{left,right} IS the
q=±1 tag B, and **LLPO = the B-valued σ left unforced** (even/odd undecidable = the ±1 bit free, `Omniscience.LLPO`).
★ **Predicts AC's independence**: a free Lens parameter admits both adjunctions consistently — Gödel–Cohen
independence = σ free, forcing = adjoining a generic σ. Honest scope: dissolution + structural prediction, NOT a
proof of AC (213 proves neither). ∅-axiom witness `ChoiceLens.lean` (two explicit sections + σ-dependent op).
ABSENT: σ-parametrized operation library (ultrafilter/well-order/Hahn–Banach each carrying σ); the forcing
statement as a Lean theorem.

**Count.** 142 worked decompositions + the `two_cells.md` meta-decomposition + the formal `q=±1` tag; one
located partial-break (knots → two precise missing primitives) + the `Lp`/funext wall; the `det`/`tr` edge
is now **dissolved as a Lean theorem** (`Mat2Spectrum`: tr=e₁, det=e₂ of the spectrum); **fourteen**
predictions, **thirteen Lean-closed** (orthogonality 2/3/**4**/6, growing-corner, convolve-rescale contraction +
dyadic completion-limit, discrete Noether-iff, the modulated Banach engine/wall defeat, Carathéodory-as-`clo`,
the formal `q=±1` tag, `continuous_iff_preimage_dyadicopen`, the **det/tr=e₁/e₂ Vieta resolution**, the
**formal power-series semiring** `PowerSeriesSemiring`, and **Newton's identities** `newton_id_p2`/`newton_id_p3`
= the power-sum ↔ elementary-symmetric character bridge) + QR already-closed; plus Lean **groundings** of the
spectral note (`Mat2SymmetricSpectrum`: symmetric `disc≥0` = real spectrum, the `q=+1` corner), the Lie
note (`Mat2Bracket`: antisymmetry + traceless-sl + Jacobi), and the representation note (`Mat2Killing`: the
`d>1` trace character as the adjoint rep's Killing form `K=4·tr(XY)` on sl₂, `killing_gram` nondegeneracy).
The `q=+1` contraction residue spans
φ/Gaussian/ODE; the formal `q=±1` tag unites Cantor/Gödel/measure (escape) with φ/Gaussian/ODE (converge);
compactness is the `q=+1` finiteness corner; the spectrum dissolves det/tr; the Lie bracket is the `q=−1`
antisymmetry; **Stokes = the telescope** (de Rham); the Banach-engine "wall" is **defeated** (`wall_synthesis.md`).
