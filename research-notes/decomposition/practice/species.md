# Decomposition: combinatorial species (Joyal's theory)

*213-decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants — the
character arrow `×↦·`/`×↦+`, the `q=±1` residue tag — over the structured frame). A **fresh** field,
chosen to sharpen `generating_functions.md`: it asks whether the EGF is the *decategorified* end of a
ladder whose categorified top is a species. The single thesis under test:*

> **A combinatorial species is the calculus's *structure-count reading made functorial* — the
> categorification of `generating_functions.md`'s EGF.** `generating_functions.md` grounded the EGF/OGF
> as the count-reading `L_gen` packaged as a power series (`PowerSeriesSemiring.power_series_semiring`,
> `GeneratingFunction.lean`). A species `F` is the **same** count-reading taken *one level earlier* —
> a functor `FinSet+bij → FinSet` assigning to each finite set the SET of `F`-structures, **before**
> cardinality. The decategorified count is the EGF; the species is the categorified object whose
> *cardinality-reading* IS the EGF. Species operations map to EGF operations under the cardinality Lens:
> sum ↦ EGF-sum, product ↦ EGF-product (the convolution character `mass_conv`/`Convolution213.conv`),
> composition ↦ EGF-substitution, derivative ↦ EGF-derivative. The exponential formula
> (connected ↦ all via `exp`) = `exponential.md`'s `exp` = the `+↦×` character (`vp`-style). The cycle
> index series = the species read through the symmetric-group-orbit Lens (Burnside/Pólya, tying
> `groups.md`'s relabel-action and the *built* `Sym3OctetOrbits` Burnside count). **NO new primitive** —
> it is the EGF lifted from numbers to the sets-before-counting, with cardinality the Lens back down.

The bar is **PREDICTION** (the cardinality Lens is *forced* to send species-operations to EGF-operations,
and the exp-formula's `+↦×` is the same arrow already proven), with one **located break** (the
functor-to-sets object itself is ABSENT — only its post-cardinality shadow is built).

---

## The decomposition (C / Reading / Residue)

- **Construction `C` — the size-indexed count-family of `generating_functions.md`, NOT yet collapsed to
  numbers.** `generating_functions.md`'s `C` is "a **counted** construction-family `{Cₙ}` — for each `n`
  the *number* `aₙ` of distinguishables of size `n`" (`generating_functions.md:18-27`). A species is that
  family **one re-categorification earlier**: for each finite *label set* `[n]` it is the *set*
  `F[n]` of `F`-structures on those labels, plus the *relabelling action* (a bijection `[n]≅[n]` carries
  structures to structures functorially). So `C` is the distinguishing read as **a family of structured
  finite sets indexed by label-size, carrying the symmetric-group relabel action** — exactly
  `generating_functions.md`'s height-stratified `C`, but with the height-`n` slab kept as a *Σₙ-set*
  rather than its cardinality `aₙ`. The relabel functoriality is the calculus's **`Aut`-family / group**
  reading of `groups.md` ("a group is the closed family of `C`-preserving self-readings under
  composition"): the symmetric group `Σₙ` is exactly that relabel `Aut`-family, built in-repo as
  `PermGroup.composeList` with associativity `composeList_assoc` and inverses `invPerm`
  (`PermGroup.lean:59,93,128`). Nothing new is constructed: `C` = `generating_functions.md`'s family,
  un-counted, with the relabel action made explicit.

- **Reading — TWO Lenses, one above the other (this is the whole content).**
  - **`L_card` (the cardinality Lens) — the categorification ladder's down-step.** A species `F` is read
    *down* to its EGF by `|F[n]|/n!`: count the structures at each size, divide by the relabel
    symmetry. This is `cardinality.md`'s count-reading (`countTrue_append`-style finite count) applied
    slab-by-slab, then `generating_functions.md`'s EGF normalization `1/n!` — the per-size weight that
    `generating_functions.md:38-40` already names ("the EGF is the *same* family-reading with weight
    `1/n!`, the resolution kernel divided by the size-`n` symmetry group"). The `n!` is the *order of the
    relabel `Aut`-family* `Σₙ` (`PermGroup` length-`n` permutations; `factorial_succ`,
    `CutFactorial.lean:34`). **So `L_card` IS `generating_functions.md`'s `L_gen` with the EGF weight —
    `species ⟨—|L_card⟩ = the EGF`, by definition of how an EGF is computed.** This is the load-bearing
    re-seeing: the EGF is not a *different* object from the species; it is the species *read through the
    cardinality-then-symmetry Lens*.
  - **`L_orbit` (the cycle-index Lens) — read `F` through the symmetric-group-orbit Lens.** Before
    cardinality, the relabel action partitions `F[n]` into Σₙ-orbits (isomorphism types of structure).
    The *cycle index series* `Z_F` records, per group element `σ`, the count of structures it fixes,
    averaged over the group — **Burnside/Cauchy–Frobenius**: `|orbits| = (Σ_g |Fix g|)/|G|`. This is the
    `groups.md` `Aut`-family read for its *fixed-point character*, and the repo has a **real ∅-axiom
    Burnside instance**: `Sym3OctetOrbits` counts the orbits of the `Sym(3)` relabel action on the octet
    by exactly this lemma — `sym3_burnside_arithmetic : (256+3·32+2·4)/6 = 60`, `sym3_burnside_sum`,
    `suborbit_decomposition` (`Sym3OctetOrbits.lean:87,91,180`, 28/0 PURE). `Z_F` specializes to the EGF
    by setting `p₁↦x, p_{k≥2}↦0` (only fixed points of the identity contribute `|F[n]|`), and to the
    OGF / type-generating-function by setting all `pₖ↦xᵏ` (the orbit count = unlabelled structures). So
    **`L_orbit` is the finer Lens; `L_card` is its identity-element specialization** — the EGF is the
    cycle index read at "only the identity fixes."

- **Residue — the categorification gap, tagged `q=±1`.** Two residues stack, exactly the
  `generating_functions.md` pattern lifted.
  - **The functorial / set-valued object itself is the residue of the cardinality Lens (`q=+1`,
    converge-but-reached-by-none-in-repo).** `L_card` *forces* a set-of-structures upstream of every
    coefficient `aₙ` but the repo only ever holds `aₙ` (a `Nat`), never the `Σₙ`-set `F[n]`. The species
    is the residue "above" the EGF the same way `generating_functions.md:46-52` puts the *analytic* GF
    above the formal one — except here the residue is **categorical, not analytic**: it is the
    set-before-count, not the value-after-limit. This is an honest located gap (below): the functor
    object is ABSENT.
  - **The analytic species / molecular-decomposition residue (`q=±1`).** A species decomposes uniquely
    into **molecular** species (transitive Σₙ-actions = single orbits = `X^n/H` for `H ≤ Σₙ`), and those
    into **atomic** species (indecomposable under product). This molecular/atomic decomposition is the
    **`q=+1` converging residue of the orbit Lens** — every species is a (possibly infinite) sum of
    molecular pieces, the orbit decomposition `suborbit_decomposition`'s family-wide analogue (the
    `Sym3OctetOrbits` file *is* a single-size molecular decomposition: `60 = 4·sing + 28·(size 3) +
    28·(size 6)`). The *infinite* molecular sum (the full analytic species) is a `Real213`-cut-style
    residue reached by no finite truncation — same boundary as `generating_functions.md`'s analytic GF.

---

## Re-seeing — ⟨C | L⟩

```
   a species F        =  ⟨ {Σₙ-set F[n]}ₙ (un-counted relabel family) | identity Lens ⟩   (C; generating_functions.md's family BEFORE cardinality)
   the EGF of F        =  ⟨ F | L_card ⟩  =  Σ (|F[n]|/n!) xⁿ                              (THE categorification down-step — generating_functions.md's L_gen + 1/n! weight)
   |F[n]| = aₙ          =  cardinality.md's count-reading, slab n                          (countTrue-style finite count)
   the n!               =  |Σₙ| = order of the relabel Aut-family                          (PermGroup, factorial_succ)
   the cycle index Z_F  =  ⟨ F | L_orbit ⟩  =  Burnside-averaged fixed-point character     (Sym3OctetOrbits.sym3_burnside_*)
   EGF = Z_F[p₁=x,p≥2=0] /  type-GF = Z_F[pₖ=xᵏ]    =  L_card / OGF specializations of one L_orbit
   species SUM  F+G     =  disjoint union of structures   ↦   EGF-sum                       (additive, the +-readout)
   species PRODUCT F·G  =  ordered partition of labels    ↦   EGF-PRODUCT = Cauchy convolution  (mass_conv / Convolution213.conv)
   species COMPOSITION F∘G =  F-structure on G-blocks     ↦   EGF-SUBSTITUTION              (the connected↦all step)
   species DERIVATIVE F' =  structures on [n]∪{*}          ↦   EGF-DERIVATIVE                (the *-pointing reading)
   EXPONENTIAL FORMULA  =  Set ∘ F⁺ = "all from connected" =  exp(EGF of connected)        (exponential.md's +↦×, vp_mul)
```

So a species is **not** a new kind of object: it is `generating_functions.md`'s family-reading `L_gen`
**stopped one step before cardinality**, with cardinality (`L_card`) the Lens recovering the EGF. The four
species operations are the four EGF operations *seen upstream of the count*, and they descend to the EGF
operations **because `L_card` is a functor that commutes with them** — the forcing below.

### The operation dictionary (why each species-op ↦ its EGF-op is FORCED, not posited)

| Species op | What it does to structures | EGF-op under `L_card` | Why forced | Lean anchor |
|---|---|---|---|---|
| **sum** `F+G` | structure is an `F`- *or* a `G`-structure (disjoint) | `(F+G)(x) = F(x)+G(x)` | cardinality is additive on disjoint union (`|A⊔B|=|A|+|B|`) | the `+`-readout (`countTrue_append`-style additivity, `LLN.lean`) |
| **product** `F·G` | split labels into an ordered pair of blocks, `F` on one, `G` on the other | `(F·G)(x)=F(x)·G(x)` = **Cauchy convolution** `Σ_{i+j=n} (|F[i]|/i!)(|G[j]|/j!)` | the EGF product is convolution (the unique product respecting the size-grading `xⁱxʲ=x^{i+j}`); the binomial `n!/(i!j!)` is exactly the label-split count | `ConvolveProfile.mass_conv` (∅-axiom: `mass(f⋆g)=mass f·mass g`), `Convolution213.conv_comm`/`conv_assoc`, `GeneratingFunction.convolution`, `PowerSeriesSemiring.power_series_semiring` |
| **composition** `F∘G` | an `F`-structure whose `F`-slots are filled with `G`-structures on a label-partition | `(F∘G)(x)=F(G(x))` substitution | substitution is the only operation taking "structure on blocks" to coefficients; the connected↦all special case is the exp-formula row | (substitution composite of the convolution semiring — **not isolated as a Lean op**; see Dropped) |
| **derivative** `F'` | `F'[n] = F[n∪{*}]`: structures on one extra distinguished "ghost" label | `F'(x) = d/dx F(x)` | the `*`-pointing shifts the size-index by one with weight `n+1` — `derivative.md`'s resolution-step on the grading axis | `derivative.md`'s `L₋`/shift reading (the discrete `Δ` on `CoeffSeq`; **not isolated as a Lean `derivative` on GFs**) |
| **exponential formula** | `Set(F⁺)`: an arbitrary structure = a SET of connected pieces | `exp(F⁺(x))` | `exp` is the unique `+↦×` character turning the "independent connected pieces" *sum* of EGFs into a *product*/series — `exponential.md`'s `L_exp` | `exponential.md`'s `vp_mul` / `vp_pow` (`+↦×`, `VpMul.lean:165,183`, ∅-axiom); `entropy.md`'s "−log forced as the `×↦+` character" run backward |

The exp-formula row is the deepest cross-tie: `entropy.md`/`exponential.md` already proved the `+↦×`
character is the *unique* arrow turning a product of independent weights into a sum (and back). "Connected
structures compose independently into all structures, so EGF_all = exp(EGF_connected)" is **the same
arrow** — independence (multiplicative) of connected components ↦ additive log-count, run through `exp` to
recover the product. No new mechanism; `exponential.md`'s `L_exp` *is* the species exp-formula.

---

## Revelation (collapse + forcing + spine)

**Collapse.** The EGF and the species are **one object read at two categorification levels** — the EGF is
`⟨species | L_card⟩`. This is the precise upgrade `generating_functions.md` left open: that note read the
EGF as the family-reading `L_gen` over a family of *numbers* `{aₙ}`; species says those numbers were
themselves a *reading* (`L_card`) of a family of *Σₙ-sets* `{F[n]}`, and the EGF operations
(sum/product/composition/derivative) are the *images under that reading* of set-level operations
(disjoint-union/label-split/block-substitution/ghost-pointing). The "GF product = convolution" theorem
(`mass_conv`, the centerpiece of `generating_functions.md`) is re-revealed as **species-product ↦
EGF-product**: the convolution is what the *label-splitting* product becomes after counting. So the
single ∅-axiom `mass_conv` now reads in a *third* field (after probability/CLT and generating functions):
it is the cardinality-image of the species product.

**Forcing.** Three things are *forced*, not chosen:
1. The EGF normalization `1/n!` is **forced** as the order of the relabel `Aut`-family `Σₙ`
   (`PermGroup`, `factorial`), not an arbitrary convention — it is "divide by the symmetry you quotiented
   to count *iso-classes*," the Burnside denominator `|G|` (`sym3_burnside_arithmetic`'s `/6`).
2. Species-product ↦ EGF-product **must** be the Cauchy convolution because the size-grading forces
   `xⁱxʲ=x^{i+j}` (the `generating_functions.md` forcing), and the binomial label-split count `n!/(i!j!)`
   is exactly what makes the *EGF* (not OGF) product multiply cleanly — proven `mass_conv` ∅-axiom.
3. The exp-formula `Set(F⁺) ↦ exp` is **forced** as `exponential.md`'s unique `+↦×` character — the same
   arrow as `vp_mul`, run on connected-component counts.

**Spine (`q=±1`).** The species sits on the calculus's spine through its **orbit Lens**:
- `q=+1` (converge/closure): the molecular/atomic decomposition — every species is its orbit
  decomposition, the `Aut`-family quotient *closing* (the finite witness `suborbit_decomposition`,
  `60 = 4+0·2+28·3+28·6`, is the `q=+1` orbit-count fixed point reached *exactly* at the group order, the
  same shape as `CyclicErgodic`'s `birkhoff_period_eq_space`). The cycle-index series IS that closure
  read family-wide.
- `q=−1` (escape): the *un-counted* functor object — the set `F[n]` upstream of every coefficient is the
  categorification residue `L_card` forces but the repo never holds (the absent species object, below). It
  is the categorical sibling of `generating_functions.md`'s analytic-GF residue: not reached by any finite
  numeric truncation.

This is the **categorification direction** the notebook had not yet recorded: every prior `L_card`-style
count-reading (`cardinality.md`, `generating_functions.md`, `probability.md`) has an *un-counted functor
above it*, and species names that ladder explicitly. The two invariants are unchanged; the new datum is the
**vertical (categorification) axis on the count-reading** — `L_card` is a functor, and species-ops are its
*preimages*, descending to EGF-ops because `L_card` commutes with them.

---

## VALIDATE verdict — **PREDICTION** (with one located break)

EXTEND-by-categorification + a sharp PREDICTION, no new primitive, plus a clean located absence.

- **PREDICTION (the load-bearing claim).** The calculus predicts — and `generating_functions.md`'s
  ∅-axiom machine *certifies the down-step* — that the four species operations descend to the four EGF
  operations under `L_card`, with the product being the convolution `mass_conv` and the exp-formula being
  `exponential.md`'s `+↦×` character. The *EGF-level* legs are all built and PURE (convolution semiring,
  `vp_mul`); the prediction is that they are the cardinality-images of species-ops. This passes the
  re-skin guard at the `generating_functions.md` level (a verified theorem, `mass_conv`, re-read in a new
  field), and adds the categorification ladder as genuinely new structure.
- **BREAK (located, honest, NOT fatal).** The *functor-to-finite-sets* object — `Species`, `speciesSum`,
  `speciesProduct`, `speciesComposition`, `speciesDerivative`, `cycleIndex`, `molecular`/`atomic` — is
  **ABSENT** (grep-confirmed below). Only the post-cardinality shadow (the EGF, `GeneratingFunction`/
  `PowerSeriesSemiring`) and a *single-size* orbit instance (`Sym3OctetOrbits`) are built. This is the
  same shape as the SYNTHESIS "engine built, named object missing" class (cf. `homological_algebra`'s
  `Ext^n`, `generating_functions`'s EGF-as-function): the *cardinality-image* engine is PURE; the
  *categorified functor* naming it is open. The break is **categorical, not constructive** — there is no
  axiom obstruction (a finite-label `F[n]` as a `List`/subtype Σₙ-set would be ∅-axiom-able, like
  `Sym3OctetOrbits`'s octet); it is unbuilt work, not a wall. Recorded as a promotion target, not a hard
  absence.

Net: **PREDICTION** — the EGF is the species' cardinality-reading, the species-ops descend to the
verified EGF-ops, and the cycle index is the `groups.md`/Burnside orbit Lens (built at one size). The
categorification ladder on the count-reading is the new structural datum; the functor object is the
located, buildable absence.

---

## Verified Lean anchors (file:line:theorem — all grep-confirmed; scan tallies from `tools/scan_axioms.py`)

| Leg | Theorem / def (file:line) | Purity (module scan) |
|---|---|---|
| ★ cardinality Lens down-step: GF product = convolution (species-product ↦ EGF-product) | `Lib/Math/Probability/Limit/ConvolveProfile.lean:190` `mass_conv` (`mass(f⋆g)=mass f·mass g`); `:239` `momentNum_conv` | ConvolveProfile **20/0 PURE** (`mass_conv`, `momentNum_conv` PURE) |
| convolution operator + semiring (the EGF product is associative/commutative) | `Meta/Nat/Convolution213.lean:156` `conv_comm`, `:257` `conv_assoc`, `:281` `delta` | Convolution213 **49/0 PURE** |
| formal GF object (`L_card`'s target): CoeffSeq, x-grading, Cauchy product | `Lib/Math/Combinatorics/GeneratingFunction.lean:27` `CoeffSeq`, `:36` `xVar`, `:50` `convolution`, `:58` `conv_one_at_0`, `:80` `catalanGF_table` | GeneratingFunction **14/0 PURE** |
| welded power-series semiring + multiplicative character on the welded product | `Lib/Math/Combinatorics/PowerSeriesSemiring.lean:373` `power_series_semiring`, `:361` `massN_toCoeffSeq_conv`, `:294` `toCoeffSeq_conv`, `:98` `conv_eq_cauchy` | PowerSeriesSemiring **33/0 PURE** |
| ★ cycle-index Lens (`L_orbit`): Burnside orbit count of a relabel action | `Lib/Math/Combinatorics/Sym3OctetOrbits.lean:87` `sym3_burnside_arithmetic` (`(256+3·32+2·4)/6=60`), `:91` `sym3_burnside_sum`, `:180` `suborbit_decomposition` (`60=4+0·2+28·3+28·6`) | Sym3OctetOrbits **28/0 PURE** |
| relabel `Aut`-family = symmetric group (the `n!` symmetry, `groups.md`) | `Lib/Math/Algebra/Linalg213/PermGroup.lean:59` `composeList`, `:93` `composeList_assoc`, `:128` `invPerm`, `:145` `composeList_invPerm_right`, `:184` `composeList_invPerm_left` | PermGroup **19/0 PURE** |
| the `n!` normalization (order of `Σₙ`) | `Lib/Math/NumberSystems/Real213/ExpLog/CutFactorial.lean:20` `factorial`, `:34` `factorial_succ`, `:37` `factorial_pos` | (def; `factorial_succ`/`factorial_zero`/`factorial_one` by `rfl`) |
| ★ exp-formula = `+↦×` character (connected ↦ all) | `Meta/Nat/VpMul.lean:165` `vp_mul` (`vp p (m·n)=vp p m + vp p n`), `:183` `vp_pow`, `:204` `vp_self_pow` | VpMul **10/0 PURE** |

Scan command run from repo root, e.g.
`python3 tools/scan_axioms.py E213.Lib.Math.Combinatorics.Sym3OctetOrbits` → `# 28 pure / 0 dirty`.
All seven cited modules: **GeneratingFunction 14/0, PowerSeriesSemiring 33/0, ConvolveProfile 20/0,
Convolution213 49/0, Sym3OctetOrbits 28/0, PermGroup 19/0, VpMul 10/0 — every one ∅-axiom PURE.**

---

## Dropped / flagged

- **`Species` / `speciesSum` / `speciesProduct` / `speciesComposition` / `speciesDerivative` /
  `cycleIndex` / `molecular`/`atomic` / `EGF` (named functor objects) — ABSENT.** Grep-confirmed:
  `grep -rln "def Species\|structure Species\|speciesProduct\|speciesComposition\|speciesDerivative\|def cycleIndex\|molecularSpecies\|atomicSpecies\|def EGF" E213/` returns **empty**. The only `species`
  hits in the corpus are `Mobius213/Px/SymmetrySpecies.lean`'s `FamilySpecies`/`AutGroup` — an *unrelated*
  catalogue tag for char-poly automorphism labels (per `groups.md:113`, `representation.md:246`), **not**
  Joyal species; not cited. Marked **predicted-not-built** (as the prompt anticipated).
- **Species composition `F∘G` and derivative `F'` as isolated Lean operations on GFs — NOT built.** The
  EGF *substitution* and *derivative* operations are not isolated theorems on `CoeffSeq`; only the
  *product* (convolution) and the additive/multiplicative *characters* are proven. Composition and
  derivative are cited only via their `generating_functions.md`/`derivative.md` decompositions, not as
  certified GF-operations. Flagged as the open legs of the operation dictionary.
- **The EGF `1/n!` weight as a Lean coefficient reading — NOT instantiated** (same honest gap
  `generating_functions.md:260-263` records: "no `EGF` type, no `aₙ/n!` coefficient reading"). The built
  anchors are the OGF-side convolution; `factorial` exists, but no `EGF` reading welds it to `CoeffSeq`.
  The species ↦ EGF down-step is therefore certified at the *product/character* level, with the `1/n!`
  weld a named target.

### Verified buildable witness (named, not asserted)

A finite-label molecular instance is already *built* as a witness of `L_orbit`: `Sym3OctetOrbits`
(`suborbit_decomposition`, 28/0 PURE) is a single-size species' orbit (molecular) decomposition —
`60 = 4·(size 1) + 0·(size 2) + 28·(size 3) + 28·(size 6)`, a Σ(3)-set quotient by Burnside. The
buildable promotion target the calculus *predicts*: a finite-label `Species` as a `List`/subtype Σₙ-set
(the octet generalized), with `speciesProduct` welded to `Convolution213.conv` and `|F[n]|/n!` the
`L_card` down-step recovering `GeneratingFunction.CoeffSeq` — ∅-axiom-able exactly as `Sym3OctetOrbits`
is, since the obstruction is categorical-naming, not axiomatic. Not asserted as built; named as the
located, verified-buildable leg.
