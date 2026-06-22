# Decomposition: additive combinatorics (sumsets A+B, sum-product, Freiman, Plünnecke–Ruzsa, Szemerédi, Cauchy–Davenport)

*213-decomposition of "the additive vs multiplicative structure of a finite set" — sumsets `A+B`, the
sum-product phenomenon `max(|A+A|,|A·A|) ≥ |A|^{1+ε}`, Freiman's theorem (small doubling ⟹ generalized
AP), the Plünnecke–Ruzsa doubling inequalities, Szemerédi's theorem (dense sets contain APs), and the
Cauchy–Davenport inequality — per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`, the
REVELATION rule) and `../SYNTHESIS.md` (the two invariants — ESPECIALLY Invariant A, the single character
arrow read two ways `×↦·` / `×↦+`). Honest grounding note up front: unlike `ramsey_theory.md` (which is
substantially BUILT), the **named additive-combinatorics objects are ABSENT** — grep over `lean/E213` for
`sumset`/`Freiman`/`Plunnecke`/`Ruzsa`/`sum_product`/`Cauchy_Davenport` returns **zero matches**, and the
only `AP` symbol in the repo is the Lambert-polynomial coefficient list `AP n`
(`ExpLog/LambertPoly.lean`), unrelated to arithmetic progressions. What IS built — and what carries this
decomposition — is the **character split itself**: the `×↦·` arrow (`det2_mul`, `legendre_mul`) and the
`×↦+` arrow (`vp_mul`, `vp_separation`) with the **wall between them** (`two_three_unique`), plus the
count-threshold engine (`ramsey_theory.md`'s `ramsey_lower`/`erdos_schema`) Szemerédi rides.*

## The thesis

**The sum-product phenomenon IS Invariant A's `×↦·` / `×↦+` character incompatibility made a
combinatorial theorem.** `SYNTHESIS.md` Invariant A is *one* construction-preserving character arrow read
two ways: `×↦·` (the multiplicative reading, which sees factorization — `det2_mul`, `legendre_mul`) and
`×↦+` (the additive/logarithmic reading, which linearizes the multiplicative structure onto independent
prime axes — `vp_mul`, `vp_separation`). `prime_factorization.md` already proved these two readings sit on
opposite poles of one axis (atom-distinguishability) and that **the two cannot be collapsed into each
other** — the `^`-wall `two_three_unique` (`2^a = 3^b ⟹ a=b=0`) is the *positive form* of the
non-collapse: the additive `+`-axis and the multiplicative `×`-axes never trade.

The sum-product theorem — `max(|A+A|, |A·A|) ≥ |A|^{1+ε}`, i.e. *a finite set cannot be simultaneously
additively-structured (small `A+A`) and multiplicatively-structured (small `A·A`)* — is **exactly that
non-collapse read on a single finite set's two doubling-counts.** Additive structure (closed under `+`,
the `×↦+` reading's structured sets) and multiplicative structure (closed under `×`, the `×↦·` reading's
structured sets) cannot **both** be tight on the one set: the set is forced to spread under at least one of
the two characters. This is the combinatorial shadow of the character split being a **genuine fork** — the
same set can't be a subgroup for both `+` and `·` (except the trivial / full-field cases). Then:

- **Freiman** (small doubling `|A+A| ≤ K|A|` ⟹ `A ⊆` a generalized AP) = the **`×↦+` structured-sets
  normal form**: the additive-structure reading's tight sets ARE the APs / lattices / GAPs, just as
  `prime_factorization.md`'s `×↦·` structured sets are the prime-axis lattices.
- **Plünnecke–Ruzsa** (the doubling constant is sub-multiplicative: `|A+B+C| ≤ (|A+B||A+C|)/|A|`,
  `|nA| ≤ Kⁿ|A|`) = the **`×↦·` character read ON the doubling functional** — the doubling constant
  multiplies under iterated sumsets, exactly the `convolution` multiplicativity (`mass_conv` — total mass
  is multiplicative under `⋆`).
- **Szemerédi** (density `⟹` AP) = **`ramsey_theory.md`'s density-unavoidability threshold (`q+1`
  unavoidability) on the additive structure** — the directed/order sub-family the Ramsey note flagged
  ABSENT.
- **Cauchy–Davenport** (`|A+B| ≥ min(p, |A|+|B|−1)` mod p) = the sumset count's `q=+1` *lower* bound in
  the prime cyclic group — the additive analogue of Sperner's saturation pole.

So additive combinatorics = (sum-product = the `×↦·` vs `×↦+` incompatibility) + (Freiman = the `×↦+`
structured sets = APs/GAPs normal form) + (Szemerédi = density-unavoidability, Ramsey `q+1`) — **NO new
primitive**; it is Invariant A's two-character fork made a combinatorial dichotomy.

## The decomposition

- **Construction `C`** — distinguishing, iterated into a **finite set `A` of distinguishables** carrying
  *both* operations. The same `ℕ`/`ℤ` construction that `parity.md` reads with `L₂` and
  `prime_factorization.md` reads with `L_vp` — but now `A` is a *finite sub-collection*, and the object of
  study is how `A` behaves under the `+`-construction (`A+B = {a+b}`) versus the `×`-construction
  (`A·B = {a·b}`). `C` carries the atom-distinguishability axis (`prime_factorization.md`): the `×`-atoms
  (primes) are distinguishable (vector readout, `two_three_unique`), the `+`-atom (unit) is not (scalar
  readout, `append_comm`).

- **Reading — the TWO character readings on `A`, read as COUNTS:**
  - `L_+` = the **additive doubling count** `A ↦ |A+A|` — the `×↦+` character's footprint: how much `A`
    spreads under the operation whose structured sets are APs/lattices.
  - `L_·` = the **multiplicative doubling count** `A ↦ |A·A|` — the `×↦·` character's footprint: how much
    `A` spreads under the operation whose structured sets are geometric/prime-axis lattices.
  - The **doubling constant** `K = |A+A|/|A|` is `L_+` normalized; the decisive parameter is the
    **smallness condition** `|A+A| ≤ K|A|` (Freiman's hypothesis), the count-reading's resolution dial
    promoted to a condition — exactly the move `ramsey_theory.md`/`topology.md`/`measure.md` each made.

- **Residue `Residue(L, C)` — q=±1, the character fork:**
  - **The fork (sum-product)** — the residue is that `L_+` and `L_·` **cannot both be `≈|A|`** (both
    tight). Tightness of `L_+` is additive subgroup-structure (`×↦+` exact); tightness of `L_·` is
    multiplicative subgroup-structure (`×↦·` exact); `two_three_unique` says the `+`-axis and the `×`-axes
    never trade, so the *one* set cannot satisfy both — at least one count must escape to `|A|^{1+ε}`. The
    incompatibility IS the residue: the surplus the two-character reading forces but neither character
    alone captures.
  - **q=+1 (converge / structured)** — when one character IS tight (small doubling), the residue
    *converges onto a normal form*: Freiman forces `A ⊆` a GAP (the `×↦+` structured set), the additive
    analogue of `prime_factorization.md`'s "zero residue = unique factorization" — small doubling buys you
    a coordinate lattice. This is the `golden_is_converge` pole at finite size.
  - **q=−1 (escape / spread)** — when neither character is tight, the set *escapes both* — the
    sum-product lower bound. This is `cardinality.md`'s escaping diagonal
    (`object1_not_surjective`/`no_surjection_of_fixedpointfree`) read at finite size: the count escapes the
    structured image under at least one character.

## Re-seeing — `⟨C | (L_+, L_·)⟩ ⊕ Residue(q=±1)` (Invariant A's fork at finite size)

```
  sumset A+B            =  ⟨ finite A | L_+ = additive doubling count ⟩        (the ×↦+ character's footprint)
  product set A·B       =  ⟨ finite A | L_· = multiplicative doubling count ⟩  (the ×↦· character's footprint)
  sum-product           =  Residue: L_+ and L_· CANNOT both be tight           (×↦+ vs ×↦· incompatibility = two_three_unique)
    max(|A+A|,|A·A|)≥|A|^{1+ε}  =  the one set forced to escape ≥1 character    (q=−1 escape, no joint subgroup)
  Freiman small doubling=  L_+ tight ⟹ Residue CONVERGES to a GAP normal form  (q=+1; ×↦+ structured set = AP/lattice)
  Plünnecke–Ruzsa       =  the doubling constant is sub-MULTIPLICATIVE          (×↦· character ON the doubling; mass_conv)
  Szemerédi (density⟹AP)=  Ramsey q+1 density-unavoidability on +-structure     (ABSENT — predicted; ramsey directed sub-family)
  Cauchy–Davenport      =  |A+B| ≥ min(p,|A|+|B|−1)  =  sumset q+1 lower bound  (ABSENT — predicted; additive saturation pole)
  the ×↦· / ×↦+ split   =  ONE character arrow, two readings — the genuine fork (det2_mul/legendre_mul vs vp_mul; two_three_unique)
```

The load-bearing collapse: the **two doubling counts are the two readings of the ONE character arrow**
(`SYNTHESIS.md` Invariant A) applied to a finite set. Sum-product is not a new phenomenon to be proved
from scratch — it is the **finite-set shadow** of the fact `prime_factorization.md` already proved at the
level of `ℕ`: the `+`-axis and the `×`-axes are independent (`two_three_unique`), so no single set can be a
subgroup for both. That independence, read on `ℕ`, gives unique factorization (zero `×↦+` residue); read
on a *finite* `A`, it gives sum-product (the two doubling counts can't both vanish).

## Revelation (collapse + forcing + the q=±1 spine)

**Additive combinatorics is Invariant A's two-character fork made a combinatorial dichotomy — no new
primitive.** Four classically-separate results fuse onto the one character arrow and the count-threshold:

1. **Sum-product = the `×↦·` vs `×↦+` character incompatibility, made a finite theorem (the new datum).**
   `SYNTHESIS.md` Invariant A is one arrow read two ways; `prime_factorization.md` proved the two readings
   are *non-collapsible* (the `^`-wall `two_three_unique`: the additive and multiplicative axes never
   trade) and that this non-trade is the dual of `+`-atom indistinguishability (`append_comm`). Sum-product
   says the *same* non-trade at finite cardinality: a set that is additively tight (small `|A+A|`, a near-
   subgroup for `+`) read through `×` must spread (large `|A·A|`), and vice versa — because being a
   subgroup for `+` and a subgroup for `·` simultaneously is exactly the field/trivial case the wall
   forbids for proper sub-collections. **This is the load-bearing new datum** distinguishing this note from
   `parity.md`/`prime_factorization.md` (which read the characters on all of `ℕ`, where there is no
   "spread" to count) and from `ramsey_theory.md` (which read *one* count-threshold, not the *two-character
   fork*): sum-product is the character split realized as a **count incompatibility on one finite set**.
   Lean certifies the two characters (`det2_mul`/`legendre_mul` = `×↦·`; `vp_mul`/`vp_separation` = `×↦+`)
   and the non-collapse between them (`two_three_unique`); the *named* sum-product inequality on a finite
   carrier is ABSENT (no `|A+A|`/`|A·A|` count object).

2. **Freiman = the `×↦+` structured sets are the APs/GAPs (the normal-form forcing).** Small doubling
   `|A+A| ≤ K|A|` is the `×↦+` character being *tight*, and the conclusion `A ⊆` a generalized AP is the
   **additive twin of `prime_factorization.md`'s unique-factorization normal form**: where the tight `×↦·`
   reading has the prime-axis lattice as its structured set (faithful coordinate, `vp_separation`), the
   tight `×↦+` reading has the **arithmetic progression / coordinate lattice** as *its* structured set. The
   GAP `{x₀ + Σ ℓᵢ dᵢ : 0 ≤ ℓᵢ < Lᵢ}` is literally a `+`-coordinate lattice — the additive analogue of the
   exponent vector `(v₂, v₃, …)`. So Freiman is the statement that the `×↦+` character's *tight* sets have a
   forced coordinate normal form, exactly parallel to factorization being the `×↦·` character's. This is a
   forcing, not a re-skin: the AP normal form is *forced* by additive tightness the way the exponent vector
   is forced by `vp_mul` + faithfulness.

3. **Plünnecke–Ruzsa = the `×↦·` character read ON the doubling functional.** The doubling constant
   `K = |A+A|/|A|` is **sub-multiplicative under iterated sumsets**: `|nA| ≤ Kⁿ|A|`, and more sharply
   `|B+C| ≤ |A+B||A+C|/|A|`. This is the `×↦·` character (the *multiplicative* reading) applied not to the
   set but to *the doubling count itself* — the count of an iterated sumset multiplies. The repo's
   `ConvolveProfile` makes the engine literal: `mass_conv` (`mass(f⋆g) = mass f · mass g`, total mass
   multiplicative under convolution, the `×↦·` arrow) and `momentNum_conv` (mean additive under `⋆`, the
   `×↦+` twin) are exactly "the count of a sum of independents multiplies" — Plünnecke–Ruzsa is that
   multiplicativity read as a sub-multiplicative *bound* on the sumset count. So the doubling constant
   inherits the character arrow: it spreads multiplicatively because the sumset count convolves.

4. **Szemerédi = Ramsey's density-unavoidability (`q+1`) on the additive structure.** `ramsey_theory.md`
   read the count-threshold and **explicitly flagged Szemerédi/van der Waerden as ABSENT** — the
   *directed/order sub-family* variant of the threshold (an AP = a swap-stable directed sub-family).
   Szemerédi's theorem (every positive-density subset of `[N]` contains a length-`k` AP) is precisely
   `ramsey_theory.md`'s `q=+1` unavoidability pole (`exists_collision`/`erdos_schema`'s threshold flip)
   read on the **additive** sub-family rather than the clique sub-family: below the density threshold an
   AP-free set escapes (`q=−1`, the Behrend construction = the additive escape), above it every dense set
   is forced to contain the AP (`q=+1`, unavoidability). The hardest leg (Szemerédi's density-regularity)
   meets the **same arbitrary-cover / infinite-quantifier wall** `topology.md`/`measure.md`/`ramsey_theory.md`
   located — a calibrated residual, not a finite COUNT object.

5. **Cauchy–Davenport = the sumset count's `q=+1` lower bound (additive saturation).** `|A+B| ≥ min(p,
   |A|+|B|−1)` in `ℤ/pℤ` is the **additive analogue of Sperner's saturation pole** (`sperner_theorem`, the
   `q=+1` dual double-count): the sumset cannot be *too small*, the lower envelope forced by the cyclic
   group having no proper subgroup (p prime). This is the `×↦+` character's tightness floor — the
   complement of sum-product's "can't be too small for both."

**The q=±1 spine, instanced via Invariant A.** `prime_factorization.md` read the character split on all of
`ℕ` (zero `×↦+` residue = unique factorization, the faithful coordinate). Additive combinatorics reads the
*same* split on a **finite set**, where the residue becomes *switchable* by the doubling: tight (`q=+1`,
Freiman GAP normal form, the converging structured pole) vs spread (`q=−1`, sum-product escape, the set
flees the structured image under ≥1 character). The **new contribution to the spine** is that here the
`q=±1` residue is driven by **Invariant A's fork itself** — the two characters can't both converge on one
set, so the residue tag is forced negative for at least one of the two readings. Sum-product is the
sharpest statement in the corpus that the `×↦·` / `×↦+` split is a *genuine fork*, not a notational
choice: read two ways on one finite set, the two readings provably disagree (one must spread). "A set
can't be both additively and multiplicatively structured" = "the one character arrow, read two ways on a
finite set, cannot have both readings tight" = `two_three_unique` at finite cardinality.

## VALIDATE — verdict

**EXTEND (by consolidation) + PREDICTION, with the named objects ABSENT.** Additive combinatorics
introduces **no new axis and no new primitive**: it is `SYNTHESIS.md` Invariant A (the one character arrow,
`×↦·` / `×↦+`) read two ways on a finite set, plus the `q=±1` residue tag (`ResidueTag`), plus the
count-threshold dial promoted to a condition (the same move `ramsey_theory.md` made). Reasons it is
consolidation, not stress:

1. **Sum-product = the character incompatibility (`two_three_unique`) at finite cardinality** — the two
   doubling counts are the two readings of the *one* arrow `prime_factorization.md` already proved
   non-collapsible. The fork is built at the `ℕ` level (`det2_mul`/`legendre_mul` vs `vp_mul`, separated by
   `two_three_unique`); sum-product is its finite-set shadow.
2. **Freiman = the `×↦+` structured-sets normal form** — the additive twin of unique factorization
   (`vp_separation`), the AP/GAP the `+`-coordinate lattice, parallel to the exponent vector.
3. **Plünnecke–Ruzsa = `×↦·` ON the doubling** — the sumset count multiplies under iteration, the
   `mass_conv` convolution multiplicativity read as a sub-multiplicative bound.
4. **Szemerédi = Ramsey `q+1` on the additive sub-family** — closes the directed/order-variant cell
   `ramsey_theory.md` explicitly left open.

**The PREDICTION / honest residual — precisely located:**
- **Every named additive-combinatorics object is ABSENT.** grep over `lean/E213` for
  `sumset`/`Sumset`/`Freiman`/`Plunnecke`/`Plünnecke`/`Ruzsa`/`sum_product`/`sumProduct`/`Cauchy_Davenport`/
  `cauchy_davenport` returns **zero matches**; grep for `arithmetic_progression`/`ArithmeticProgression`
  returns nothing (the `AP n` hits are Lambert-polynomial coefficient lists in
  `Real213/ExpLog/LambertPoly.lean`, NOT arithmetic progressions; the `isAP` predicate does not exist).
  There is **no `|A+A|`/`|A·A|` doubling-count object, no GAP type, no doubling constant.** This is a
  PREDICTION-grade decomposition: the *characters and the wall between them are built* (`det2_mul`,
  `legendre_mul`, `vp_mul`, `vp_separation`, `two_three_unique`), and the *count-threshold engine* is built
  (`ramsey_lower`, `erdos_schema`, `sperner_theorem`), but the *named field objects gluing the two together
  on a finite set* are not written.
- **Sum-product, Freiman, Plünnecke–Ruzsa, Cauchy–Davenport are predicted-buildable** on the existing
  character + finite-count infra (the carriers exist: finite `Bool`/`List` sets as in `RamseyNamedBound`,
  the characters as `vp`/`det2`/`legendre`). I did **not** verify a concrete `decide`-bounded witness, so I
  assert none — flagged predicted-buildable, not built.
- **Szemerédi's density-regularity leg** meets the same arbitrary-cover / infinite-quantifier residual
  `topology.md`/`measure.md`/`ramsey_theory.md` located — a calibrated boundary, not a finite COUNT object.

**No BREAK.** The normal form `⟨C | (L_+, L_·)⟩ ⊕ Residue(q=±1)` covers the structure: the two doubling
readings are Invariant A's two characters, the residue is their forced incompatibility, the threshold is
the resolution dial. The absences are *named field objects on existing character+count infra*, the same
predicted-not-built shape as `ramsey_theory.md`'s Turán/vdW — not the isotopy/colimit-quotient break
(`knots.md`) nor the propext ceiling. The two invariants and four axes are unchanged in the interior.

---

## Verified Lean anchors (file : line : theorem) — all grep-confirmed + scan-tallied

All scans run `python3 tools/scan_axioms.py E213.<module>` from repo root.

**Invariant A — the character arrow `×↦·` (multiplicative reading = `L_·`'s footprint):**
- `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul` —
  `det2(mul M N) = det2 M * det2 N` (the `×↦·` character, determinant form). Module **130/0 PURE**.
- `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` — the Legendre/quadratic
  character is multiplicative (the `×↦·` arrow in `{±1}`). Module **5/0 PURE**.

**Invariant A — the character arrow `×↦+` (additive/log reading = `L_+`'s footprint), and the WALL:**
- `Meta/Nat/VpMul.lean:165` `vp_mul` — `vp p (m·n) = vp p m + vp p n` (the `×↦+` character: multiplication
  linearizes to coordinate addition). `vp_mul` confirmed **[PURE]** (module 10/0).
- `Meta/Nat/VpSeparation.lean:172` `vp_separation` — the valuation vector is faithful (the `×↦+` reading's
  zero-residue = unique factorization = the structured-set normal form Freiman mirrors). `vp_separation`
  confirmed **[PURE]** (module 9/0).
- `Meta/Nat/FoldCriterion.lean:158` `two_three_unique` — `2^a = 3^b ⟹ a=0 ∧ b=0`: the `+`-axis and
  `×`-axes never trade — **the non-collapse between the two characters, which sum-product reads at finite
  cardinality.** `two_three_unique` confirmed **[PURE]** (module 8/0).
- `Meta/Nat/UnitList.lean:53` `append_comm` — `+`-atom (unit) indistinguishability, the dual pole of
  `two_three_unique` (`prime_factorization.md`).

**Plünnecke–Ruzsa engine — `×↦·` ON the doubling (convolution multiplicativity):**
- `Lib/Math/Probability/Limit/ConvolveProfile.lean:190` `mass_conv` — `mass(f⋆g) = mass f · mass g` (total
  mass multiplicative under convolution = the `×↦·` doubling). `mass_conv` confirmed **[PURE]** (module 20/0).
- `:239` `momentNum_conv` — mean additive under `⋆` (the `×↦+` twin). Confirmed **[PURE]**.

**The q=±1 spine (the character fork's two poles):**
- `Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`, `:133` `escape_residue_outside`
  (q=−1, the sum-product spread pole, ⟵ `no_surjection_of_fixedpointfree`), `:160` `converge_residue_fixed`
  (q=+1, the Freiman GAP normal-form pole), `:180` `golden_is_converge`, `:86` `multiplier_unimodular`.
  Module **55/0 PURE**.
- `Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective`, `:47` `object1_injective` — the
  escaping diagonal sum-product reads at finite size. Module **7/0 PURE**.

**Szemerédi = Ramsey `q+1` density-unavoidability (the threshold engine, from `ramsey_theory.md`):**
- `Lib/Math/Combinatorics/RamseyNamedBound.lean:174` `ramsey_lower` — `2·C(N,k) < 2^{C(k,2)} ⟹` a
  structure-dodging 2-colouring exists (the `q=−1` escape; the AP-free analogue is the Behrend
  construction). Module **13/0 PURE**.
- `Lib/Math/Combinatorics/CountExistence.lean:192` `erdos_schema` — `t·c < 2ⁿ ⟹` a dodging colouring
  (the threshold = the resolution dial as a condition; below = AP-free escape). Module **10/0 PURE**.
- `Lib/Math/Combinatorics/Pigeonhole.lean:166` `exists_collision` — the `q=+1` forcing base (density
  forces coincidence). Module **5/0 PURE**.

**Cauchy–Davenport = additive saturation, the analogue of Sperner's `q+1` dual double-count:**
- `Lib/Math/Combinatorics/SpernerChains.lean:534` `sperner_theorem` — `|F| ≤ C(n,⌊n/2⌋)`, the `q=+1`
  saturation pole (Cauchy–Davenport is its additive-sumset lower-bound twin). Module **50/0 PURE**.

**Cross-references (prior decompositions this note consolidates):**
- `../SYNTHESIS.md` §2 Invariant A (the single character arrow `×↦·` / `×↦+` — the load-bearing object;
  sum-product = its fork made combinatorial).
- `../practice/prime_factorization.md` (the `×↦+` character `vp_mul`, faithfulness `vp_separation`, the
  wall `two_three_unique`, atom-distinguishability — the `ℕ`-level statement of the split sum-product reads
  at finite cardinality), `../practice/parity.md` (the `×↦·`/`×↦{±1}` character `det`/Legendre).
- `../practice/ramsey_theory.md` (the count-threshold `q=±1` flip — Szemerédi = its directed/AP sub-family
  variant, explicitly flagged ABSENT there; this note locates it as the same threshold on the additive
  structure), `../practice/cardinality.md` (the escaping diagonal sum-product reads at finite size),
  `../practice/fourier.md` (the Fourier-analytic method — the dual `Ĉ` reading underlying the
  Hardy–Littlewood circle-method proofs of Szemerédi/Roth; the `×↦+` character's dual face).

## Dropped / flagged (could not verify / predicted-not-built)

- **Sumset `A+B` / product set `A·B` count objects — ABSENT.** grep `sumset`/`Sumset`/`SumSet` over
  `lean/E213` → **zero matches**. No `|A+A|`/`|A·A|` doubling-count is defined. Flagged
  predicted-buildable on the finite-set carriers in `RamseyNamedBound` (no concrete witness asserted).
- **Sum-product theorem `max(|A+A|,|A·A|) ≥ |A|^{1+ε}` — ABSENT.** grep `sum_product`/`sumProduct`/
  `SumProduct` → **zero matches**. The *characters and the non-collapse between them* are built
  (`det2_mul`, `vp_mul`, `two_three_unique`); the finite-cardinality incompatibility statement is not.
  Predicted-buildable (PREDICTION-grade), no witness asserted.
- **Freiman's theorem / generalized AP (GAP) — ABSENT.** grep `Freiman`/`freiman` → **zero matches**; no
  `arithmetic_progression`/`ArithmeticProgression`/`GAP` type (the `AP n` symbol in
  `Real213/ExpLog/LambertPoly.lean` is a Lambert-polynomial coefficient list, NOT an arithmetic
  progression). Flagged predicted-not-built; the structured-set normal form is the additive twin of the
  built `vp_separation` factorization, but the GAP object does not exist.
- **Plünnecke–Ruzsa inequalities — ABSENT.** grep `Plunnecke`/`Plünnecke`/`Ruzsa`/`ruzsa` → **zero
  matches**. The convolution-multiplicativity engine (`mass_conv`) is built; the doubling-constant
  sub-multiplicativity bound is not stated.
- **Szemerédi / van der Waerden — ABSENT** (consistent with `ramsey_theory.md`). grep
  `Szemeredi`/`Szemerédi`/`vanderWaerden` → no field file. Predicted as Ramsey `q+1` on the additive
  sub-family; the density-regularity leg meets the calibrated arbitrary-cover/infinite-quantifier residual
  (`topology.md`/`measure.md`).
- **Cauchy–Davenport — ABSENT.** grep `CauchyDavenport`/`cauchy_davenport` → **zero matches**.
  Predicted-buildable as the additive saturation twin of `sperner_theorem`; no witness asserted.
- No verified false-witness was produced. Every cited theorem was grep-confirmed at the stated `file:line`;
  every cited module was scanned this pass and the load-bearing theorems print `[PURE]`
  (`det2_mul` SternBrocotMarkov 130/0, `legendre_mul` 5/0, `vp_mul` 10/0, `vp_separation` 9/0,
  `two_three_unique` 8/0, `mass_conv`/`momentNum_conv` 20/0, `ResidueTag` 55/0, `FlatOntologyClosure` 7/0,
  `RamseyNamedBound` 13/0, `CountExistence` 10/0, `Pigeonhole` 5/0, `SpernerChains` 50/0).
