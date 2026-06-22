# Decomposition: the p-adic numbers ℚ_p (LEVERAGE)

*213-decomposition of ℚ_p, per `../README.md` (model v6: `L` carries a **resolution** parameter;
the prime-valuation reading `vp` is the `×↦+` character; `Residue` = the completion's reached-by-none
limit). Directly continues `continuity.md` (resolution as the organizing axis) and
`prime_factorization.md` (`vp` as the faithful character coordinate). The hypothesis under test:
**ℝ and ℚ_p are the same number-construction — ℚ + a completion-reading — at two resolutions**, the
resolution parameter selecting which, with `vp` supplying the p-adic resolution's modulus.*

## The decomposition

- **Construction `C`** — the **approximation-sequence-with-modulus**, the *same* `C` as
  `continuity.md`'s dyadic refinement tree: a number is not a held object but a sequence of
  narrowing approximants together with a modulus saying how fast they settle. 213 builds *both*
  completions of ℚ from this one shape:
  - the **archimedean** instance is `CauchyCutSeq` — `(cs : Nat→Nat→Nat→Bool, N : Nat→Nat→Nat,
    cauchy)` with `limit m k := cs (N m k) m k` (`Lib/Math/Analysis/CauchyComplete.lean:38`
    `structure CauchyCutSeq`, `:44` `CauchyCutSeq.limit`, `:48` `limit_eq_at`). Resolution measured
    at base `2^{−k}` (a `DyadicBracket` narrowing); the cut/bracket *is* the sequence, so
    completeness is "almost trivial" (file docstring, user insight E1).
  - the **p-adic** instance is `ZpSeq` — `(digits : Nat → ZpDigit p)` read at every truncation
    depth `N` via `trunc x (n+1) = trunc x n + (digits n)·p^n`
    (`Lib/Math/NumberSystems/Padic/Foundation.lean:41` `structure ZpSeq`, `:52` `ZpSeq.trunc`).
    Its limit object is the **diagonal of an approximant sequence** —
    `diagLimit s := fun k => (s k).digits k` (`Foundation.lean:65`), the *identical* "read digit `k`
    off the level-`k` approximant once it has settled" move as `CauchyCutSeq.limit`, certified by
    `diagLimit_trunc_succ` (`Foundation.lean:75`).

  So `C` is one thing: a refinement sequence whose digits/brackets stabilize, plus a modulus. ℝ and
  ℚ_p differ in *one parameter of the reading*, not in the construction.

- **Reading `L_res(base)`** — the **resolution-reading**, exactly `continuity.md`'s dial, with one
  new slot: *which base measures "close"*. "Agree up to resolution `N`" means:
  - **base = the archimedean count** (Real213's `|·|`, brackets at `2^{−k}`) → ℝ;
  - **base = `p^{−N}`** (truncation-agreement mod `p^N`) → ℚ_p.

  The p-adic modulus is literally `vp` read as a distance: `valAtLeast x n` = "every digit `< n` is
  zero" ⟺ `trunc x n = 0` (`Lib/Math/NumberSystems/Padic/Norm.lean:31` `Zp.valAtLeast`, `:44`
  `valAtLeast_iff_trunc`), and the bounded valuation `vAt x N` returns the first-non-zero-digit
  position, `≤ N` (`Lib/Math/NumberSystems/Padic/Valuation.lean:45` `vAt`, `:191` `vAt_le`). High `vp`
  = small p-adic distance = agreement at deep truncation. **The valuation `vp` of
  `prime_factorization.md` is the p-adic resolution's modulus** — the same `×↦+` coordinate, now
  read as "how many factors of `p` separate us" = "at what depth do we still agree". The ultrametric
  is `vp` being that modulus: `valEq_add_of_lt` (`Norm.lean:335`) — when valuations differ the sum
  takes the lower one (the strong triangle inequality) — and `valEq_mul` (`Norm.lean:461`) —
  valuations *add* under product (the `vp_mul` character, `NumberTheory/PrimeValuation.lean:96`,
  now read as `dist(xy) = dist(x)·dist(y)`).

- **Residue** — the completed point: reached by no finite depth `N`, only narrowed to. For ℝ it is
  the `RealCut` limit (`CauchyComplete.lean:44`); for ℚ_p it is the `ZpSeq`/`QpSeq` whose every
  truncation is pinned but which is never a finite object. ℚ_p adds its denominators as the
  localization `QpSeq = (num : ZpSeq p, shift : Nat)` representing `num·p^{−shift}`
  (`Lib/Math/NumberSystems/Padic/Field.lean:28` `structure QpSeq` — explicitly `ℤ_p[1/p]`), the
  field of fractions over the completed integers. Same residue shape as every other completion: a
  finite-signature pointing (the modulus / the digit-stream), never the limit itself.

## Re-seeing

```
   ℝ      =  ⟨ approximant-sequence-with-modulus | L_res(base = archimedean |·|, 2^{−k}) ⟩
   ℚ_p    =  ⟨ approximant-sequence-with-modulus | L_res(base = p^{−N}, i.e. vp) ⟩
   |C|, ℝ-completion        =  CauchyCutSeq + limit            (CauchyComplete.lean:38,44)
   |C|, ℚ_p-completion       =  ZpSeq + trunc/diagLimit         (Foundation.lean:41,52,65)
   "p-adic distance"        =  vp read as a modulus            (valAtLeast_iff_trunc, vAt_le)
   "ultrametric"            =  vp is that modulus              (valEq_add_of_lt, valEq_mul)
   ℚ_p as a field           =  ℤ_p[1/p] localization           (QpSeq = (num, shift), Field.lean:28)
   Residue (both)           =  the reached-by-none limit; finite signature = the modulus
```

The single move: **ℝ and ℚ_p are one `⟨C | L_res(base)⟩`, the `base` slot the only difference.** The
archimedean completion dials `base` to the count's own size; the p-adic completion dials it to
`p^{−vp}`. Nothing else in `C` or `L` changes — Lean builds both from "digit/bracket sequence + a
`Nat→Nat`(`→Nat`) modulus + diagonal/limit extraction".

## LEVERAGE — prediction vs collapse (honest about what's Lean-built)

**Verdict: PREDICTION on the structural axis, not collapse-only.** The calculus does not merely
re-describe ℚ_p; it *predicts the shape of the family of completions* and that prediction matches
what is independently Lean-built.

What the calculus genuinely predicts and Lean certifies:

1. **ℝ and ℚ_p are one construction at two resolutions — built, side by side.** This is the
   load-bearing claim, and it is *not* hand-waved: `CauchyCutSeq` (`CauchyComplete.lean:38`) and
   `ZpSeq` (`Foundation.lean:41`) are the *same* "approximant sequence + modulus" object with the
   *same* diagonal-limit extraction (`CauchyCutSeq.limit` `:44` vs `diagLimit` `Foundation.lean:65`,
   `diagLimit_trunc_succ` `:75`). The only structural difference is the base at which the modulus
   measures closeness. The calculus *predicted* this from `continuity.md`'s "resolution is the
   organizing axis"; the repo built both completions before the decomposition was written, so the
   match is evidence, not construction-to-fit.

2. **`vp` IS the p-adic modulus — proven, not asserted.** The prime-valuation character of
   `prime_factorization.md` (`vp_mul`, `PrimeValuation.lean:96`) is exactly the p-adic resolution's
   modulus: `valAtLeast_iff_trunc` (`Norm.lean:44`) identifies "valuation ≥ n" with
   "truncation-agreement to depth n", and the two distance laws are theorems —
   `valEq_add_of_lt` (`Norm.lean:335`, ultrametric) and `valEq_mul` (`Norm.lean:461`, `dist`
   multiplicative). So "the p-adic distance is `p^{−vp}`" is the `×↦+` character read as a modulus,
   ∅-axiom (Padic INDEX: ~484 PURE / 0 DIRTY). This is the sharpest leverage: the *same* `vp`
   coordinate that gives unique factorization, when dropped into the `L_res` `base` slot, *is* the
   second completion.

3. **Ostrowski flavour — predicted at the right altitude, honestly partial.** The calculus predicts
   the *form* of Ostrowski's theorem: the completions of ℚ are indexed by **which reading you take
   the residue under** — the archimedean count, or one prime's `vp`. That indexing is forced by the
   model: `base` ranges over the available faithful modulus-readings of ℚ, which are precisely
   {the count's size} ∪ {`vp` : `p` prime} (the `vp` family being faithful is
   `prime_factorization.md`'s `vp_separation`). 213 *builds an instance per prime* (`ZpSeq p` is
   parametric in `p`; concrete `i_5`, `i_13`, `√2 ∈ ℤ_7` in `Hensel.lean`) and the archimedean one
   (Real213), so the *enumeration of the family* is realized. **Honest gap:** the
   *completeness/exhaustiveness* half of Ostrowski — "these are the **only** absolute values on ℚ up
   to equivalence" — is **not a Lean theorem**. 213 has each completion as a clean ∅-axiom object and
   the `vp`-family as faithful coordinates, but no `ostrowski_classification` stating the list is
   exhaustive. So the calculus predicts the *flavour and the index set*; the no-others uniqueness is
   conceptual-only.

**Why this clears the re-skin guard (README "revelation rule").** A collapse-only reading would say
"ℚ_p is just another completion, like the reals" — true but empty. The prediction is stronger and
testable: it says (a) the two completions must be *one* `⟨C|L⟩` differing in a single reading
parameter — confirmed by the shared `CauchyCutSeq`/`ZpSeq`+diagLimit machinery; (b) the p-adic
modulus must be *exactly* the `vp` character already built for factorization — confirmed by
`valAtLeast_iff_trunc` + `valEq_mul`; (c) the completion-family must be indexed by the faithful
modulus-readings — partially confirmed (instances built; exhaustiveness open). Three structural
predictions, two Lean-closed, one (Ostrowski exhaustiveness) named as the open target.

### Lean grounding — certified vs conceptual

**Certified (verified by grep this session; PURE per Padic `INDEX.md` ~484 PURE / 0 DIRTY, not
re-scanned here):**
- ℝ completion as sequence+modulus: `Lib/Math/Analysis/CauchyComplete.lean:38` `CauchyCutSeq`,
  `:44` `CauchyCutSeq.limit`, `:48` `CauchyCutSeq.limit_eq_at`.
- ℚ_p integers as digit-sequence read at every depth: `Padic/Foundation.lean:41` `ZpSeq`, `:52`
  `ZpSeq.trunc`; diagonal limit `:65` `Zp.diagLimit`, `:75` `Zp.diagLimit_trunc_succ` (the same
  diagonal-extraction shape as the ℝ limit).
- p-adic distance = `vp` as modulus: `Padic/Norm.lean:31` `Zp.valAtLeast`, `:44`
  `Zp.valAtLeast_iff_trunc`; `Padic/Valuation.lean:45` `vAt`, `:191` `vAt_le`.
- ultrametric / multiplicative distance: `Padic/Norm.lean:335` `Zp.valEq_add_of_lt`, `:461`
  `Zp.valEq_mul`.
- the character supplying the modulus: `Lib/Math/NumberTheory/PrimeValuation.lean:96` `vp_mul`.
- ℚ_p as a field (localization): `Padic/Field.lean:28` `QpSeq` (= `ℤ_p[1/p]`), with
  arithmetic/inv/div incl. non-unit denominators (`invGeneral` `:301`, `divGeneral` `:338`).
- per-prime instances realizing the family: `Padic/Hensel.lean` (`i_5`, `i_13`, `√2 ∈ ℤ_7`);
  Teichmüller `ℤ_p^× ≃ μ_{p−1}×(1+pℤ_p)` (`TeichmullerUnit.lean`).

**Conceptual-only (honest — Lean thin or absent):**
- *Ostrowski exhaustiveness.* No `ostrowski_classification` theorem ("every absolute value on ℚ is
  archimedean or `p`-adic, up to equivalence"). The family is *enumerated and instantiated*, not
  proved *complete*. This is the load-bearing open leg of the leverage.
- *A single theorem "ℝ and ℚ_p are `⟨C|L_res(base)⟩` for two bases".* The shared structure is
  evident at the type level (both = sequence+modulus+diagonal-limit) but there is **no** abstract
  `Completion (base)` functor with `ℝ`/`ℚ_p` as its two instances — the unification is read off
  matching constructions, the way `continuity.md`'s open-preimage weld is conceptual. A
  `Completion`-parametrized-by-modulus-base would close it (the analogue of
  `four_way_modulus_framework`, `continuity.md`).
- *`vp`-as-distance ⟺ archimedean-`|·|`-as-distance as one dial.* Each is built; their identification
  as the same `L_res` at two `base` values is the decomposition's reading, certified piecewise (the
  ℝ modulus `N`, the p-adic `vAt`) not by one bridge lemma.

## Note for the technique — resolution selects the completion (a major generalization)

**Yes — and it is the largest single extension of the resolution axis so far.** `derivative.md` made
resolution select `Δ` vs `d`; `integration.md` made it select `Σ` vs `∫`; `continuity.md` made it the
organizing axis of topology. This decomposition shows the *same* parameter, given a new **`base`
slot**, selects **which completion of ℚ you land in** — ℝ vs ℚ_p. So the resolution reading now spans:

| `L_res` slot setting | what it selects | Lean anchors |
|---|---|---|
| step-1 vs modulus `h→0` | `Δ` vs `d`, `Σ` vs `∫` | `derivative.md`, `integration.md` |
| commutes-with-refinement (condition) | continuity / open / limit | `continuity.md`, `Continuity.lean:28` |
| **base = archimedean vs `p^{−vp}`** | **ℝ vs ℚ_p** | `CauchyComplete.lean:38`, `Foundation.lean:41`, `Norm.lean:335` |

The shape-refinement the README should record: **`L`'s resolution parameter has an inner `base`
slot — *what metric the modulus measures in* — and that slot is filled by a choice of faithful
modulus-reading of the construction.** For ℚ the available bases are exactly {the count's size,
`vp` per prime}, which is *why* the completion family has the Ostrowski shape: the completions are
indexed by the `base`-fillings, i.e. by the faithful modulus-readings. This ties three earlier
findings into one: the resolution axis (`continuity.md`), the `vp`/`×↦+` character
(`prime_factorization.md`), and the faithful-coordinate residue-stratification (`vp_separation`).
The character that gives unique factorization, slotted as a `base`, gives a whole completion — the
deepest cross-tie since "one character read four ways" (README batch 7). The honest edge mirrors
`continuity.md`'s: the *core* (each completion as sequence+modulus, `vp` as the p-adic modulus) is
∅-axiom-built; the *perimeter* (the abstract `Completion(base)` functor and Ostrowski
exhaustiveness) is conceptual, and names two concrete Lean targets:
`completion_parametric_in_modulus_base` and `ostrowski_classification`.
