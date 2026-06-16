# Genuine m_p/m_e rebuild — compute `6·π⁵` from the `PiCut` bracket

**Status**: OPEN (rebuild roadmap), **DOWNGRADED** by a multi-agent panel audit
(2026-06-16). **Domain**: physics (DRLT branch).
**Template**: `research-notes/frontiers/genuine_hodge_rebuild.md` (honesty tone).

> **⚠ Panel verdict (2026-06-16): `m_p/m_e ≈ 6π⁵` is numerology, NOT 213-forced —
> and this roadmap's Stage-1 numbers were wrong.** Two load-bearing corrections:
>
> 1. **Stage 1's bracket claim is numerically FALSE.** `π ∈ (311/99, 22/7)` gives
>    `6π⁵ ∈ (6·(311/99)⁵, 6·(22/7)⁵) = (1835.60, 1839.82)` — which contains 1836,
>    1837 *and* 1838, 1839: it pins `6π⁵` between **no** pair of consecutive
>    integers. The proposed `mp_me_bracket_excludes_neighbors` (`1836 < 6π⁵ < 1837`)
>    is false and would **not** `decide`. The lower endpoint `1835.60 < 1836`, so it
>    cannot even prove `6π⁵ > 1836`.
> 2. **Only `6 = NS·NT` is genuinely atomic; the `π⁵` is a reverse-engineered fit.**
>    The repo carries **two mutually inconsistent** stories for the exponent 5:
>    `ProtonElectronRatio.lean` says "`π⁵ = π·(6ζ(2))²`", `PiFiveGap.lean` says
>    "one π per atomic dim, `d = 5`". Two derivations for one number is the
>    signature of fitting, not forcing (`07_primacy.md` §7.2: this is **fudge**).
>    No Lean theorem derives the exponent; the `vp_separation`-style forcing
>    template is never instantiated. Contrast the genuine α_em spine
>    (`GramStructuralCapstone.invAlphaEm_precision_theorem`), which *computes*
>    `137035999111`; here nothing computes `6π⁵`.
>
> **Honest deliverable**: a *pure-math* computed enclosure of `6π⁵` (reusing
> `piCut_in_14_5_to_4`), explicitly labelled as **NOT** deriving `m_p/m_e`, to
> retire the typed `pi_e9` literal and the tautological `6 ≤ NS·NT ≤ 6` "falsifier".
> The genuine `(1836,1837)` discriminant is a **separate hard sub-project** (see §4):
> it needs a fast π presentation (Machin/arctan) that does not yet exist, and even at
> full precision certifies a 19 ppm *coincidence*, not a derivation.

## 1 — What is deflated, and the bogus mechanism

`lean/E213/Lib/Physics/Hadron/ProtonElectronRatio.lean` claims
`m_p/m_e ≈ NS·NT·π⁵ = 6·π⁵ ≈ 1836.118`.  But every Lean theorem in the file
proves only an **integer skeleton by `decide`**:

```lean
theorem proton_electron_ratio_atomic :
    NS * NT = 6 ∧ d + 1 = 6 ∧ (NS*NT)*(NS*NT)*(NS*NT) = 216 ∧ … := by decide
theorem proton_electron_falsifier :
    NS * NT = 6 ∧ NS * NT ≤ 6 ∧ 6 ≤ NS * NT ∧ (NS*NT)^3 = 216 ∧ … := by decide
```

`π` **never appears as a term**.  The file even concedes it:

> "The relative-agreement figures … '19 ppm', '0.062 ppm', '3 ppm' — are
> informal off-Lean estimates; the Lean theorems below prove only the integer
> atomic skeletons, not a Lean-computed precision."

So the "1836" is **hand-typed in the docstring** and never confronted with a
computed `6·π⁵`.  The `falsifier` clause `6 ≤ NS·NT ∧ NS·NT ≤ 6` is a tautology
(`6 = 6`) — a self-match, not a measurement test.  Compare the genuine α_em
spine (`GramStructuralCapstone.invAlphaEm_precision_theorem`) which **computes**
`137035999111` through a Newton/Gram chain; here nothing is computed.

## 2 — The genuine target

- **Observable**: proton-to-electron mass ratio, `m_p/m_e`.
- **CODATA 2022**: `1836.152673426(32)` (≈ 0.017 ppb measured).
- **213 formula**: `m_p/m_e ≈ NS·NT·π⁵ = 6·π⁵`, with `6 = NS·NT` the S–T spoke
  count of `K_{3,2}^{(c=2)}` (forced by `(NS,NT)=(3,2)`).
- **Numeric of the formula** (off-Lean ground truth): `π⁵ = 306.0196848…`, so
  `6·π⁵ = 1836.1181…` — i.e. the *formula itself* is **19 ppm** from CODATA.
  This is the honest ceiling: `6π⁵` is a coincidence good to ~19 ppm, **not** a
  ppb identity.  No amount of bracket-tightening beats the formula's own error.

## 3 — Why the current Lean fails to DERIVE it

- `π` is absent: the file proves `6=6`, `216=216`, `1296=1296` — arithmetic
  facts about the integer prefactor, never the product `6·π⁵`.
- The "falsifier" excludes nothing measurable: `6 ≤ NS·NT ≤ 6` is `decide`-true
  by definition of `NS·NT`.  A real falsifier must place `6·π⁵` in a window
  **between adjacent integers** (1836 vs 1837), so that a future remeasurement
  landing on the wrong integer would break it.
- The companion `PiFiveGap.lean` (`AlphaEM/`) does carry `6·π⁵`, but via
  `pi_e9 := 3141592654` — **π hand-typed as a rounded literal**, then `decide`d.
  That is a typed-constant self-match, not a constructed cut.

## 4 — Staged plan to COMPUTE `6·π⁵` from the atoms

The construction tool already exists: `Real213/ExpLog/PiCut.lean` packages π as
an `AbCutSeq` (Wallis product) and proves, ∅-axiom, the **localization**
`piCut n 14 5 = false ∧ piCut n 4 1 = true` for `n ≥ 2` — i.e. `π ∈ (14/5, 4)`
— and the sharper half-angle `π/2 ∈ (7/5, 2)`.  These are *computed* rational
brackets from a forced sequence, not typed digits.

### Stage 1 — a genuine computed enclosure of `6π⁵` (math-honest, NOT an m_p derivation)

The PiCut localization is too coarse alone (`π ∈ (14/5, 4)` ⇒ `6π⁵ ∈ (1032.6, 6144)`,
useless).  The honest Stage-1 deliverable is a *computed* rational enclosure of `6π⁵`
from the Wallis cut — replacing the typed `pi_e9` literal — **explicitly not claiming
it derives `m_p/m_e`**.

**Corrected feasibility (panel, 2026-06-16) — the earlier "(1836,1837)" plan was wrong:**

1. A tighter Wallis pair `π ∈ (311/99, 22/7) ≈ (3.14141, 3.142857)` is `decide`-checkable
   — but raising it to the 5th power × 6 gives `6π⁵ ∈ (1835.60, 1839.82)`, a **width ≈ 4.2**.
   This pins `6π⁵` between **no** consecutive integers (it straddles 1836–1839).  So the
   once-proposed `mp_me_bracket_excludes_neighbors : 1836 < 6π⁵ < 1837` is **numerically
   false** and must not be written.
2. To actually pin `6π⁵` strictly inside `(1836, 1837)` needs π to absolute width
   `≈ 3.4×10⁻⁴`.  Wallis converges like `1/(4n)`, so that is `n ≈ 4600` terms; the cut
   integers grow ≈ 1 digit per 1.3 terms (n=100 → ~377-digit), so `n ≈ 4600` means
   ~17 000-digit numerators whose **5th powers** (~85 000-digit `Nat` comparisons) must
   `decide`.  **Infeasible** with kernel `decide`; `native_decide` is forbidden (CLAUDE.md).
   The formula's own 19 ppm target needs ≈ 66 000 Wallis terms — far beyond reach.
3. So Stage 1's *honest* form is just: `wallisLower⁵·6 < 6π⁵ < wallisUpper⁵·6` for a
   feasible small `N₀` (a wide but **computed** enclosure, π never typed), tagged as a
   pure-math bracket on the *number* `6π⁵`, with a docstring stating plainly it does **not**
   bracket the *measured* `m_p/m_e` to any useful precision.  A fast π `AbCutSeq`
   (Machin/`arctan`) — which **does not yet exist** in the repo — would be required for the
   genuine `(1836,1837)` discriminant; Wallis cannot reach it.

### Stage 2 — tighten to the formula's intrinsic 19 ppm

Push `N₀` (or switch to a faster π presentation, e.g. a Machin/`arctan` cut, or
the `PiMeasureModulus` rate-stratified modulus) until the bracket width on
`6·π⁵` is below ~0.04 (i.e. ~19 ppm of 1836).  At that resolution the computed
bracket *brackets CODATA's central value from both sides*.  This is the genuine
end state: `6π⁵` is right to 19 ppm and the Lean bracket certifies exactly that
— no more, no less.

### Stage 3 — the missing-physics question (do NOT fake it)

19 ppm is not ppb.  Either (a) `6π⁵` is a leading-order coincidence and the
residual needs a correction term (an `α_GUT`-style tail, by analogy with the
α_em Gram correction `α²/d²`), or (b) it is exactly a 19 ppm accident.  Stage 3
is to *look for the missing physics*, per CLAUDE.md "Theoretical integrity" — not
to add a hand-tuned constant to force 1836.1527.  Until found, the honest claim
is "`6π⁵`, computed, good to 19 ppm".

## 5 — Honest scope (keep vs replace)

- **Replace (must)**: `proton_electron_ratio_atomic` / `proton_electron_falsifier`
  as the *precision* claim — they prove `6=6`, not `6π⁵`.  The integer-skeleton
  theorems may stay as "the prefactor is `NS·NT`", but must not be presented as
  the ratio prediction.
- **Keep / strengthen**: a Stage-1 computed bracket `6π⁵ ∈ (1836,1837)` IS a
  legitimate DRLT "measurable falsifier bracket" (the DRLT Validation Standard
  accepts a measurable falsifier) — once π is the `PiCut` construction, not a
  literal.
- **Do NOT claim**: ppb or sub-ppm precision.  The formula's own 19 ppm gap is
  the ceiling; no bracket can certify tighter agreement than the formula has.

## 6 — Cross-references (construction tools + the genuine spine)

- `lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/PiCut.lean` — π as `AbCutSeq`,
  `piCut_in_14_5_to_4`, `halfPiCut_in_7_5_to_2` (the bracket machinery to extend).
- `lean/E213/Lib/Math/Analysis/Cauchy/Wallis.lean` — `wallisRawSeq` (the source
  sequence; sharper layers via `decide` at higher `N`).
- `lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/PiMeasureModulus.lean` — a
  rate-stratified modulus for faster π convergence (Stage 2).
- `lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean` — the genuine
  spine that *computes* `137035999111`; the model for "compute, don't type".
- `lean/E213/Lib/Physics/AlphaEM/PiFiveGap.lean` — the `pi_e9` typed-literal
  pattern to be retired in favor of `PiCut`.
- `research-notes/frontiers/headline_precision_scope.md` — the audit that flagged
  these as docstring-numerics-not-theorems.
