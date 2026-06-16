# Genuine m_p/m_e rebuild — compute `6·π⁵` from the `PiCut` bracket

**Status**: OPEN (rebuild roadmap). **Domain**: physics (DRLT branch).
**Template**: `research-notes/frontiers/genuine_hodge_rebuild.md` (honesty tone).
**Most concrete of the four rebuilds** — `PiCut` already gives a usable π bracket.

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

### Stage 1 (reachable now) — a genuine computed bracket that excludes 1837

The PiCut localization is too coarse alone (`π ∈ (2.8, 4)` ⇒ `6π⁵ ∈ (1318, ...)`,
useless).  Stage 1 is to **sharpen the Wallis cut** to a window narrow enough that
`6·π⁵` is pinned between two consecutive integers:

1. Extend `PiCut` with a tighter pair, e.g. prove `piCut n 22 7 = true` and
   `piCut n 311 99 = false` at a concrete layer `n = N₀` by `decide` (Wallis
   partial-product `wallisNum N₀ / wallisDen N₀` cross-multiplied), giving
   `π ∈ (311/99, 22/7)` ≈ `(3.14141, 3.142857)`.  Both endpoints are
   `decide`-checkable rationals from the *same* `wallisRawSeq`.
2. Define `piFifth_lower, piFifth_upper : Nat × Nat` by raising the bracket
   endpoints to the 5th power (rational `(num^5, den^5)`), then multiply by
   `NS·NT = 6`.  All exact `Nat` arithmetic.
3. **Target theorem** (the genuine Stage-1 falsifier):
   ```
   theorem mp_me_bracket_excludes_neighbors :
       1836 * piFifth_lower.2 < 6 * piFifth_lower.1     -- 6π⁵ > 1836
     ∧ 6 * piFifth_upper.1 < 1837 * piFifth_upper.2 := by decide
   ```
   i.e. `1836 < 6·π⁵ < 1837`, computed from the Wallis cut with **π never typed**.
   This *excludes* the neighboring integers 1836 and 1837 — a real measurable
   discriminant (the count-Lens reading lands strictly between them).

   Honest scope of Stage 1: this proves `6π⁵ ∈ (1836,1837)`, consistent with
   CODATA `1836.1527`.  It does **not** reach 19 ppm, let alone ppb — the bracket
   width after a feasible `N₀` is ~10⁻²–10⁻³, far wider than the formula's own
   19 ppm gap.  Stage 1 is a *computed* bracket falsifier, the honest replacement
   for the typed `6=6`.

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
