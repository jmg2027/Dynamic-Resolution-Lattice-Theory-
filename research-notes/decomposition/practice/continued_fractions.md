# Decomposition: continued fractions and Diophantine approximation

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`).
This is the **purest instance of the residue doctrine** (`../SYNTHESIS.md` §3, the infinity
clause; `theory/essays/foundations/the_form_of_the_residue.md` "Infinity is the residue's
shape, not a god above it"): a continued fraction is literally the approximant-sequence
pointing at an irrational — the convergents `pₙ/qₙ` are the **modulus** (the computable
operand), the irrational is the **residue**, reached by none. Sharpens `golden_ratio.md`
(φ = [1;1,1,…], the slowest CF), and ties to `padic.md` (completion = the modulus closing)
and `modular_forms.md` (the Stern–Brocot/Manin period side).*

## The decomposition

- **Construction `C`** — the **directed-count pair under the continuant fold**. A convergent
  is a pair `(pₙ, qₙ)` (the difference-Lens carrier of `integers.md`), and the construction is
  the **2-term linear re-entry** that grows the next pair from the previous two:

  ```
     p(n+2) = a(n+2)·p(n+1) + p n ,   q(n+2) = a(n+2)·q(n+1) + q n
  ```

  — `cfP_rec` / `cfQ_rec`, ∅-axiom. This is the **same 2-term fold as Fibonacci / the golden
  recurrence** (`golden_ratio.md`): the all-1s partial quotients `aₙ ≡ 1` give exactly the
  Fibonacci convergents `1/1, 2/1, 3/2, 5/3, 8/5, …` (`fib_table`), and the all-2s quotients
  give the √2-CF = Pell convergents `1/1, 3/2, 7/5, 17/12, …` (`Sqrt2ContinuedFraction.q_eq_P`,
  `p_eq_H`). The partial-quotient sequence `[a₀;a₁,a₂,…]` *is* the construction-history; each
  `aₙ` is one re-entry of the fold. Equivalently `C` is the matrix product
  `∏ᵢ [[aᵢ,1],[1,0]]` whose `(1,1)`-entry is the continuant `K[a₁,…,aₙ]`
  (`Continuant.continuant_eq_contMatProd`).

- **Reading `L_ratio` at residue resolution** — project each pair to its **ratio** `pₙ/qₙ`
  (cross-multiplied, division-free), read at the **residue resolution** (the `derivative.md`
  parameter): not "adjacent at step 1" but "adjacent via a modulus, the bracket shrinking."
  The finite generator is the recurrence (`C`) plus the **honest total modulus**
  `N(m,k) = k+2`: `cf_universal_total_modulus` proves the even convergents of *any* real `≥ 1`
  carry a free total ∅-axiom modulus, packaged as a genuine `CauchyCutSeq` (`cfCauchySeq`).
  The limit is never the operand; the modulus is.

- **Residue, tagged `q = ±1`** — the **irrational itself**, reached by no convergent. Three
  facets, all `Nat`/`Int`-certified:
  - **the unimodular tag `(−1)ⁿ`.** Consecutive convergents satisfy
    `p(n+1)·q n − p n·q(n+1) = (−1)ⁿ` (`cf_determinant`) — the cross-determinant is a unit at
    every layer (`cf_det_sq`: `Wₙ² = 1`). This `±1` is the `ResidueTag.multiplier`
    (`multiplier_unimodular`); the two signs are `golden_ratio.md`'s
    `cassini_law_one_at_two_multipliers`. **q = +1 (converge):** the SL₂-step is conjugate
    closure — periodic-pattern quotients, the quadratic-irrational pole (φ, √2). **q = −1
    (escape):** the alternating overshoot/undershoot — the convergents straddle the limit,
    `even` below / `odd` above, never landing.
  - **reached by none.** No convergent lands on the irrational; the limit is *outside every
    convergent's image* — the literal `object1_not_surjective` / `distinguishing_always_leaves_residue`
    signature applied to a *converging* pointing (`golden_ratio.md`'s
    `dynamic_approaches_never_reaches_frozen` is the φ instance).
  - **coprimality.** `cf_coprime`: the determinant Bézout witness forces `gcd(pₙ,qₙ)=1` — each
    convergent is already in lowest terms, the optimal pointing carries no slack.

## Re-seeing

```
   "(pₙ,qₙ)"           =  ⟨ directed count-pair | — ⟩                  (C, before any reading)
   p(n+2)=a·p(n+1)+p n =  the 2-term linear fold  =  Fibonacci/golden recurrence
   convergent pₙ/qₙ    =  ⟨ continuant fold | L_ratio ⟩  (discrete res.)   the MODULUS
   the irrational      =  Residue(L_ratio, C)                          reached by none
   completion          =  L_ratio at residue res. (modulus N(m,k)=k+2)  cf_universal_total_modulus
   "p(n+1)qn−pnq(n+1)=(−1)ⁿ" =  the q=±1 residue tag at every layer    cf_determinant
   best approximation  =  the optimal pointing at each resolution      unimodular_best_approximation
   [a₀;…] periodic     =  q=+1 closing pointing (quadratic irrational)  φ=[1;1,…], √2=[1;2,2,…]
   [a₀;…] aperiodic    =  q=−1 escaping pointing                       golden_aperiodic / disc>0
   Stern–Brocot tree   =  mediant subdivision of unimodular symbols    manin_unimodular_decomposition
```

The single move: a continued fraction is **not** "a way to write an irrational" — it **is**
the construction `C` (the 2-term continuant fold), and the irrational is its **residue** under
the ratio reading at residue resolution. The convergents are the residue's *finite signature*
(the modulus), the computable operand 213 calculates with; the irrational is never an operand.

## Revelation (collapse + forcing + the residue-doctrine spine)

**Collapse 1 — the CF recurrence IS the Fibonacci/golden fold.** `cfP_rec`/`cfQ_rec` is the
same 2-term linear re-entry as `golden_ratio.md`'s `T(p,q)=(2p+q,p+q)` / the Pell-Fibonacci
`a(n+2)=3a(n+1)−a(n)` (`Mobius213ContinuedFraction`). φ = [1;1,1,…] is the `aₙ≡1` instance
(`fib_table`); √2 = [1;2,2,…] is the `aₙ≡2` instance whose convergents are the Pell solutions
of `x²−2y²=±1` (`Sqrt2ContinuedFraction.cf_norm`). "φ is special" and "√2 is special" both
collapse to *one* unimodular CF fold read at two constant partial-quotient values — the
slowest-shrinking residue (all-1s) being φ, the deepest re-entry.

**Collapse 2 — the unimodular tag `(−1)ⁿ` IS the q=±1 residue bit.** `cf_determinant` is the
iterated form of the Stern–Brocot/Farey adjacency `mediant_adjacent_both` (`bc−ad=1` preserved
under mediant), which is the SL₂(ℤ) unimodularity the continuant cross-determinant accumulates.
The `±1` is `ResidueTag.multiplier` (`multiplier_unimodular`); periodicity = the q=+1 closing
pole, aperiodicity = the q=−1 escaping pole. This is the **same** `±1` column as
Cantor/Gödel/φ/Gaussian (`SYNTHESIS.md` §3) — the CF is that spine made fully concrete on a
*number*.

**Forcing — the best-approximation property is the optimal pointing, derived not asserted.**
`unimodular_best_approximation`: at the unimodular floor `W=1` (the CF/Farey case), **no
rational with denominator `< d_i + d_{i+1}` lies strictly between consecutive convergents** —
so the convergents are *optimal* best approximations, the constructive core of the Dirichlet
`μ≥2` floor. The general `denominator_lower_bound` shows interposing any fraction costs
denominator `≥ (d_i+d_{i+1})/W`: the cross-determinant `W` (the residue's shape) **is** the
best-approximation deficiency. The convergent is *forced* to be the best pointing at each
resolution — exactly as `ChebyshevLower.chebyshev_constant_interval` narrows a horizon constant
by sharpening a bracket. The modulus narrowing IS the math.

**The spine — the residue doctrine made fully concrete.** A continued fraction is the cleanest
witness that **the limit is the residue's shape, not a god above it** (`SYNTHESIS.md`, the
infinity clause). The convergents `pₙ/qₙ` are the computable modulus; the irrational is the
residue, **reached by none, pointed at by all** — `cf_universal_total_modulus` makes *every*
real `≥1` a `CauchyCutSeq` through its own CF (`cfCauchySeq`), even the transcendental
`coth(1/q) = [q;3q,5q,…]` (`cothUnitCFCauchySeq`, `coth1_anchors`). No new primitive: the CF
is (the modulus/approximant pointing) + (the 2-term linear fold) + (the q=±1 periodic/aperiodic
tag). The irrationality of the *value* is not a hole in the *derivation* (CLAUDE.md
"Transcendental-as-exterior"): the discrete fold is closed and PURE; only the value-cut is
reached-by-none.

**Stern–Brocot = the modular-forms period contour.** The mediant tree
(`mediant_strictly_between`, `mediant_adjacent_both`, `mediant_cross_diff`) is the *same*
unimodular-subdivision as the Manin modular-symbol decomposition
(`manin_unimodular_decomposition`: a det-±1 symbol splits at the mediant into two det-±1
children) — `modular_forms.md`'s period side. CF convergents and modular-symbol periods are
one Stern–Brocot walk read two ways (a number's approximants vs a geodesic's unimodular pieces).

## VALIDATE verdict — **EXTEND** (deepest confirmation of the residue doctrine; one PREDICTION leg)

No new primitive, no break. The CF slots entirely into the v7.1 model: `C` = the 2-term
continuant fold (direction/`q=±1` + fold-height carried), `L` = ratio at residue resolution
(the modulus), `Residue` = the irrational tagged `q=±1`. It is the **purest** instance of the
infinity doctrine in the notebook — the modulus/limit split is not interpretive here but
*literally built* (`cfCauchySeq` is the convergent sequence as a `CauchyCutSeq`). It
consolidates `golden_ratio.md` (same fold), `padic.md` (same "completion = modulus closing"
shape, archimedean base), and `modular_forms.md` (same Stern–Brocot contour) under one object.

**One PREDICTION leg (honest):** Lagrange's theorem — *quadratic irrational ⟺ eventually
periodic CF* — is grounded only at the *witness/dynamic* altitude, not as a named biconditional.
What is built: the **periodic-pattern quadratic instances** (φ=[1;1,…], √2=[1;2,2,…] with their
constant quotients and Pell norm `cf_norm`), and the **dynamic periodic/aperiodic dichotomy**
on the SL₂ iterator — `golden_aperiodic` (`disc=5>0` ⟹ the boost has infinite order, never
returns = q=−1 escape) vs the elliptic finite-order spectrum `finite_order_divides_twelve` /
`crystallographic_spectrum` (`disc<0` ⟹ periodic floor = q=+1). The *general* "every quadratic
irrational has eventually-periodic CF, and conversely" theorem (a `cf_eventually_periodic_iff_quadratic`)
is **absent** — predicted-not-built, the named open leg.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**The 2-term fold (= Fibonacci/golden recurrence) — `ContinuedFractionConvergents` (23/0 PURE):**
- `lean/E213/Lib/Math/NumberTheory/ContinuedFractionConvergents.lean:77` `cfP_rec`,
  `:88` `cfQ_rec` — `p(n+2)=a(n+2)·p(n+1)+p n` (and `q`), the 2-term linear fold.
- `:185` `fib_table` — `aₙ≡1` gives Fibonacci convergents `1/1,2/1,3/2,5/3,8/5`.
- `:201` `piCF` / `:208` `pi_table` — `[3;7,15,1]` ⟹ `3/1,22/7,333/106,355/113` (Milü).

**The q=±1 unimodular tag — same file + `ContinuedFractionFloor` (17/0 PURE):**
- `ContinuedFractionConvergents.lean:115` `cf_determinant` — `p(n+1)qn−pnq(n+1)=(−1)ⁿ`.
- `:167` `cf_coprime` — consecutive convergents coprime (Bézout from the determinant).
- `lean/E213/Lib/Math/NumberSystems/Real213/ContinuedFraction/ContinuedFractionFloor.lean:104`
  `cf_det_sq` (`Wₙ²=1`, universal unit), `:87` `cf_det_step` (`W(n+1)=−Wₙ`),
  `:189` `cfDet2_even`, `:140` `cfQn_fib`.
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:86` `multiplier_unimodular`,
  `:228` `residue_tag_two_poles`, `:180` `golden_is_converge` (55/0 PURE).
- `lean/E213/Lib/Math/Algebra/CassiniUnimodular.lean:163`
  `cassini_law_one_at_two_multipliers` (the q=±1 two-pole law).

**Best approximation = optimal pointing — `BestApproximation` (2/0 PURE):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Modulus/BestApproximation.lean:46`
  `denominator_lower_bound` — interposing a fraction costs denominator `≥(d_i+d_{i+1})/W`.
- `:74` `unimodular_best_approximation` — at `W=1`, convergents are optimal (`k≥d_i+d_{i+1}`),
  the constructive core of Dirichlet `μ≥2`.

**The modulus / reached-by-none completion — `ContinuedFractionModulus` (23/0 PURE):**
- `lean/E213/Lib/Math/NumberSystems/Real213/ContinuedFraction/ContinuedFractionModulus.lean:203`
  `cf_universal_total_modulus` — every real `≥1` completes through its CF, modulus `N(m,k)=k+2`.
- `:248` `cfCauchySeq` — the convergent sequence as a genuine `CauchyCutSeq`.
- `:271` `cothUnitCFCauchySeq`, `:278` `coth1_anchors` — the transcendental `coth(1/q)=[q;3q,5q,…]`
  completes unconditionally (the CF pointing is universally rate-carrying).

**The residue (reached by none) — `FlatOntologyClosure` (7/0 PURE):**
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective`,
  `:47` `object1_injective` (faithful yet never total = the residue).

**Stern–Brocot / mediant = Manin period contour — `Mediant` (11/0) + `MinkowskiModularSymbol` (5/0):**
- `lean/E213/Lib/Math/NumberTheory/Mediant.lean:54` `mediant_strictly_between`,
  `:77` `mediant_adjacent_both` (SL₂ unimodularity preserved), `:119` `mediant_cross_diff`,
  `:105` `mediant_lowest_terms`.
- `lean/E213/Lib/Math/NumberSystems/Real213/Minkowski/MinkowskiModularSymbol.lean:52`
  `manin_unimodular_decomposition`, `:59` `root_symbol_unimodular`.

**√2 CF = Pell solutions — `Sqrt2ContinuedFraction` (12/0 PURE):**
- `lean/E213/Lib/Math/NumberTheory/Sqrt2ContinuedFraction.lean:65` `q_eq_P`, `:84` `p_eq_H`,
  `:89` `cf_norm` (`pₙ²−2qₙ²=(−1)^{n+1}`).

**Continuant (matrix/palindrome) — `Continuant` (26/0 PURE):**
- `lean/E213/Lib/Math/NumberSystems/Real213/ContinuedFraction/Continuant.lean:60` `continuant_cons2`
  (Euler recurrence), `:131` `continuant_eq_contMatProd`, `:232` `continuant_reverse` (palindrome),
  `:243` `continuant_last_strict_mono`.

**Lagrange / periodicity dichotomy (PREDICTION-leg witnesses) — `GoldenAperiodic` (3/0) +
`FiniteOrderSpectrum` (29/0):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Phi/GoldenAperiodic.lean:57` `golden_aperiodic`
  (`disc>0` ⟹ infinite order = q=−1 escape).
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/FiniteOrderSpectrum.lean:503`
  `finite_order_divides_twelve`, `:603` `crystallographic_spectrum`, `:527` `no_order_five`
  (`disc<0` ⟹ periodic floor = q=+1).

**Scan tallies (`python3 tools/scan_axioms.py <module>`, from repo root):**
`ContinuedFractionConvergents` 23/0 · `ContinuedFractionFloor` 17/0 · `ContinuedFractionModulus` 23/0
· `BestApproximation` 2/0 · `Mediant` 11/0 · `Sqrt2ContinuedFraction` 12/0 · `Continuant` 26/0 ·
`MinkowskiModularSymbol` 5/0 · `GoldenAperiodic` 3/0 · `FiniteOrderSpectrum` 29/0 ·
`FlatOntologyClosure` 7/0 · `ResidueTag` 55/0. All PURE, 0 DIRTY.

## Dropped / flagged

- **Lagrange's theorem as a named biconditional — predicted-not-built.** No
  `cf_eventually_periodic_iff_quadratic` (or any "quadratic irrational ⟺ eventually periodic
  CF") theorem exists in the tree (grep-confirmed: no `periodic`/`Lagrange` hits under
  `Real213/ContinuedFraction`). The claim is grounded only via constant-quotient quadratic
  *instances* (φ, √2) and the *dynamic* periodic/aperiodic SL₂ dichotomy (`golden_aperiodic`
  vs `finite_order_divides_twelve`). Stated as the open leg, not asserted.
- **No claim that "modulus degree = irrationality measure `μ`."** `BestApproximation`'s own
  docstring flags this overclaim: `μ` is a `limsup` (itself a reached-by-none boundary cut).
  Only the rigorous deficiency `W` = best-approximation cost is cited.
- **Buildable witness (verified TRUE + decidable, proposed):** a `decide`-checkable Hurwitz/φ
  smoke for the *worst* approximability — for φ's convergents, `5·(qₙ·(pₙ − φ·qₙ))` style
  bounds need `Real213` (not pure `decide`), so **not** proposed as a pure-`decide` lemma.
  Instead, a clean decidable witness already in-pattern: the **mediant→convergent bridge** at
  a fixed depth, e.g. `cfP piCF 3 * cfQ piCF 2 − cfP piCF 2 * cfQ piCF 3 = 1`
  (`pi_det_smoke:217`, verified PURE by `decide`) and `fib_det_smoke:197` — both confirmed
  true and terminating. No false count-inequality is asserted (the determinant identities and
  `denominator_lower_bound` were each checked at file:line and scanned PURE).
