# G175 — the ∅-axiom boundary of non-holonomicity: FGS has no shadow, the mod-2 obstruction does

**Tier 1 (volatile).**  Branch-1 of the marathon-3 (FGS shape-obstruction recon).  Continues
`G170`/`G173` (the π-non-holonomicity arc).  Deliverable: a precise map of *what the
constructive ∅-axiom setting can and cannot certify about non-holonomicity*, and the concrete
next targets.  A research agent (literature, web) supplied the verdicts; distilled below.

## Verdict (blunt)

1. **The FGS analytic obstruction has no ∅-axiom shadow.**
2. **π is unreachable by it** — it bottoms out at an *open* hypothesis about π.
3. **There IS a second ∅-axiom-reachable obstruction, strictly finer than Klazar's growth
   bound: the Garrabrant–Pak mod-2 forbidden-factor lemma** — but it, too, does not reach π.

So the reachable boundary is `{Klazar growth bound}` (done, `NonHolonomicWitness`) `∪`
`{Garrabrant–Pak mod-2 obstruction}` (a new target); everything finer is analytic, and π
specifically sits beyond *both* behind an open statistical conjecture.

## Why FGS is not ∅-axiom (Q1, Q4)

The Flajolet–Gerhold–Salvy structure theorem (FGS 2005; Flajolet–Sedgewick *Analytic
Combinatorics* VII–VIII): a holonomic sequence's coefficients are a *finite* sum of
`C·ρ⁻ⁿ·n^θ·(log n)^κ` with `ρ` algebraic, `θ ∈ ℂ`, `κ ∈ ℤ≥0` **bounded** (the `log`-power is
capped).  The irreducible ingredients are complex-analytic: Fuchs–Frobenius singularity
classification of linear ODEs, a summability/Stokes mechanism turning *formal* solutions into
analytic ones, and an Abelian/Tauberian transfer between coefficient asymptotics and the OGF's
singularity.  FGS themselves call it "basic complex analysis," and flag that the *discrete*
(Birkhoff–Trjitzinsky) normal form has an **unbridged formal-to-analytic gap** (Wimp–Zeilberger).
There is no finite `ℕ/ℤ` restatement of analytic continuation and Tauberian transfer — so no
∅-axiom shadow.

## Why π is unreachable (Q3)

To run FGS against π one needs π's partial quotients to behave incompatibly with the rigid
holonomic shape — the natural input being that `(aₙ)` is **Gauss–Kuzmin distributed**
(`P(a=k)=log₂(1+1/(k(k+2)))`).  But Gauss–Kuzmin normality is proven for *no* number not built
for the purpose; for π it is **open**, as is even the boundedness of `(aₙ)`.  So the FGS route
for π is not even *conditionally* ∅-axiom-closable — it is closable only modulo an open
ergodic hypothesis, by an irreducibly analytic argument.

## The genuinely reachable new obstruction — Garrabrant–Pak mod 2 (Q2b, Q4)

> **Lemma (Garrabrant; Garrabrant–Pak, "Pattern avoidance is not P-recursive", arXiv:1505.06508).**
> For a P-recursive **integer** sequence `(aₙ)` (`q₀(n)aₙ = Σᵢ qᵢ(n)a_{n−i}`, `qᵢ ∈ ℤ[n]`), the
> mod-2 word `wₙ = aₙ mod 2` **omits some finite binary factor** (its factor complexity is not
> full).  Contrapositive (the falsifier): *any explicit integer sequence whose mod-2 reduction
> contains **every** finite binary word is non-holonomic.*

The proof is elementary 2-adic-valuation combinatorics (`η(n)=v₂(n)`: on a residue class
`n ≡ ℓ mod 2^m` the valuations `v₂(qᵢ(n))` stabilise, forcing the parity pattern; the explicit
forbidden factor is `(0^{k−d}10^k10^{d−1})^{2^m}`).  **No analysis, no choice, no EM** — ∅-axiom
feasible.  It is strictly finer than Klazar: Klazar rejects only super-`(n!)^d` growth; this
rejects parity-rich sequences at *any* growth (including bounded).

**Correction to `G173`'s wording.**  The plain "P-recursive ⟹ eventually periodic mod m" is
**false in general for unbounded sequences** (the `q₀(n)` denominator; Banderier–Luca
arXiv:1903.01986 is a *case study*, not a universal theorem).  The correct unbounded analog is
the *forbidden-factor* (not periodicity) statement above.  The *bounded* case used in `G173`
(bounded P-recursive ⟹ eventually periodic) stands, but as a separate, bounded-only fact.

**Does it reach π?  No.**  It constrains `aₙ mod 2`; π's partial quotients are conjectured
statistically generic (no forbidden factor), so the lemma is vacuous on π.

## Queued ∅-axiom targets (Q5) — concrete, with difficulty

Two explicit non-holonomic witnesses reachable *without* analysis (orthogonal to the
growth route of `NonHolonomicWitness`):

- **Champernowne-parity (via the mod-2 lemma).**  Let `w` be the binary Champernowne word
  (concatenate all binary strings in length-lex order); it is factor-universal by construction,
  so any integer lift is non-holonomic by the contrapositive above.  *Cost:* formalise
  Garrabrant–Pak Lemma 1.2.1 (the 2-adic valuation argument over polynomial-coefficient
  recurrences with `q₀` division) — substantial; needs `v₂` infrastructure (`Meta` has bit/2-adic
  fragments) and the residue-class valuation-stabilisation lemma.

- **Thue–Morse / Sturmian (via bounded + aperiodic).**  A bounded integer sequence equals its
  mod-`M` reduction (`M > sup`); bounded P-recursive ⟹ eventually periodic; so a bounded
  *aperiodic* sequence is non-holonomic.  Thue–Morse (`DyadicFSM/ThueMorse`, repo has the
  definition + finite-period aperiodicity witnesses only) or the Fibonacci/Sturmian word.
  *Cost:* two hard pieces are missing in-repo — (i) **full** Thue–Morse aperiodicity (the
  overlap-free argument; repo has only periods 1–4), and (ii) **bounded P-recursive ⟹ eventually
  periodic** in full (the polynomial-coefficient-periodic-mod-m + finite-ring-state argument;
  the repo has the pigeonhole template for the fixed-map case `d^n mod m`,
  `Cohomology/Fractal/EventualPeriodicity.expSeq_eventually_periodic`, but not the
  varying-coefficient case).  The *C-finite* sub-case (`bounded C-finite ⟹ eventually periodic`,
  fixed finite-state map + pigeonhole) is clean and elementary, but yields only "not C-finite",
  weaker than non-holonomic.

## Update — the bounded route is DONE, and cleaner than the recon expected

The Thue–Morse/Sturmian idea (bounded + aperiodic ⟹ non-holonomic) had two hard pieces (full TM
aperiodicity; bounded-P-recursive ⟹ eventually-periodic, the latter LPO-adjacent).  Both are
**sidestepped** by a sharper observation: a P-recursive recurrence is **homogeneous**, so a
*zero window* (past the leading-coefficient's finitely many roots) forces every later term to
zero.  Hence the criterion needs only *arbitrarily long zero-runs + infinitely many nonzero* —
no periodicity theorem, no LPO, no `funext`.  Built ∅-axiom:

  - `Cauchy/ZeroRunNonHolonomic.zero_run_not_homogRec` (3 PURE) — the criterion.
  - `Cauchy/ZeroRunNonHolonomicWitness.chi_nonHolonomic` (18 PURE) — the **powers-of-two
    indicator** `χ` (bounded `{0,1}`, growing gaps ⟹ long zero-runs, infinitely many `1`s) is
    non-holonomic.  A fuel-structural power-of-two test makes the witness fully constructive.

So the second ∅-axiom non-holonomicity certificate (orthogonal to growth) is **closed**.  Scope:
the zero-run route catches *sparse* sequences (growing zero-gaps), **not** dense aperiodic ones
like Thue–Morse (overlap-free, no long runs) — that case still needs the bounded-periodicity
machinery and remains queued.  The Champernowne/mod-2 (Garrabrant–Pak Lemma 1.2.1) route also
remains queued (needs the 2-adic valuation argument).  Neither reaches π.

## Net for the marathon

The honest π result stands where it was: **classically OPEN, no ∅-axiom closure.**  This recon
makes the *boundary* precise (FGS analytic, no shadow; π behind open Gauss–Kuzmin) and converts
the vague "FGS route" into two concrete, costed ∅-axiom targets (mod-2 forbidden-factor;
bounded-aperiodic) that certify *other* sequences' non-holonomicity — neither reaching π, which
is the genuine open core.  No new Lean shipped on this branch (the disciplined outcome for an
open analytic problem: map the boundary, do not force an unverified proof).

## Sources
- FGS 2005, *On the non-holonomic character of logarithms, powers, and the nth prime function*.
- Garrabrant–Pak, *Pattern avoidance is not P-recursive*, arXiv:1505.06508 (Lemma 1.2.1).
- Banderier–Luca, arXiv:1903.01986 (mod-m periodicity is case-by-case).
- Adamczewski–Bugeaud, math/0511682 (Subspace-Theorem-based, non-elementary, wrong direction).
- MathWorld, *Gauss–Kuzmin Distribution* (unproven for every non-purpose-built constant).
