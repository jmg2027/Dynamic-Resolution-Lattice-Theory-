# G164 — the HolonomicReal generator: constructive on algebraic AND degree-1 (e)

**Date**: 2026-06-01 (revised). **Status**: finding; the earlier "transcendental
modulus = LEM wall" reading is **corrected below** — e has a total ∅-axiom modulus.
Companion to `Real213/HolonomicReal.lean`, `Real213/ExpLog/EulerModulus.lean`,
`Real213/ExpLog/EulerCertifiedBracket.lean`.

## The question

`HolonomicReal` carries its convergence modulus as a *constructed field*.  The
autonomous case (φ) closed with a total modulus `N(m,k) = 2k`.  Does the general
generator `Holonomic → CertifiedModulus` extend to transcendental rungs (e, π)?

## Correction to the earlier reading

An earlier pass concluded e's total modulus was the LEM wall: `MonotonicBounded`
shows monotone-bounded ⟹ Cauchy needs LEM (the case split "true ∀n" vs "false ∃n"),
which for a transcendental looked like a constructive irrationality measure.

**That bound is for *rate-free* sequences, and e is not one.**  e's convergents
`e_i = eulerNum i / eulerDen i = a_i/i!` carry explicit factorial denominators and a
known tail rate.  That structure gives a total modulus directly — **no LEM, no
irrationality measure** (`EulerModulus.euler_total_modulus`, `N(m,k) = k+2`).

### The mechanism that breaks the wall

Carry the margin invariant `e_i + 1/(i·i!) ≤ m/k` (`euler_inv`).  Its forward step
reduces to `i(i+2) ≤ (i+1)²` (i.e. `0 ≤ 1`, discharged by the `PolyNat` reflection
ring) — the tail estimate is a trivial induction.  At index `k+1` the denominator gap
`|m/k − e_{k+1}| ≥ 1/(k·(k+1)!)` exceeds the future variation `< 1/((k+1)·(k+1)!)`, so
the cut is constant past `k+1` (or `k+2` in the boundary case `m/k = e_{k+1}`).  The
side (`e </> m/k`) is read off the decidable Bool `eulerCut (k+1) m k` — the gap
exceeds the approximation error, which is exactly what a rate-free sequence lacks.

So `eulerCut` is constant past `k+2` uniformly in `(m,k)` (`euler_cut_const`), and
**e is a complete `HolonomicReal`** (`eHolonomicReal`) with a constructed total
modulus, on the same footing as φ.

## Where the generator stands now

  - **Autonomous (algebraic, det-1) class**: total constructive modulus — φ done.
  - **Degree-1 holonomic (e)**: total constructive modulus `k+2` — DONE.
  - **Open frontier**: higher-degree transcendentals (π, degree 4) — their explicit
    convergence-rate modulus — and the *general* `Holonomic → CertifiedModulus` for
    arbitrary recurrence data.  The π case should follow the same margin-invariant
    idea with the Wallis tail rate; the general case wants the rate extracted from
    arbitrary polynomial-coefficient recurrence data (the depth/`polyDepth` link).

The honest lesson: the LEM wall is a property of *rate-free* presentation, not of
transcendence.  A real presented with its convergence rate (any holonomic real, via
its recurrence) escapes it; the open work is *computing* that rate per coefficient
class, not a foundational obstruction.
