# G165 — which reals get a FREE total modulus: the rate-vs-denominator-gap criterion

**Date**: 2026-06-01. **Status**: finding + frontier map.  Companion to
`Real213/ExpLog/EulerModulus.lean`, `Real213/HolonomicReal.lean`.

## The criterion that made e work

e's total ∅-axiom modulus (`euler_total_modulus`, `N(m,k)=k+2`) came from a clean
collision of two quantities at the convergent `e_i = a_i/d_i` (`d_i = i!`):

  - **denominator-gap quantum**: if `m/k ≠ e_i` then `|m/k − e_i| ≥ 1/(k·d_i)`
    (the cross-difference `|m·d_i − k·a_i|` is a positive integer);
  - **tail rate**: `|e − e_i| < 1/(i·d_i)`.

At index `i = k` (and beyond) the tail `1/(i·d_i)` is **smaller** than the gap
quantum `1/(k·d_i)` — because the tail carries an extra `1/i` over the gap.  So the
convergent lands strictly on e's side of `m/k`, the side is read off a decidable
`Bool`, and the modulus is `~k`.  **No irrationality measure needed.**

The general criterion this instantiates:

> **A monotone cut sequence with convergents `a_i/d_i` has a FREE total modulus
> `N(m,k) ≈ k` whenever its tail rate beats its own denominator-gap quantum at index
> `~k`: `tail_i < 1/(k·d_i)` for `i ≳ k`.**

Equivalently `tail_i · k · d_i < 1`.  For e: `tail_i · k · d_i < (1/(i·d_i))·k·d_i =
k/i < 1` for `i > k`.  The factorial rate `1/(i·d_i)` is exactly fast enough.

## Why π-via-Wallis does NOT meet it

`PiCut` uses the Wallis product: convergents `W_n = wallisNum n / wallisDen n` with
`wallisDen` growing fast (a product), but the partial-product tail
`|π/2 − W_n| ~ 1/n` — only *first-order* convergence.  Then `tail_n · k · wallisDen n
~ (1/n)·k·wallisDen n ≫ 1` (the denominator grows far faster than `n`).  The
criterion fails: the convergent is rationally precise (tiny gap quantum) yet far from
`π/2` (tail `~1/n`), so `m/k` can sit on the wrong side until `n > 1/|π/2 − m/k|`.
That threshold needs a lower bound on `|π/2 − m/k|` — **π's irrationality measure**
(famously hard, `μ(π) ≤ 7.1`).  So π-via-Wallis genuinely needs an analytic input e
did not; it is not an e-style "free" modulus.

A *fast* π series (Machin/arctan, or any geometric-rate representation) would meet
the criterion — but none is formalized here yet.  That, not Wallis, is the route to
a free π modulus.

## Frontier map for the `HolonomicReal` generator

  - **FREE total modulus** (`tail · k · d_i < 1` at `i≳k`): the algebraic reals (φ:
    convergents *equal* the closed cut past `2k`) and the **factorial-rate**
    transcendentals — e done.  Likely also `1/e`, `sinh 1 / cosh 1`, and exp/log at
    rationals (factorial tails) — cheap instances if their cut machinery is wired.
  - **NEEDS an irrationality measure** (rate too slow for its denominators): π via
    Wallis.  Route: a fast π series, or π's measure as a separate hard theorem.
  - **General generator**: the criterion `tail_i · k · d_i < 1` is the abstract
    hypothesis under which the `euler_inv` margin argument gives `N(m,k)`.  Abstracting
    `EulerModulus` over `(a, d)` + this hypothesis is the reusable "rate-carrying ⟹
    total modulus" theorem (the depth/`polyDepth` recurrence supplies `d_i`'s growth;
    the rate supplies `tail_i`).  Next concrete step if pursued.

The honest one-liner: **a total constructive modulus is free exactly when the
convergence rate out-runs the denominators; e does, Wallis-π does not, and that — not
transcendence — is the real divide.**
