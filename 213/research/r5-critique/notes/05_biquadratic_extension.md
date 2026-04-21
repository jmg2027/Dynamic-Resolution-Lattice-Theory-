# 05 — Biquadratic extensions: scope, design, deferral

## Motivation

The `ZSqrt D` parametric family (see `notes/01` and
`Research/ZSqrt*.lean`) catalogues all imaginary quadratic
integer rings as R4Codomain witnesses for Paper 1's §4 Lens
layer.  The next natural question — **do biquadratic (rank-4)
extensions add new structure?** — leads to e.g. `ℤ[i, √-2]` with
three non-trivial involutions (send `i → -i`, send `√-2 → -√-2`,
or both).

## Two orthogonal directions

### Direction A: biquadratic ring `ℤ[i, √-2]`

An element `a + b·i + c·√-2 + d·i·√-2` with `i² = -1`,
`(√-2)² = -2`, `i·√-2 = √-2·i`.  Multiplication is a 16-term
expansion that closes over the 4-rank lattice.  Three
involutions:

- σᵢ : flips `i → -i` (fixes `√-2`)
- σⱼ : flips `√-2 → -√-2` (fixes `i`)
- σᵢⱼ : flips both (Galois composite)

For R4 we pick one.  **The non-uniqueness of conj** (now
three candidates, whereas `ZSqrt D` had only one) is a new
qualitative phenomenon: R4 is satisfiable in multiple
inequivalent ways.

### Direction B: product codomain `(ZSqrt D₁) × (ZSqrt D₂)`

Componentwise operations.  Easier to implement: just a
product structure.

- `base_a = (I, I)`, `base_b = (negI, negI)`
- `combine` componentwise `(mul, mul)`
- `conj` componentwise `(conj, conj)`

**Yields R12Codomain + R4-style SwapMatching** (componentwise
factors verify).  **But R3 FAILS** —
`(I, 0) * (0, I) = (0, 0)` is a zero divisor.  This is
qualitatively different from `ZMod6Lens`'s R3 failure: here
R4 is preserved but R3 is broken.

## Tractability assessment

- **Direction A** requires building 4-rank arithmetic from
  scratch (no Mathlib).  The `quad_norm` tactic only handles
  rank-2 identities; `normSq_mul` would need a hand-proof
  involving a 16-term polynomial expansion.  Feasible but
  several sessions of work.

- **Direction B** is shallow: ~50 lines of Lean, mostly
  pairing off existing `ZSqrt` lemmas.  Adds the
  *qualitative* R3-fail-while-R4-holds witness to the
  catalogue; this is a genuine gap today.

## Decision

Defer Direction A (heavy arithmetic, adds multiplicity of
conj but this is already clear at the prose level from Galois
theory).  Direction B is folded into future work under
`Research/ZSqrtProduct.lean`; this note records the design.

## Paper 2 implication

The *catalogue-level* observation — "R4 is satisfiable in
multiple ways when the codomain has non-trivial
automorphism group" — strengthens Paper 2 §3.6's point
that the paper's R1–R4 do not uniquely single out an
involution, let alone a codomain.  Biquadratic extensions
exhibit this phenomenon most cleanly; quadratic families
already exhibit it across D.

## Status

- A: deferred (speculative, heavy).
- B: design sketched, implementation queued (Paper 2 §4
  follow-up).
