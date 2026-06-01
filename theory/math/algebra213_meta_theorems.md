# Algebra213 Meta-Theorems

**Status**: Closed — `Math/Tactic/{Ring213, HurwitzRing, QuadExtension}` infrastructure + Hurwitz layer in SignedCut.

## Overview

Meta-theorems characterising **polynomial-identity proofs** in
Cayley-Dickson rings.  These identities (Hurwitz norm-multiplicativity,
associativity at each level, etc.) are polynomial in 2^N Int variables.
At level 3 (𝕆), Hurwitz `|uv|² = |u|²·|v|²` is an 8-variable identity
with ~100 monomials per side.

The meta-theorem: **classical polynomial-flatten + `simp + omega`
tactics work**, and 213's `Ring213` / `HurwitzRing` / `QuadExtension`
tactics provide the 213-native equivalent without `propext` reliance.

## Lean source

- **Tactic infrastructure** (`Lib/Math/Tactic/`):
  - `Ring213.lean` — base 213-native ring tactic
  - `HurwitzRing.lean` — Hurwitz-norm tactic
  - `QuadExtension.lean` — quadratic-extension tactic
  - `IntSquare.lean` — Int-square supporting lemmas
- **Hurwitz layer** (`Lib/Math/SignedCut/Hurwitz/`):
  - `HurwitzNormProduct.lean` — norm product
  - `HurwitzExactL1.lean` — L1 exact
  - `HurwitzFailure.lean` — failure modes
  - `HurwitzDichotomy.lean` — Hurwitz dichotomy
- **∅-axiom status**: PURE

## Narrative

Classical algebra tactic ecosystems (`ring`, `polyrith`) rely on
propext-tainted decision procedures.  In 213, the Cayley-Dickson
polynomial identity proofs need an equivalent that:

1. Doesn't import `propext`
2. Handles 2^N-variable polynomial identities at level N
3. Closes within reasonable heartbeats for L ≤ 6

`Ring213` provides this as a 213-native term-mode tactic.  The
strategy: flatten to Int polynomial → close via Nat.lt /
Nat.sub_add bridges + decide on small finite checks.  At higher
levels (L ≥ 4), the polynomial size blows up; `HurwitzRing`
specializes for Hurwitz-norm identities (the most common case),
and `QuadExtension` handles quadratic-extension identities.

The Hurwitz layer (`SignedCut/Hurwitz/`) applies these tactics to
get the L = 1 exact ceiling + L ≥ 2 product identities, closing
the algebraic side of the tower.

## Connection to other chapters

- **Algebra tower** (`theory/math/cayley_dickson/algebra_tower.md`):
  uses these tactics for the Order-4 monopoly proofs at L3-L6.
- **Universe chain** (`theory/math/universe_chain.md`): Möbius P
  matrix identities (`P^10 ≡ I mod 5`) use `Ring213` at the
  underlying linear-algebra level.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Tactic
lake build E213.Lib.Math.SignedCut.Hurwitz
```
