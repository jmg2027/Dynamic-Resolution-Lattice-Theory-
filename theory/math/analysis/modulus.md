# Modulus Combinators

**Status**: Closed (10 files, capstone `Modulus.Capstone`).

## Overview

The **ε-δ discrete depth modulus** replaces classical ε-δ
convergence with explicit `HasModulus` predicates on Real213 cuts.
This makes all convergence statements **decidable** in 213 by
exhibiting the modulus function directly, rather than asserting
its existence.

`zeta_modulus = identityDepthModulus` (used in α_em C5 chapter)
is the canonical example.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Analysis/Modulus/` (10 files)
- **Capstone**: `Modulus/Capstone.lean`
- **∅-axiom status**: PURE

| Group | Files |
|---|---|
| Core predicate | `HasModulus`, `HasModulusBoundsExtra`, `StrongModulus` |
| Diagonal / depth / info | `DiagonalHasModulus`, `DiagonalIrrelevance`, `DepthCompleteness`, `InfoClosure` |
| Concrete witnesses | `PellHasModulus`, `Translation` |
| Capstone | `Modulus.Capstone` |

## Narrative

Classical real analysis hides convergence behind existential
quantifiers (`∀ ε > 0, ∃ δ > 0, ...`).  In 213, this hides
decidability behind unrealizable Skolemization.  The 213-native
approach: provide the `δ` (or `N`, or `L`) as an explicit
function.

```
HasModulus s := ∀ N, ∃ δ : Nat, ∀ k ≥ δ, |s_k| < 1/2^N
```
becomes
```
HasModulus s := { f : Nat → Nat // ∀ N k, k ≥ f N → |s_k| < 1/2^N }
```

The function `f` is the modulus.  `StrongModulus` requires the
function to be **monotone**; `DiagonalHasModulus` provides the
diagonal trick to convert sequence-of-sequences moduli into
single-sequence moduli; `DepthCompleteness` shows that any
classically-converging sequence in 213's substrate has a
computable modulus.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Analysis.Modulus
python3 tools/scan_axioms.py Lib/Math/Analysis/Modulus
```

## Citation guidance

- ✅ `theory/math/analysis/modulus.md`
