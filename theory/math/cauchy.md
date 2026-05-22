# Cauchy / Euler / Wallis / Pell Sequences

**Status**: Closed (7 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch).

## Overview

213-native sequence machinery: monotone-bounded convergence,
Archimedean property, profinite sequences, and classical sequence
families (Euler, Wallis, Pell, generic).  All sequence-level
theorems are stated with **explicit moduli** (per ε-δ modulus), not
existential ε-δ.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Cauchy/` (7 files)
- **∅-axiom status**: PURE

| Group | Files |
|---|---|
| Generic + properties | `GenericFamily`, `Properties` |
| Classical families | `Euler`, `Wallis`, `Pell` |
| Convergence | `MonotoneBounded`, `Archimedean` |

## Narrative

Classical Cauchy sequences need an ε-δ predicate.  213's version:

```
Cauchy s := { f : Nat → Nat // ∀ N k l, k ≥ f N → l ≥ f N → |s_k - s_l| < 1/2^N }
```

The modulus `f` is **part of the witness** — no Skolemization
needed.  `MonotoneBounded.lean` proves: every monotone bounded
sequence is Cauchy with explicit modulus.  `Archimedean.lean`
provides the Archimedean property for Real213 cuts.

### Classical families

- **Euler**: e ≈ 2.71828... As `Σ 1/k!` with explicit truncation
  bound
- **Wallis**: π/2 as the Wallis product with explicit bracket
- **Pell**: Pell numbers as DyadicFSM output, used for √2 brackets

These are the **finite-rational bracket** versions of standard
transcendentals — same content, different packaging (per G6 §0
corrected position).

## Connection to other chapters

- `theory/math/real213.md` — Cauchy sequences feed Real213 cuts
- `theory/math/modulus.md` — explicit moduli used here
- `theory/math/dyadic_fsm.md` — Pell sequence via DyadicFSM
- `theory/physics/alpha_em/precision_derivation.md` — Wallis used
  in α_em derivation (S_Wallis bracket)

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Cauchy
```
