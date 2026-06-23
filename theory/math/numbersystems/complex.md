# Complex 213

**Status**: Closed (4 files).

## Overview

Complex numbers `ℂ` in 213 as
`ComplexCut := (Nat → Nat → Bool) × (Nat → Nat → Bool)`, a
`(real, imag)` pair of Cut functions — L1 of the Cayley-Dickson
tower on the `Cut`-level reals.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberSystems/Complex/` (4 files)
- **∅-axiom status**: PURE

## Narrative

`ComplexCut := (Nat → Nat → Bool) × (Nat → Nat → Bool)` — the
`(real, imag)` pair of Cut functions (`re := z.1`, `im := z.2`).
The tuple **is** the number: the two axes are real, and the `+` in
`a + bi` is not ℕ's `+`.  Operations as standard complex arithmetic:

```
(a + bi)(c + di) = (ac − bd) + (ad + bc)i
```

realized by `cAdd`/`cMul` on the component cuts.  No new substrate
primitive; ℂ is the first Cayley-Dickson level on `Cut`.

Classical residue theory needed for α_em C5 reduces to
finite-bracket sums in this representation.

## Connection to other chapters

- `theory/math/numbersystems/signed_cut.md` — L1 base
- `theory/math/algebra/cayley_dickson/algebra_tower.md` — L2 of tower
