# Hyper 213

**Status**: Closed (3 files).

## Overview

213-native handling of "hyper" number systems built on `Raw`
sequences: a hyperreal-like algebra (sequences under cofinite
equivalence), its Lens tower, and p-adic integers as a Lens
sub-family.  The point: structures usually presented via ZFC's
power-set (free ultrafilters for NSA, inverse limits for ℤ_p) are
absorbed framework-internally as sequences-of-`Raw` or Lens families.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberSystems/Hyper/` (3 files)
- **∅-axiom status**: PURE

| File | Topic |
|---|---|
| `Hyper213.lean` | `Hyper213 := Nat → Raw` (no Cauchy modulus); `cofiniteEquiv xs ys := ∃ N, ∀ n ≥ N, xs n = ys n` |
| `Hyper213Tower.lean` | `HyperTower α n := Nat → LensTower α n` — the sequence-large × tower-large axes captured together |
| `Padic.lean` | ℤ_p as `padicFamily p k = leavesModNat (p^(k+1))`, an inverse-limit sub-family of `leavesModNat` |

## Narrative

`Hyper213 = Nat → Raw` is a *looser* construction than `Real213`:
sequences **without** a Cauchy modulus, with **cofinite equivalence**
on top, give a framework-internal algebra of "infinitesimal + finite
+ infinite."  Standard Cauchy is a strict subset (Cauchy with the
same limit implies cofinite equiv once the limit stabilizes).  This
is weaker than the free-ultrafilter quotient of classical NSA, but it
needs no choice principle — the equivalence is reflexive, symmetric,
transitive by direct construction.

`Hyper213Tower` captures two large axes at once, both
framework-internal: the *sequence-large* axis (`Nat → Raw`) and the
*tower-large* axis (`Lens^n α` via recursive self-application).

`Padic` realizes the p-adic integers ℤ_p as the inverse limit of
`ℤ/p^k`, encoded as a sub-family of `leavesModNat` over powers of a
fixed base — prime base gives ℤ_p; general base ≥ 2 gives the
mod-`p^k` Lens tower (= ℤ_p of the prime factors via CRT).

## Tetration and the hyper-operation ladder

Tetration `a ↑↑ b` and the higher hyper-operations are **not** part of
this sub-tree; they are formalized in the Meta/Nat layer:

- `Meta/Nat/HyperLadder.lean` — the hyper-operation ladder
  (`+`, `×`, `^`, `↑↑`, `↑↑↑`, …) with the per-rung recurrence
  `a↑↑(b+1) = a^(a↑↑b)` and unit/fixed-point laws holding at every level.
- `Meta/Nat/UnitTetra.lean` — the rung-4 object for `↑↑`: a cube whose
  dimension is a tower count (`tetra a b`, `a↑↑0 = 1`).
- `Meta/Nat/ExpVector.lean` — `toVec_tetration`, the curved `↑↑` readout.

The "evaluation level" framing (`configCount 2 = 5²⁵`,
`configCountD d n := d ^ (d^n)`, so `5²⁵ = configCountD 5 2 =
configCount 2`, a parametric family with no privileged level) lives in
`Lib/Math/Cohomology/Fractal/ConfigCount.lean`.  A tetration value
exceeding `configCount 2` is read at a different family-evaluation
level, not against a privileged cap (`fractal.md` §7; CLAUDE.md
"Universe-constant framing" failure mode).

## Connection

- `theory/math/numbertheory/dyadic_fsm.md` — FSM-based hyper recursion
- `theory/math/cohomology/fractal.md` — `configCount` family
