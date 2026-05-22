# DyadicFSM — 213-native Number Theory

**Status**: Closed (78 files, sub-organized 2026-05-13).
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch).  No source G-note; large
multi-session Lean closure.

## Overview

**DyadicFSM** is 213-native number theory expressed as **finite-state
machines on dyadic-encoded integers**.  Pell, Fibonacci, Tribonacci,
Pisano, Legendre, and other classical number sequences are all
realized as Mealy machines on `Bool`-encoded inputs.

The FSM realization is the 213-native equivalent of recursive
definitions: each step is a small finite transition, the result is
the FSM's accumulated state.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/DyadicFSM/` (78 files)
- **Umbrella**: `DyadicFSM.lean`
- **∅-axiom status**: PURE

### Sub-cluster organization

| Sub-cluster | Topic |
|---|---|
| `ArithFSM/` (9 + 3 Mod buckets) | Per-modulus arithmetic FSM (Mod{Small,Medium,Large}) + Hierarchy + Hardness + helpers |
| `Pell/` | Pell sequence FSM (Pell numbers, Pell-Lucas) |
| `Fib/` | Fibonacci FSM (Fibonacci, Lucas, Tribonacci) |
| `Pisano/` | Pisano periods (per-modulus) |
| `Legendre/` | Legendre symbol via FSM |
| `Capstones/` | Master theorems per family |

## The narrative

### FSM as 213-native recursion

Classical recursion (`fact (n + 1) = (n + 1) * fact n`) is hidden
behind Lean's `Nat.rec`.  In 213, the recursion is made **explicit**
as a finite-state machine:

- States = small finite set (often Bool, Fin k, or small Nat)
- Inputs = bits of the dyadic-encoded argument
- Transition = (state, bit) → state
- Output = post-transition state

This makes recursion **decidable in fixed bits**: a sequence value
at input N requires O(log N) FSM steps, each constant-time.

### Pell sequence example

The Pell numbers `P_n = 2·P_{n-1} + P_{n-2}` (P_0 = 0, P_1 = 1)
are realized as a 2-state FSM:
- State = (P_n, P_{n-1}) modulo some bound
- Input bit = which Pell index we're computing toward
- Transition = (a, b) → (2a + b, a)

The Pell FSM proves `P_n` satisfies the Möbius matrix identity
`[[2, 1], [1, 0]]^n = [[P_{n+1}, P_n], [P_n, P_{n-1}]]` directly
at the FSM level.

### Pisano periods

Pisano (n) = period of Fibonacci modulo n.  As an FSM, Pisano (n)
is the FSM's cycle length on the Fibonacci-mod-n transition.
**Decidable in O(n²)** by detecting cycle return to initial state.

`Pisano/` provides per-n decided values for n ≤ ~100, plus
parametric results for prime n (Pisano (p) divides p - 1 or p + 1).

### Connection to other chapters

- `theory/math/universe_chain.md` — Möbius P matrix [[2,1],[1,1]]
  is the Pell-Fib generator; DyadicFSM closes the P^n identities
- `theory/math/cayley_dickson/algebra_tower.md` — algebra-tower
  asymptote rate uses Pisano periods
- `theory/math/real213.md` — Real213 brackets use dyadic encodings

## Open frontier

- **Higher-order recursions** (Tribonacci, k-bonacci) — partially
  done (Tribonacci has FSM); generalization to arbitrary k open
- **Continued fractions** as FSM — sketched, not yet capstoned

## How to verify

```bash
cd lean
lake build E213.Lib.Math.DyadicFSM
python3 tools/scan_axioms.py Lib/Math/DyadicFSM
```
