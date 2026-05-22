# DyadicFSM — 213-native Number Theory

**Status**: Closed (101 files; universal-Pisano marathon merged 2026-05-22).
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch).  No source G-note; large
multi-session Lean closure.  Universal-Pisano marathon (Parts 28-58) closed
the Pisano-period theorem for Pell universal in the prime `p`
via FLT + Frobenius in `F_{p²} = F_p[√5]`.

## Overview

**DyadicFSM** is 213-native number theory expressed as **finite-state
machines on dyadic-encoded integers**.  Pell, Fibonacci, Tribonacci,
Pisano, Legendre, and other classical number sequences are all
realized as Mealy machines on `Bool`-encoded inputs.

The FSM realization is the 213-native equivalent of recursive
definitions: each step is a small finite transition, the result is
the FSM's accumulated state.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/DyadicFSM/` (101 files)
- **Umbrella**: `DyadicFSM.lean`
- **∅-axiom status**: PURE

### Sub-cluster organization

| Sub-cluster | Topic |
|---|---|
| `ArithFSM/` (10 + 3 Mod buckets) | Per-modulus arithmetic FSM (Mod{Small,Medium,Large}) + Hierarchy + Hardness + helpers; universal-Pisano marathon added `InvertibleArithFSM2` (Phase 2 abstraction template) |
| `Pell/` | Pell sequence FSM (Pell numbers, Pell-Lucas) |
| `Fib/` | Fibonacci FSM (Fibonacci, Lucas, Tribonacci) |
| `Pisano/` | Pisano periods (per-modulus, parametric predictors) |
| `Legendre/` | Legendre symbol via FSM |
| `PellMatrix*` (5 files, 2026-05-22 marathon) | Pell matrix Cayley-Hamilton + action + cases + inverse + pigeonhole — Phase-3-bridge infrastructure for universal-Pisano marathon Pisano-prime universal closure |
| `FLT/` (8 files, universal-Pisano marathon Phase 3.2-3.3) | Binomial / BinomialTheorem / ChoosePrime / FreshmanDream / FLTPrimary / FLTMain / PhiFLT / Sum — Fermat's Little Theorem chain for Pisano closure |
| `Capstones/` | Master theorems per family |

universal-Pisano marathon top-level additions (Pell-Fibonacci universal closure):
- `BinetBridge` — `FLT(φ) + FLT(ψ) → F_{p−1} ≡ 0 (mod p)` bridge
- `PellFibBridge` — Pell ↔ Fibonacci coupled identities
- `PhiMod5`, `PsiMod5` — `φ ≡ ψ ≡ (1 + √5) / 2 (mod 5)` per-residue
- `MulOrderPigeonhole` — existential multiplicative order via pigeonhole
- `UniversalPhase32` — Phase 3.2 universal in prime `p` (Binet → mod-p FLT)
- `UniversalPhase33` — Phase 3.3 universal: `F_{p²} = F_p[√5]` Frobenius FLT
- `UniversalPhase4` — Phase 4 terminal closure via Legendre dispatch

Companion Meta modules (Lean-4 bridge, ring-independent):
- `Meta/Nat/ModPow213.lean` — modular exponentiation with period reduction
- `Meta/Nat/MulMod213.lean` — mul-mod helpers (Phase 2 prerequisites)

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
parametric **Predictor** files (Predictor8/11/14/17/20/22/23) that
prove the bridge "predicted period from prime p ⇒ Pisano period
matches" for specific prime cases.  Predictor23 (2026-05-22)
closed the 23-prime case via the Phase-3 bridge.

### PellMatrix infrastructure (Phase 1-2-3 of universal-Pisano marathon)

The Pell sequence's matrix realization [[2,1],[1,0]]^n is upgraded
from per-step FSM transitions to a **matrix-level Cayley-Hamilton +
action + inverse + pigeonhole** structure:

- `PellMatrix` — 2×2 integer matrix base + Cayley-Hamilton identity
- `PellMatrixAction` — group action of P^n on pellCoeff state space
- `PellMatrixCases` — case-by-case behaviour at small n
- `PellMatrixInverse` — invertibility of P (det = ±1) + universal
  `stepInv_step` proof
- `PellMatrixPigeonhole` — existential Pisano period via pigeonhole
  (state space finite → must collide → collision = period)

Closes universal-Pisano marathon Phase 2 (existential Pisano period); paves Phase 3
(constructive prediction per prime).

### universal-Pisano marathon — Pell-Fibonacci universal closure (Phase 3.2/3.3/4)

The Pell sequence's period mod `p` admits a closed-form prediction
driven by `legendre213 5 p` (the Legendre symbol of 5 mod `p`):

- `legendre213 5 p = 0` (ramified)  →  predict = `2p`
- `legendre213 5 p = 1` (split, QR) →  predict = `(p−1) / 2`
- `legendre213 5 p = 2` (inert, NQR) →  predict = `p + 1`

universal-Pisano marathon closes this universally in `p` (any prime `p ≥ 2`), no
per-prime evidence required.  The route splits at Phase 3.2 and
recombines at Phase 4:

**Phase 3.2 (split case, `5 ≡ □ mod p`).** When 5 is a quadratic
residue mod `p`, the golden ratio `φ = (1 + √5) / 2` lives in
`F_p` directly.  The Binet formula `F_n = (φ^n − ψ^n) / √5`
then reduces the Pisano period to FLT in `F_p`:
`φ^(p−1) ≡ 1` ⇒ `F_{p−1} ≡ 0 (mod p)`.  `BinetBridge` formalises
this; `UniversalFLT` (in ModArith) supplies the FLT.

**Phase 3.3 (inert case, `5` is a non-residue mod `p`).** `φ` no
longer lives in `F_p`; instead it lives in `F_{p²} = F_p[√5]`
(see `theory/math/modular_arithmetic.md` universal-Pisano marathon section).  The
Frobenius `σ : F_{p²} → F_{p²}`, `x ↦ x^p`, swaps `√5 ↦ −√5` in
this case, so `σ(φ) = ψ` (the conjugate).  The identity
`φ · σ(φ) = N(φ) = −1` gives `φ^(p+1) = φ · σ(φ) = −1`, hence
`φ^(2(p+1)) = 1`.  Combined with Fibonacci's recurrence,
`F_{p+1} ≡ 0 (mod p)`.

**Phase 4 (terminal closure).** Legendre dispatch unifies both
branches: regardless of which case `(5/p)` lands in, the period
predicted by `pisano_predict` matches the actual Pell period.
This closes the original universal-Pisano marathon conjecture universally in `p`.

The key algebraic moves are all in
`theory/math/modular_arithmetic.md` (UniversalFLT, FP2Sqrt5);
DyadicFSM contributes the bridge from FLT-statements-in-F_p (or
F_{p²}) to Pisano-statements-on-the-FSM.

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
- **Real213-p-adic** — the modular-arithmetic substrate
  universal-Pisano marathon produced (Bezout, FLT, F_{p²}, Frobenius) is the natural
  foundation for a 213-native p-adic construction.  STARTER at
  `lean/E213/Lib/Math/Padic/Foundation.lean`; campaign plan at
  `research-notes/G122_real213_padic_research_direction.md`.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.DyadicFSM
python3 tools/scan_axioms.py Lib/Math/DyadicFSM
```
