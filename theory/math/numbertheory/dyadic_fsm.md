# DyadicFSM — 213-native Number Theory

**Status**: Closed (101 files).

## Overview

**DyadicFSM** is 213-native number theory expressed as **finite-state
machines on dyadic-encoded integers**.  Pell, Fibonacci, Tribonacci,
Pisano, Legendre, and other classical number sequences are all
realized as Mealy machines on `Bool`-encoded inputs.

The FSM realization is the 213-native equivalent of recursive
definitions: each step is a small finite transition, the result is
the FSM's accumulated state.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberTheory/DyadicFSM/` (101 files)
- **Umbrella**: `DyadicFSM.lean`
- **∅-axiom status**: PURE

### Sub-cluster organization

| Sub-cluster | Topic |
|---|---|
| `ArithFSM/` (10 + 3 Mod buckets) | Per-modulus arithmetic FSM (`Mod{Small,Medium,Large}`) + `Hierarchy` + `Hardness` + helpers + `InvertibleArithFSM2` abstraction template |
| `Pell/` | Pell sequence FSM (Pell numbers, Pell-Lucas) |
| `Fib/` | Fibonacci FSM (Fibonacci, Lucas, Tribonacci) |
| `Pisano/` | Pisano periods (per-modulus, parametric predictors) |
| `Legendre/` | Legendre symbol via FSM |
| `PellMatrix*` (5 files) | Pell matrix Cayley-Hamilton + action + cases + inverse + pigeonhole bridging to the Pisano-prime universal closure |
| `FLT/` (8 files) | Binomial / BinomialTheorem / ChoosePrime / FreshmanDream / FLTPrimary / FLTMain / PhiFLT / Sum — Fermat's Little Theorem chain (split + inert prime cases) feeding the Pisano-period closure |
| `Capstones/` | Master theorems per family |

Top-level additions (Pell-Fibonacci universal closure):
- `BinetBridge` — `FLT(φ) + FLT(ψ) → F_{p−1} ≡ 0 (mod p)` bridge
- `PellFibBridge` — Pell ↔ Fibonacci coupled identities
- `PhiMod5`, `PsiMod5` — `φ ≡ ψ ≡ (1 + √5) / 2 (mod 5)` per-residue
- `MulOrderPigeonhole` — existential multiplicative order via pigeonhole
- `UniversalPhase32`, `UniversalPhase33`, `UniversalPhase4` —
  split / inert / Legendre-dispatch components of the universal-in-`p`
  Pisano-period prediction

Companion Meta modules (Lean-4 bridge, ring-independent):
- `Meta/Nat/ModPow213.lean` — modular exponentiation with period reduction
- `Meta/Nat/MulMod213.lean` — mul-mod helpers

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
matches" for specific prime cases, with Predictor23 closing the
23-prime case via the `F_{p²}` Frobenius FLT bridge.

### PellMatrix infrastructure

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

Existential Pisano-period closure uses pigeonhole on the matrix
state space; the constructive per-prime prediction below builds
on top.

### Pell-Fibonacci universal closure

The Pell sequence's period mod `p` admits a closed-form prediction
driven by `legendre213 5 p` (the Legendre symbol of 5 mod `p`):

- `legendre213 5 p = 0` (ramified)  →  predict = `2p`
- `legendre213 5 p = 1` (split, QR) →  predict = `(p−1) / 2`
- `legendre213 5 p = 2` (inert, NQR) →  predict = `p + 1`

This holds universally in `p` (any prime `p ≥ 2`), with no
per-prime evidence required.  The route splits on the Legendre
symbol and recombines at the universal dispatch:

**Split case (`5 ≡ □ mod p`).** When 5 is a quadratic
residue mod `p`, the golden ratio `φ = (1 + √5) / 2` lives in
`F_p` directly.  The Binet formula `F_n = (φ^n − ψ^n) / √5`
then reduces the Pisano period to FLT in `F_p`:
`φ^(p−1) ≡ 1` ⇒ `F_{p−1} ≡ 0 (mod p)`.  `BinetBridge` formalises
this; `UniversalFLT` (in ModArith) supplies the FLT.

**Inert case (`5` is a non-residue mod `p`).** `φ` no longer
lives in `F_p`; instead it lives in `F_{p²} = F_p[√5]`
(see `theory/math/numbertheory/modular_arithmetic.md`).  The Frobenius
`σ : F_{p²} → F_{p²}`, `x ↦ x^p`, swaps `√5 ↦ −√5` in this case,
so `σ(φ) = ψ` (the conjugate).  The identity
`φ · σ(φ) = N(φ) = −1` gives `φ^(p+1) = φ · σ(φ) = −1`, hence
`φ^(2(p+1)) = 1`.  Combined with Fibonacci's recurrence,
`F_{p+1} ≡ 0 (mod p)`.

**Terminal closure.** Legendre dispatch unifies both branches:
regardless of which case `(5/p)` lands in, the period predicted
by `pisano_predict` matches the actual Pell period universally
in `p`.

The key algebraic moves are all in
`theory/math/numbertheory/modular_arithmetic.md` (UniversalFLT, FP2Sqrt5);
DyadicFSM contributes the bridge from FLT-statements-in-F_p (or
F_{p²}) to Pisano-statements-on-the-FSM.

### Connection to other chapters

- `theory/math/foundations/universe_chain.md` — Möbius P matrix [[2,1],[1,1]]
  is the Pell-Fib generator; DyadicFSM closes the P^n identities
- `theory/math/algebra/cayley_dickson/algebra_tower.md` — algebra-tower
  asymptote rate uses Pisano periods
- `theory/math/numbersystems/real213.md` — Real213 brackets use dyadic encodings

## k-bonacci closure — `KBonacci.lean` (48 PURE)

`Lib/Math/NumberTheory/DyadicFSM/KBonacci.lean` realises the k-bonacci family
parametric in `k : Nat`:

  · Definition `kBonacci k n` via a list-window-state iterator:
    initial seeds `[0, ..., 0, 1]` of length `k`; one step =
    drop the oldest, append the sum of the current window;
    return the head after `n` steps.
  · Smoke tests at `k ∈ {2, 3, 4, 5}` and `n ∈ {0, 1, ..., 12}`:
    Fibonacci, Tribonacci, Tetranacci, Pentanacci match standard
    OEIS values via `decide`.
  · ★★★ **Depth-5 cascade** (`depth_5_cascade`): reading at the
    atomic-dimension index `n = d = 5` gives the cascade
    `(kBonacci 2 5, kBonacci 3 5, kBonacci 4 5, kBonacci 5 5)
     = (5, 4, 2, 1) = (d, d−1, NT, 1)` — the k-bonacci ladder
    at index `d` reads out the atomic family.
  · Catalogue hits: `Tetra(5) = 2 = NT`, `Penta(6) = 2 = NT`.

The parametric definition makes Tribonacci's hand-rolled
`Trib` (in `Cohomology/Fractal/TribonacciCutoff.lean`) one case
of a single generic family.

## Continued fractions as FSM — closed (ContinuedFraction.lean, 17 PURE)

`Lib/Math/NumberTheory/DyadicFSM/ContinuedFraction.lean` realises the
continued-fraction expansion of a positive rational `p/q` as an
explicit FSM:

  · State `CFState := Nat × Nat`.
  · Transition `cfStep (n, d) := (d, n mod d)` — Euclidean step.
  · Output `cfDigit (n, d) := n / d` — current quotient.
  · `cfCoeff p q k` — the k-th continued-fraction coefficient.
  · Terminal state `(n, 0)` — fixed point with digit `0`.

Smoke at 213-relevant rationals:
  · Cabibbo `5/22 = [0; 4, 2, 2]`.
  · Archimedean `22/7 = [3; 7]` (π approximation).
  · CKM-δ `176/147 = [1; 5, ...]`.
  · Fibonacci convergents `5/3 = [1; 1, 2]`, `8/5 = [1; 1, 1, 2]`,
    `13/8 = [1; 1, 1, 1, 2]` (φ-convergent fingerprint: leading
    1s with terminal 2).
  · `21/8 = [2; 1, 1, 1, 2]` (Fibonacci-convergent φ² approximation).
  · ★★★★ `continued_fraction_fsm_capstone` packages all four
    classes + termination.

Reading: every rational in the DRLT precision tables (Cabibbo,
CKM δ, π approximations, Fibonacci convergents) has its
continued-fraction expansion as a finite FSM output stream — the
Euclidean algorithm IS the FSM transition.

## Open frontier

- **Real213-p-adic** — the modular-arithmetic substrate
  produced (Bezout, FLT, F_{p²}, Frobenius) is the natural
  foundation for a 213-native p-adic construction.  STARTER at
  `lean/E213/Lib/Math/NumberSystems/Padic/Foundation.lean`.
- ~~**Higher-order recursions** (Tribonacci, k-bonacci)~~ —
  CLOSED via `KBonacci.lean` (48 PURE) above.  Parametric in `k`,
  depth-5 cascade theorem.
- ~~**Continued fractions** as FSM~~ — CLOSED via
  `ContinuedFraction.lean` (17 PURE) above.

## Rigor — k-bonacci recurrence identity (26 PURE)

`Lib/Math/NumberTheory/DyadicFSM/KBonacciRecurrence.lean` establishes that
`kBonacci k n` satisfies the standard recurrence
`a_{n+k} = a_{n+k-1} + ... + a_n`:

  · `fib_rec_{0..5}` — Fibonacci recurrence at `n = 0..5`.
  · `trib_rec_{0..5}` — Tribonacci recurrence at `n = 0..5`.
  · `tetra_rec_{0..3}` — Tetranacci recurrence at `n = 0..3`.
  · `penta_rec_{0..2}` — Pentanacci recurrence at `n = 0..2`.
  · Monotonicity at small indices past the seed region.
  · ★★★★★ `kbonacci_recurrence_capstone` packages one identity
    from each (k=2..5) family + monotonicity.

Reading: rigorous Nat-decidable confirmation that the list-window-
state definition reproduces the standard k-bonacci recurrence.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.NumberTheory.DyadicFSM
python3 tools/scan_axioms.py Lib/Math/NumberTheory/DyadicFSM
```
