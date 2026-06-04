# φ self-similarity — one matrix, three readings, all ∀n ∅-axiom

**Status**: Closed at the ∀n level.  Every claim below is a strict ∅-axiom
Lean theorem (`#print axioms → no axioms`); the citations are the derivation.

## Overview

The golden ratio φ = (1+√5)/2 enters 213 not as an analytic limit imposed from
outside but as the single invariant of one object — the Möbius matrix
`P = [[2,1],[1,1]]`, the algebraic shadow of the residue's self-pointing
(`mobius_self_form_fixed_point.md`).  "Same shape under descent" — what stays
invariant as a structure is refined — is read three ways off `P`, and the three
readings are one self-similarity, not three coincidences:

| reading | content | scale factor | witness (Lean) |
|---|---|---|---|
| **form** | the constructor shape is invariant at every depth; descent terminates at the atoms | — | `Theory/Raw/Lambek.self_similar_floor` |
| **count** | each level replicates the whole; the vertex count multiplies | rational `d = 5 = disc P` | `Lib/Math/SelfSimilarityBridge.self_similar_count` |
| **limit-ratio** | the convergent ratio settles on the matrix's irrational fixed point | irrational `φ` | `…SelfSimilarityBridge.self_similar_ratio_is_phi` |

`d = 5 = NS + NT = disc P` (rational) and `φ` (irrational) are invariants of the
*same* matrix, so the three are one fact: `self_similarity_three_readings`
bundles them.

## 1. Form — same shape under descent (`Theory/Raw/Lambek.lean`)

The most primitive self-similarity is structural, on Raw itself.  A non-atom Raw
refines into two parts, and each part *again* has the atom-or-slash shape, while
its `depth` strictly drops, bottoming out at the atoms:

  - `decompose` — every Raw is `a`, `b`, or `slash x y h` (the constructor shape
    holds at every depth; this is Lambek's forward map `Raw → F(Raw)`).
  - `self_similar_peel` — peeling `x/y` yields two parts that each satisfy
    `decompose`, and `depth x, depth y < depth (x/y)`.
  - `self_similar_floor` — bundles shape-invariance + strict descent + atomic
    floor (`atoms_are_floor : a.depth = 0 ∧ b.depth = 0`).

The "floor" is therefore not where a regress is *stopped* but the shape that is
*invariant under refinement* — a fixed shape, with a terminating descent.

## 2. Count — `5^L` replication (`Lib/Math/SelfSimilarityBridge.lean`)

The count-Lens reading of "each level carries a copy of the whole" is the
universe-chain vertex count `numV L = 5^L`:

  - `self_similar_count : numV (m + n) = numV m * numV n` — the count replicates
    under level addition (the exponential law is exactly self-similarity read by
    the count-Lens); `self_similar_base : numV 2 = numV 1 * numV 1` is the base
    instance.

The scale factor is the rational `d = 5`, the discriminant of `P`
(`disc P = NS + NT = 5`).

## 3. Limit-ratio — φ, pinned and realized as a Cut

The ratio of consecutive terms of the P-orbit does not settle on an integer but
on the irrational fixed point of `P`.  This reading is closed in four steps.

### 3.1 The norm invariant (`Lib/Math/NumberSystems/Real213/PhiNormInvariant.lean`)

The P-orbit numerator/denominator follow the matrix action of `P`:

  - `coupling` / `seq_coupling_{num,den}` — `num_{n+1} = 2·num_n + den_n`,
    `den_{n+1} = num_n + den_n` (by induction on the shared recurrence
    `s(n+2) = 3·s(n+1) − s(n)`).

Under this coupling the single-layer φ-norm equals the consecutive cross-product,
which is the det-1 symplectic invariant:

  - `norm_eq_pell_unit` — `num_n² − num_n·den_n − den_n² = pell_unit_at n`.
  - `phi_norm_eq_neg_one` — `… = −1` for **all** n
    (`mobius_213_pell_unit_invariant_forall`).

Positivity facts the rational comparison needs, all ∅-axiom via the repo's
`Int213.{add_nonneg, mul_nonneg, le_of_add_eq_of_nonneg}` (Lean-core `Int` `≤`
pulls `propext`): `seq_nonneg`, `gap_nonneg`, `seq_den_le` (`den_n ≤ 2·num_n`).

### 3.2 φ is the unique nested-bracket limit (`Lib/Math/NumberSystems/Real213/PhiConvergence.lean`)

The convergents form a *nested, shrinking* sequence of rational brackets, so they
pin a unique value:

  - `convergents_nest` — adjacent cross-products are exactly ±1 (so consecutive
    convergents bracket φ from opposite sides).
  - `pellDen_strictly_increasing` + `bracket_width_shrinks` — gap denominators
    strictly grow, so bracket widths shrink to 0.
  - `phi_is_unique_nested_limit` — nested + shrinking + the layer-2 bracket
    `[3/2, 5/3]` pin the value: it is φ.  `self_similar_ratio_pins_phi` exposes
    this as the strengthened limit-ratio reading.

### 3.3 φ as a single ValidCut (`Lib/Math/NumberSystems/Real213/PhiAsCut.lean`)

φ is not only bracketed; it is a concrete 213-native Cut object, built directly
from `x² = x + 1` with no Cauchy-completion machinery:

  - `phiCut m k := decide (k ≤ 2m ∧ 5k² ≤ (2m − k)²)` — the closed-form decidable
    cut (`m/k ≥ φ`).
  - `phiCut_valid : ValidCut phiCut` — both monotonicities, by direct Nat
    arithmetic.
  - `phiCut_false_of_norm` — if `(2m − k)² + 4 = 5k²` then `phiCut m k = false`
    (`m/k` below φ): the single-layer mechanism behind "a convergent reads below
    φ".

### 3.4 The Fibonacci convergents lie below φ, ∀n (`Lib/Math/NumberSystems/Real213/FibCassiniNat.lean`)

The Pell convergents are the consecutive Fibonacci pair
`(pellNum n, pellDen n) = (fib(2n+2), fib(2n+1))`.  Their below-φ property is
proved natively in Nat (every `Int↔Nat` cast pulls `propext`, so the Int norm of
§3.1 cannot be lifted — the fact is re-proved on `fib` directly), using the
repo's PURE Nat-polynomial tools (`Meta/Nat/PureNat`, `Meta/Nat/NatRing213`):

  - `fib_cassini_norm` — `fib(2n+2)² + 1 = fib(2n+2)·fib(2n+1) + fib(2n+1)²`
    for all n (a Cassini variant; induction over the fib couplings, step reduced
    to the IH via monomial cancellation).
  - `phiform` — converts that norm to the cut form `(2a − b)² + 4 = 5·b²`,
    eliminating `a` via `2a = (2a − b) + b` (additive; needs `den_le :
    fib(2n+1) ≤ 2·fib(2n+2)`).
  - ★ `fib_convergent_below_phi` — `phiCut (fib(2n+2)) (fib(2n+1)) = false` for
    **all** n.  The native-Nat form of "every Fibonacci/Pell convergent is below
    φ" (`PhiCutConvergents.convergents_below_phi` had only layers 0..8 by
    `decide`).

### 3.5 φ as the Cauchy-complete limit object (`Lib/Math/NumberSystems/Real213/PhiCauchyLimit.lean`)

§3.3 pins φ as one closed-form cut; §3.4 shows every convergent sits below it.
The remaining direction — φ built **as** the limit of the convergent sequence —
is now closed, and lands on the *same* object.

  - ★ `FibCassiniNat.cs_eq_phiCut` — for every target `(m, k)` and every layer
    `i ≥ 2k`, the convergent cut value equals the closed-form cut:
    `decide (fib(2i+2)·k ≤ fib(2i+1)·m) = phiCut m k`.  This is **stronger than
    Cauchy**: the sequence is eventually *constant* and equal to `phiCut`.  The
    modulus is honest and pure-Nat — squaring the cross-comparison collapses the
    entire √5 analysis to the single condition `fib(2i+1) > 2k`, reached at
    `i = 2k` by the Archimedean bound `fib_lb` (`i + 1 ≤ fib(2i+1)`).  Case A
    (target `≥ φ`) is `true` at every layer (`cs_true_of_ineqs`, cut-order
    transitivity through φ in squared-norm form); case B (target `< φ`) is
    `false` past the modulus (`cs_false_of_below`/`cs_false_of_small`, the strict
    mirror).
  - `PhiCauchyLimit.phiConvergentSeq` — the convergent cut sequence assembled as
    a `CauchyCutSeq` (`Analysis/CauchyComplete`) with explicit modulus
    `N(m, k) = 2k`; the `cauchy` field is immediate from `cs_eq_phiCut`.
  - ★ `PhiCauchyLimit.phiCauchy_limit_eq_phiCut` — `phiConvergentSeq.limit m k =
    phiCut m k`.  The limit object built by completion **is** the closed-form
    cut, pointwise.
  - ★ `PellFibCutBridge.pellConvergentCut_eq_phiCut` — the **canonical**
    `Int`-seq-defined Pell convergent cut (`PhiCut.pellConvergentCut`, the object
    `PhiCut`/`PhiConvergence` work with) stabilizes to `phiCut` for every target
    at every layer `i ≥ 2k`.  Transported from `cs_eq_phiCut` through the PURE
    bridge `pellNum_eq_fib`/`pellDen_eq_fib` (`pellNum n = fib(2n+2)`,
    `pellDen n = fib(2n+1)` ∀n) — proved by 2-step induction over the shared Pell
    recurrence, the `toNat` read-out collapsing by `rfl` once the `Int` seq is
    pinned to a `natCast`.

So φ is now constructed two ways that agree on the nose: directly as one
decidable `ValidCut` (§3.3), and as the Cauchy-complete limit of the rational
Pell convergents (§3.5) — on **both** the native-`fib` sequence and the canonical
`pellConvergentCut`.  The residue's irrational limit-ratio signature is one
213-native Cut, however it is approached.

## The single statement

`SelfSimilarityBridge.self_similarity_three_readings` bundles form + count +
limit-ratio.  φ is the matrix's irrational fixed point, `d = 5` its
discriminant; the descent that keeps the same shape (`self_similar_floor`)
converges to φ because φ is `P`'s fixed point — so "the felt snag of an endless
refinement" is the experience of that single self-fixed-point, now a theorem.

## Boundary — what this is not

  - φ is built **both** closed-form (§3.3) and by Cauchy completion (§3.5), and
    the two coincide pointwise (`phiCauchy_limit_eq_phiCut`).  The completion runs
    on the native-Nat convergent sequence `fib(2i+2)/fib(2i+1)`; the **canonical**
    `Int`-seq-defined `PhiCut.pellConvergentCut` inherits the same stabilization
    through the PURE bridge `PellFibCutBridge.pellNum_eq_fib`/`pellDen_eq_fib`
    (`pellNum n = fib(2n+2)`, `pellDen n = fib(2n+1)` ∀n) — see
    `pellConvergentCut_eq_phiCut`.  The earlier "no PURE Int→Nat bridge" caveat is
    cleared: `(↑n).toNat = n` is `rfl`, so the `toNat` read-out is harmless once
    `P_numerator.seq n` is pinned to a `natCast` by 2-step induction over the
    shared Pell recurrence.
  - The `pellNum`-stated `PhiCutConvergents.convergents_below_phi` stays at
    layers 0..8 (`decide`); its ∀n upgrade lives in the native-Nat
    `fib_convergent_below_phi`, because `pellNum n := (P_numerator.seq n).toNat`
    is an Int→Nat cast and the repo has no PURE such bridge.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.NumberSystems.Real213 E213.Lib.Math.SelfSimilarityBridge E213.Theory.Raw.Lambek
python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Real213.FibCassiniNat
python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit
python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Real213.PellFibCutBridge
python3 tools/scan_axioms.py E213.Lib.Math.SelfSimilarityBridge
```

## Citation guidance

- ✅ this chapter — primary narrative for the φ self-similarity result.
- Lean source of truth: `Theory/Raw/Lambek`, `Lib/Math/SelfSimilarityBridge`,
  `Lib/Math/NumberSystems/Real213/{PhiNormInvariant, PhiConvergence, PhiAsCut, FibCassiniNat}`.
- Larger frame (CD / universe-chain / GRA / Raw towers as readings of the same
  P-orbit): `theory/essays/tower_atlas.md`.
