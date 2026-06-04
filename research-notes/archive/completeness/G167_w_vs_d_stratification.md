# G167 — W-vs-d stratification: completeness as a two-growth-axis comparison

**Date**: 2026-06-01.  **Status**: closed ∅-axiom result + agenda response.
**Source of truth**: `lean/E213/Lib/Math/Real213/RateStratification.lean` (12 PURE / 0
DIRTY).  **Narrative**: `theory/math/analysis/holonomic_modulus.md` §4.
**Anchors**: `Real213/RateModulus` (`Htel`, `Htel_of_crossdet`, `rate_total_modulus`),
`Cauchy/DepthFloorDetOne` (the det-1 floor `W ≡ 1`), `G166` (tower-native agenda).

## The agenda this answers

The research proposal "Intensional Reduction of Transfinite Ordinals" asks (Phase 2)
for a **층별 완비성 정리 / free-modulus stratification**: stratify the space by the
layer where the inequality comparing the cross-determinant growth `W` to the
denominator's discrete growth `d` flips truth value, *without* depending on any
individual real's measure `μ`.  This is exactly `G166`-T1 (the exponential-overtake
boundary layer).  The deliverable is the comparison made the primitive object.

## What was already there

`Htel_of_crossdet` (in `RateModulus`) reduced the rate certificate `Htel` to a
smallness law on the cross-determinant `W_i = a_{i+1}d_i − a_i d_{i+1}`:

    i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}.

But it was stated as a one-way *implication* (smallness ⟹ certificate), and the
"floor is the free bottom" / "overtake breaks it" picture lived only in prose
(`DepthFloorDetOne` for `W ≡ 1`; `DepthDoubleExp`/`DepthExponentRecursion` for the
exponential overtake).

## What this note closes

`RateStratification.lean` makes the smallness law the primitive predicate
`Dominates W d i := i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}` and proves:

  1. **`htel_layer_iff_dominates`** — per layer, the `Htel` inequality ⟺ `Dominates`.
     Both margin sides share the term `i(i+1)·(a_i·d_{i+1})`; cancelling it (PURE
     `NatHelper.le_of_add_le_add_left` — the Lean-core cancel is propext-dirty) leaves
     exactly the W-vs-d comparison.
  2. **`htel_iff_dominates`** — globally, `Htel a d` ⟺ every layer `i ≥ 1` is
     dominated.  This **upgrades `Htel_of_crossdet` from implication to
     characterization**: completability *is* the W-vs-d comparison read at every
     layer, not a yes/no fact about a real.
  3. **`dominated_free_modulus`** — domination everywhere ⟹ total ∅-axiom modulus
     `N(m,k)=k+2` (composes with `rate_total_modulus`).
  4. **`overtake_breaks_layer`** — the negative direction (T1's boundary): *any* layer
     where `W` overtakes the denominator quantum, `(i+1)·d_{i+1} < W_i`, is **not**
     dominated.  The margin increases there; the certificate fails.  No irrationality
     measure — just the two growth axes flipping order.  Fully general over `d`, `W`.
  5. **The unimodular floor is the trivially-free bottom.**  `floor_dominates_all`:
     `W ≡ 1` (the `DepthFloorDetOne` invariant of `T = [[2,1],[1,1]]`, `det T = 1`)
     against `d_i = (i+1)(i+2)` is dominated at *every* layer — the comparison
     `i(i+1)·1 + i·d_i ≤ (i+1)·d_{i+1}` collapses to the identity
     `(i+1)(i+2)(i+3) = [i(i+1) + i(i+1)(i+2)] + 2(i+1)(i+3)`, i.e. `i ≤ i+2`
     (discharged by `Meta.Nat.PolyNat`).  `floor_carries_Htel`: any presentation whose
     cross-determinant is the unimodular floor carries its own rate certificate
     unconditionally.  `tower_stratification` bundles (5)+(2)+(4).

## Why this matches the proposal's three Phases

  - **Phase 1 (단모듈러 원자 대수의 고차 환 확장).**  The atomic `T = [[2,1],[1,1]]`
    (det 1) is the floor whose cross-determinant invariant is the constant `W ≡ 1`
    (`DepthFloorDetOne.depth_floor_is_det_one`).  Here it is the *bottom of the
    stratification*: `floor_carries_Htel` shows the unimodular floor is the
    structurally-free completion point — the scale-invariant shift's fixed invariant
    is exactly what makes the rate certificate trivial.
  - **Phase 2 (내부 성장축 좌표 비교법 W vs d).**  `Dominates` is the cross-det/denom
    coordinate comparison; `htel_iff_dominates` is the **free-modulus stratification
    theorem** — the comparison decides completability layer by layer, depending on no
    measure `μ` of an individual real.
  - **Phase 3 (리우빌 모서리와 소용돌이 정렬).**  `overtake_breaks_layer` is the
    abstract collision point: where the diff-axis explosion of `W` overtakes the
    recursion-axis growth of `d`, domination fails.  The Liouville corner
    (`DepthLiouvilleCoord`: `W ~ c^{k!}` while the denominator grows polynomially) is
    the concrete instance where the overtake bites — its formal home is the existing
    `DepthLiouvilleCoord`/`DepthDoubleExp`; `overtake_breaks_layer` is the general law
    that says any such overtake is a boundary, and no level is privileged (the
    boundary is a coordinate, read off the comparison, not a wall).

## What remains genuinely open (next ∅-axiom targets)

  - A **concrete cut sequence** `a` realizing the unimodular floor against `floorDen`
    with `hmono`/`hmonoS`, so that `dominated_free_modulus` fires end-to-end on a named
    real (φ already completes with closed-form modulus `N=2k`; the point would be a
    second floor instance built *from* the stratification rather than bespoke).
  - The **Liouville overtake made concrete**: instantiate `overtake_breaks_layer` on
    `DepthLiouvilleCoord.fact`-driven `W` vs a polynomial denominator, exhibiting the
    explicit boundary layer.  (`overtake_breaks_layer` already supplies the general
    law; what is missing is the named `W`/`d` from a Liouville presentation as num/den.)
  - **Closure of the dominated class under `+`/`×`** (G166-T3): is `Dominates`
    preserved by the tower's arithmetic?  If so, a whole family follows from the floor
    and e for free.
