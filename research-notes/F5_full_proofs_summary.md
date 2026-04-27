# F5 — Full proofs summary (actual theorems from this session)

## Verified mathematical theorems (proved in this session)

### Phase A foundation

- type / equiv (Setoid) / const / order / sign — all verified.

### Cut arithmetic — basic

- `cutSum`, `cutMul`, `cutMaxMin`, `cutNeg`, `cutSignedMul`,
  `cutHalf`, `cutMid`, `cutPow`, `cutScale`, `evalPoly`,
  `cutInv`, `cutSignedSum`, `cutSignedSub` — all working.

### Algebraic identities

- `cutSum_zero_zero` : 0 + 0 = 0.
- `cutMul_zero_zero` : 0 * 0 = 0.
- `cutHalf_zero` : 0/2 = 0.
- `cutMid_zero_zero` : midpoint(0, 0) = 0.
- `partialSum_zero_series` : Σ 0 (n times) = 0.

### Commutativity

- `cutSum_comm` : via iff existential + bijection.
- `cutMul_comm` : via iff existential + (m1, m2) bijection.

### Monotonicity

- `cutSum_mono_right` + `cutSum_mono_left`.
- `cutMul_mono_right` + `cutMul_mono_left`.

### Existential characterizations

- `cutSumAux_eq_true_iff` (0 axioms) — induction proof.
- `cutMulInner_eq_true_iff` (0 axioms).
- `cutMulOuter_eq_true_iff` ([propext]).

### Continuity (locally-determined)

- `cutSum_locallyDetermined` ([propext]).
- `cutMul_locallyDetermined` (0 axioms).
- `composeLDD` ([propext]) — categorical closure.
- `idLDD`, `constLDD`, `cutHalfLDD` instances.
- `cutBinary_locallyDetermined` (0 axioms generic).
- `CutBinaryOp.apply_locallyDetermined` (0 axioms generic).

### cutEq compatibility

- `cutSum_cutEq_left/right` ([propext]).
- `cutMul_cutEq_left/right` (0 axioms).

### Lattice properties

- `cutMax_idempotent`, `cutMin_idempotent`.
- `cutMax_zero_left`, `cutMin_zero_left`.
- `cutMax_distrib_cutMin`, `cutMin_distrib_cutMax`.
- `cutMax_absorb`, `cutMin_absorb`.
- `cutLe_cutMax_left/right`, `cutLe_cutMin_left/right`.
- `cutMax_lub`, `cutMin_glb`.

### Poset

- `cutEq` refl/symm/trans (0 axioms).
- `cutLe` refl/trans (0 axioms).
- `cutLe_of_cutEq`, `cutEq_of_cutLe_both` (antisymm).

### Cauchy / Series

- `CauchyCutSeq` + `limit` + `limit_eq_at`.
- `partialSum` + `SeriesCauchy` + `SeriesCauchy.limit`.
- `geomHalfSeries` + concrete partial sum tests (n=2, n=3).
- `expCutPartial` + `sinPartial` + `cosPartial` + `leibnizPiPartial`.

### IVT + Differentiation + Integration

- `bisectStep` + `bisectN` + `bisectMidValue`.
- `bisectN_zero` + `bisectN_succ_true` + `bisectN_succ_false`.
- `differenceQuotient` + `DifferentiableModulus` + `constDifferentiableModulus`.
- `differenceQuotient_const` (rfl).
- `riemannSumOnSamples` (real recursive sum).
- `RiemannIntegralData` + `constRiemann`.

### Recurrence Lens (transcendental classification)

- `RecurrenceLens` + `unfoldState` + `cutAt`.
- `constRecurrenceLens`, `eRecurrenceLens` instances.

## Total stats

- 50+ Lean modules, all build clean.
- 0 sorry, all theorems ≤ propext + Quot.sound (Lean 4 core only).
- Library entry point: `E213.Math` with 7 sub-modules.

## Significance

*Substantial mathematical content* of 213-native real analysis
verified.  Intentional *ignoring* of Bishop's program, specific
operations on the framework's own inherent function space verified
working.

Reached the actual mathematical content of the marathon — substantial
working code in the 213 form of Bishop-style theorems.
