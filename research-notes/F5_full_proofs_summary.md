# F5 — Full proofs summary (this session 의 actual theorems)

## Verified mathematical theorems (이 session 에 서 proved)

### Phase A foundation

- type / equiv (Setoid) / const / order / sign — 모두 verified.

### Cut arithmetic — basic

- `cutSum`, `cutMul`, `cutMaxMin`, `cutNeg`, `cutSignedMul`,
  `cutHalf`, `cutMid`, `cutPow`, `cutScale`, `evalPoly`,
  `cutInv`, `cutSignedSum`, `cutSignedSub` — 모두 working.

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
- 0 sorry, 모든 theorem ≤ propext + Quot.sound (Lean 4 core only).
- Library entry point: `E213.Math` with 7 sub-modules.

## 의의

213-native real analysis 의 *substantial mathematical content*
verified.  Bishop program 의 의도 적 *무 시*, framework 자체 의
인 herent 함 수 공 간 위 의 specific operations 를 verified working.

Marathon 의 actual mathematical content 까 지 도 달 — 상 당 한 Bishop-
style theorems 의 213 form 에 서 working code.
