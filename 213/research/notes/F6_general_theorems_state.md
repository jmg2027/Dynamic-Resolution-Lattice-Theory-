# F6 — General theorems state (Marathon final)

## 이 wave 의 actual general theorems (NOT just decide tests)

### Algebraic identities

- `cutSum_one_one` : 1 + 1 = 2.
- `cutMul_one_one` : 1 * 1 = 1.
- `cutSum_zero_const` : 0 + a/b = a/b.
- `cutSum_const_zero` : a/b + 0 = a/b.
- `cutMul_one_const` : 1 * a/b = a/b.
- `cutMul_const_one` : a/b * 1 = a/b.
- **`cutSum_self` : c + c = 2c for any const c = a/b** (most general).
- `cutSum_half_half` : 1/2 + 1/2 = 1 (corollary).
- `cutSum_third_third` : 1/3 + 1/3 = 2/3 (corollary).
- `cutSum_half_general` : a/2 + b/2 = (a+b)/2 (same denom 2).
- `cutHalf_constCut` : (a/b)/2 = a/(2b).
- `cutMid_self_constCut` : midpoint(c, c) = c.
- `cutPow_zero/succ`, `partialSum_zero/succ`, `riemannSumOnSamples_zero/succ`
  (rfl-level unfolding lemmas).

### Rational equivalence

- `constCut_scale` : constCut a b = constCut (a*c) (b*c) for c ≥ 1.
- `constCut_one_one_eq` : 1 = a/a for a ≥ 1.
- `constCut_zero_eq` : 0 = 0/b for b ≥ 1.

### Commutativity + monotonicity

- `cutSum_comm`, `cutMul_comm`, `cutSignedMul_comm`.
- `cutSum/Mul_mono_left/right` (4 directions).
- `cutSum/Mul_cutLe_left/right/both` (6 versions).

### Lattice theory (full bounded distributive)

- `cutMax/Min_idempotent`, `_zero_left`, `_assoc`, `_comm`.
- `cutMax_distrib_cutMin`, `cutMin_distrib_cutMax`.
- `cutMax_absorb`, `cutMin_absorb`.
- `cutLe_cutMax_left/right`, `cutLe_cutMin_left/right`.
- `cutMax_lub`, `cutMin_glb`.

### Continuity (locally-determined)

- `cutSum/Mul_locallyDetermined`, `cutBinary` generic.
- `cutHalfLDD`, `cutScaleLDD`.
- `composeLDD` categorical closure.
- `idLDD`, `constLDD`.

### Existential characterizations

- `cutSumAux_eq_true_iff`, `cutMulInner_eq_true_iff`,
  `cutMulOuter_eq_true_iff`.

### Cauchy + Series

- `CauchyCutSeq` + `limit` + `limit_eq_at`.
- `partialSum`, `SeriesCauchy`, `zeroSeriesCauchy`.
- `partialSum_zero_series`.
- `geomHalfSeries`, `expCutPartial`, `sinPartial`, `cosPartial`,
  `leibnizPiPartial`.

### IVT structural + cutEq compat + Cut poset

- `bisectN_zero`, `bisectN_succ_true`, `bisectN_succ_false`.
- `cutSum/Mul_cutEq_left/right/both`.
- `cutEq` refl/symm/trans, `cutLe` refl/trans/antisymm.

### cutDouble

- `cutDouble_constCut`, `cutDouble_zero`, `cutDouble_cutDouble`.

## Total stats (extended marathon)

- 56+ Real213-related Lean modules.
- 60+ commits in this wave.
- All build clean, ≤ propext + Quot.sound (Lean 4 core only).
- Library entry: `E213.Math` with 7 sub-modules.

## 비 verified scaffolded

- Series convergence theorems (full).
- IVT bracket convergence proof.
- Differentiation rules (sum/product/chain).
- Riemann FTC.
- Specific transcendental limit proofs.
- cutSum_assoc as general theorem.
- cutSum × cutMul distributivity.
