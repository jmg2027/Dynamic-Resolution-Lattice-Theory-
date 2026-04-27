# F6 — General theorems state (Marathon final + extension)

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

### Cauchy completeness — closed under cut ops (Phase F)

CauchyCutSeq closed under SIX cut operations, each with a limit
theorem proving the limit operation commutes:

- `CauchyCutSeq.cutMax` / `cutMax_limit`.
- `CauchyCutSeq.cutMin` / `cutMin_limit`.
- `CauchyCutSeq.cutDouble` / `cutDouble_limit`.
- `CauchyCutSeq.cutHalf` / `cutHalf_limit`.
- `CauchyCutSeq.cutSum` / `cutSum_limit` (uses maxModulus + cutSumAux_congr).
- `CauchyCutSeq.cutMul` / `cutMul_limit` (uses maxNAt + cutMulOuter_congr).

Cauchy lattice structure at limit:
- `cutMax_self_limit`, `cutMin_self_limit` (idempotent).
- `cutMax_comm_limit`, `cutMin_comm_limit`.
- `cutMax_assoc_limit`, `cutMin_assoc_limit`.
- `cutMax_distrib_cutMin_limit`, `cutMin_distrib_cutMax_limit`.

Cauchy ring-like at limit:
- `cutSum_comm_limit`, `cutMul_comm_limit`.

Plus `cutDouble_cutHalf_comm_limit`.

### cutDouble distributive (Phase G)

- `cutDouble_cutSum` : cutDouble (cutSum cx cy) = cutSum (cutDouble cx) (cutDouble cy).
- `cutDouble_cutMid` : 2 * midpoint = midpoint of doubles.
- `cutSumAux_cutDouble` (helper).

These are the FIRST cut-level mixed-op distributivity theorems.

### IVT structural + cutEq compat + Cut poset

- `bisectN_zero`, `bisectN_succ_true`, `bisectN_succ_false`.
- `cutSum/Mul_cutEq_left/right/both`.
- `cutEq` refl/symm/trans, `cutLe` refl/trans/antisymm.

### cutDouble

- `cutDouble_constCut`, `cutDouble_zero`, `cutDouble_cutDouble`.
- `cutSum_self_eq_cutDouble` : cutSum c c = cutDouble c on constants.
- `cutDouble_cutHalf_comm` : cutDouble ∘ cutHalf = cutHalf ∘ cutDouble.
- `cutHalf_cutHalf_constCut`, `cutDouble_cutDouble_constCut`.
- `cutDouble_cutEq`, `cutDouble_cutLe` : preservation of order/equiv.
- `cutHalf_cutEq`, `cutHalf_cutLe` : same for cutHalf.

### cutMid composition

- `cutMid_int_int` : midpoint(a/1, c/1) = (a+c)/2.
- `cutMid_int_half` : midpoint(a/1, c/2) = (2a+c)/4.
- `cutMid_half_int` : midpoint(a/2, c/1) = (a+2c)/4.

### cutHalf/cutDouble × cutMax/cutMin commute (rfl-trivial)

- `cutHalf_cutMax`, `cutHalf_cutMin`.
- `cutDouble_cutMax`, `cutDouble_cutMin`.

### cutSum associativity (NEW — Phase D)

- `cutSum_int_int_three` : (a + b) + c = (a+b+c)/1.
- `cutSum_int_int_three_right` : a + (b + c) = (a+(b+c))/1.
- `cutSum_int_assoc` : (a+b)+c = a+(b+c) on integer constants.
- `cutSum_half_three`, `cutSum_half_three_right`, `cutSum_half_assoc`.

### partialSum closed forms

- `partialSum_pointwise_eq` : pointwise-equal series have equal sums.
- `partialSum_const_int (a n)` : Σ_{i<n} (a/1) = (n*a)/1.
- `partialSum_const_half (a n)` : Σ_{i<n+1} (a/2) = ((n+1)*a)/2.
- `partialSum_ones` : Σ_{i<n} 1 = n.
- `partialSum_halves` : Σ_{i<n+1} 1/2 = (n+1)/2.
- `partialSum_const_one/two/three_int/three_half` : per-n closed forms.

### cutSignedSum closed forms

- `cutSignedSum_pos_int`, `cutSignedSum_neg_int`,
  `cutSignedSum_pos_half`.

### cutInv / cutAbs / cutNeg

- `cutInv_cutInv` = id.
- `cutNeg_cutSignedMul_left/right` : sign distributes over signed mul.
- `cutNeg_cutSignedSum` : sign distributes over signed sum.
- `cutAbs_cut`, `cutAbs_cutNeg`, `cutNeg_cutAbs` : abs/neg algebra.
- `cutAbs_signedConstCut`, `cutAbs_cutSignedMul` :
  abs distributes over signed mul.

### cutSignedMul on constants

- `cutSignedMul_one_one_pos` : (+1)(+1) = +1.
- `cutSignedMul_one_one_neg` : (−1)(−1) = +1.
- `cutSignedMul_pos_neg` : (+1)(−1) = −1.
- `cutSignedMul_zero_zero` : (+0)(+0) = +0.
- `cutSignedMul_one_const_pos` : (+1)(+a/b) = +(a/b).

### cutPow on simplest constants

- `cutPow_zero_succ` : 0^(n+1) = 0 for any n.
- `cutPow_one_n` : 1^n = 1 for any n.

### cutMax/cutMin × cutEq / cutLe (NEW)

Real213CutLatticeEq.lean — full substitution structure:

- `cutMax_cutEq_left/right/both`, `cutMin_cutEq_left/right/both`.
- `cutMax_cutLe_left/right/both`, `cutMin_cutLe_left/right/both`.

12 theorems mirroring cutSum/cutMul's compatibility coverage.

## Total stats (extended marathon + Phase D + E)

- 62+ Real213-related Lean modules.
- 100+ commits across the full marathon.
- All build clean, ≤ propext + Quot.sound (Lean 4 core only).
- Library entry: `E213.Math` with 7 sub-modules.  CutOps now imports
  SumOne / MulOne / MidSelf / PowConst / ConstCutScale / ScaleLattice
  / LatticeEq / SignedMulConst.  Series imports SeriesConst.

### Phase E summary

- Lattice eq/le compatibility (12 theorems).
- Signed mul on const cuts (5 theorems).
- cutPow on 0 and 1 (inductive, all n).
- cutSum_assoc on integer/half constants.
- partialSum closed forms (inductive).

### Phase F summary (Cauchy completeness)

- CauchyCutSeq closed under cutMax, cutMin, cutDouble, cutHalf,
  cutSum, cutMul (6 lifted ops).
- Each comes with a limit-commutation theorem.
- Helpers: maxModulus / maxNAt for finite-range modulus computation.
- Corollaries: idempotent at limit, double-half commute at limit.
- Bounded distributive lattice structure at limit (comm/assoc/
  distrib/idempotent — 8 theorems).
- Commutative arithmetic at limit (cutSum_comm, cutMul_comm).

### Phase G summary (mixed-op distributivity)

- cutDouble distributes over cutSum (universal).
- cutDouble distributes over cutMid (composed).
- cutSumAux_cutDouble (induction on iteration index).

### Phase H summary (Cauchy cutMid + const closed forms)

- CauchyCutSeq.cutMid + cutMid_limit (7th lifted op).
- constCauchy_cutSum_int / half closed forms.
- constCauchy_cutMul_one_one closed form.
- CauchyCutSeq.cutDouble_cutSum_limit (mixed-op distributivity at
  Cauchy limit).

### Phase I (LATEST — IVT framework foundation)

ValidCut + RatioCut infrastructure for IVT:

- structure ValidCut : upM (m-monotone) + dnK (k-anti-monotone).
- constCut_valid : constCut is ValidCut.
- cutMax/Min/Half/Double/Sum_valid : closure under common ops.
- cutMid_valid : cutHalf ∘ cutSum closure.

- structure RatioCut : ratioMono (rational-ordering monotonicity,
  k1 ≥ 1 hypothesis).
- constCut_ratio : constCut is RatioCut.

cutMid pointwise monotonicity (Real213CutMidMono.lean):
- cutLe_a_cutMid_at : a ≤ cutMid a b at fixed (m, k) with k ≥ 1.
- cutLe_cutMid_b_at : cutMid a b ≤ b symmetric.

Bracket containment foundation (Real213IVTContainment.lean):
- cutLeAt cx cy m k : pointwise cutLe at fixed (m, k).
- cutLeAt_refl, cutLeAt_trans.
- bisectStep_contains : 1-step bracket containment.

### IVT open problems

- **n-step bracket containment**: needs RatioCut closure under cutMid
  (or cutSum), blocked by precision artifact at tight m1*k2 = m2*k1
  with k1 ≥ 2.
- **Bracket Cauchy convergence**: needs bracket-length halving with
  quantitative bound on the modulus N.
- **Root identification**: requires continuity (LDD) integration.
- Workaround paths: dyadic restriction (cutSum_quarter_general etc.),
  ScaleCut/RescaleCut stronger property, Decidable choice axiom.

## 비 verified scaffolded

- Series convergence theorems (full).
- IVT bracket convergence proof.
- Differentiation rules (sum/product/chain).
- Riemann FTC.
- Specific transcendental limit proofs.
- cutSum_assoc on arbitrary same-denom (blocked at b ≥ 3 by
  divisibility — only b ∈ {1, 2} give clean closed forms in Lean).
- cutSum × cutMul distributivity.
- cutMul_const_const = constCut(ac)(bd) (cutMul has precision
  artifacts, only special cases proved).
