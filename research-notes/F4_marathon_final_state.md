# F4 — Marathon final state (2026-04-26)

## Session arc

D1 (ZFC ℝ as final boss) → D3 retraction → E1 roadmap (Bishop-style
Phase A-H) → E2-E4 walls → E5 ("213 은 213만") → F1 cutSum working →
F1-F3 generic kernel + recurrence Lens → F2 reframe (Real = Lens
output, framework inherent) → F3 (transcendental recurrence
classification).

총 commits: 30+ (b4a29fe → 95b79b3 + ongoing).
총 Real213 modules: 43+.

## Library completed items

E213.Math.lean (single import entry) re-exports the following modules:

### Foundation (Phase A)

Real213, Real213Equiv (+ Setoid), Real213Const, Real213Order,
Real213OrderExtra, Real213Sign, Real213StrictPos.

### Cut-level arithmetic

- `cutSum`, `cutMul`, `cutInv`, `cutDiv`, `cutNeg`, `cutSignedMul`
- `cutSignedSum`, `cutSignedSub`
- `cutMax`, `cutMin` (lattice ops, search-free)
- `cutHalf`, `cutMid` (bisection support)
- `cutPow`, `cutScale`, `cutAbs`, `cutDistance`
- `evalPoly` (polynomial)

### Generic kernel

- `cutBinary` (P k1 k2 M1 M2 cx cy → Bool), `cutBinaryInner_congr`,
  `cutBinaryOuter_congr`, `cutBinary_locallyDetermined` (모두 0 axioms).
- `CutBinaryOp` struct + `cutSumOp` + `cutMulOp` + `apply_locallyDetermined`.
- `CutAlgebra` struct + `stdCutAlgebra` (universal binding).

### Continuity

- `CutFunction := RealCut → RealCut`.
- `isLocallyDetermined`, `isLocallyDetermined2`.
- `cutSum_locallyDetermined` ([propext]), `cutMul_locallyDetermined`
  (0 axioms).
- `LocallyDeterminedData` (data form) + `composeLDD` (categorical
  closure).

### Cauchy + Sequence + Series

- `CauchyCutSeq` (Cauchy sequence of cuts + limit).
- `CutSeq`, `CauchyCutSeq.limit`, `constCauchySeqCut`.
- `partialSum`, `SeriesCauchy` + `SeriesCauchy.limit`.

### Specific functions

- `expCutPartial` (e via factorial series).
- `sinPartial`, `cosPartial` (signed alternating series).
- `leibnizPiPartial` (π/4 via Leibniz).
- `geomHalfSeries` (geometric Σ (1/2)^i).

### Recurrence Lens classification (F3)

- `RecurrenceLens` struct (state + init + transition + output).
- `constRecurrenceLens`, `eRecurrenceLens` instances.
- `unfoldState`, `cutAt`.

### Cut poset

- `cutEq` (pointwise Bool equality), `cutLe` (cy implies cx).
- Refl / symm / trans / antisymm all verified.

## Honest assessment

### Verified working (decide-tested or proved 0/propext axioms)

- Cut arithmetic: cutSum, cutMul, cutMaxMin, cutNeg, cutSignedMul.
- **cutSum_comm + cutMul_comm** (via iff existential + bijection).
- **cutSum_mono + cutMul_mono** (left + right, via iff).
- Continuity: cutSum/Mul locally-determined.
- Composition closure: composeLDD.
- Cauchy completeness (direct construction).
- Lattice properties: cutMax/Min idempotent, zero, **distributive**,
  **absorption**, **upper/lower bounds (cutLe_cutMax/Min)**.
- Cut poset (cutLe refl/trans/antisymm + lattice ordering).
- IVT bisection structural lemmas (zero/succ_true/succ_false).
- Constant difference quotient simplification.
- Geometric series partial sum tests (n=2, n=3).
- Riemann actual recursive sum (replacing placeholder).
- cutSumAux_eq_true_iff + cutMulInner/Outer_eq_true_iff (existential
  characterizations).

### Scaffolded (definitions correct, full proofs deferred)

- IVT, Differentiation, Integration interfaces.
- Series convergence (up to partialSum, limit proof separate arc).
- exp / sin / cos / π partial sums (convergence proof separate).
- Division (boundary precision artifact).
- Symmetric predicate → commutativity (deferred).

## True significance

User's framework-philosophical interventions were the driving force
throughout the marathon:

1. "Define 213's own reals rather than mapping Dedekind cuts" → D3
   retraction.
2. "Write kernels one by one" → ModulusCombiner kernel.
3. "213 must stay 213" → Cut-level breakthrough (F1).
4. "Go generic in the 213 style" → cutBinary universal kernel.
5. "Libraryize" → E213.Math entry point.
6. "Infinite natural number pickup for reals like 0.28..." → F2
   reframe (Real = Lens output, framework inherent).
7. "Pattern-generating rule of transcendentals" → F3 recurrence Lens
   classification.

Each directive was a *framework simplification* — removing the noise
of Bishop ε-N attempts.

## Next axis candidates

- Full proof of the IVT bisection algorithm.
- Generic theorem for series convergence.
- Differentiation: difference quotient + modulus.
- Integration: Riemann sum convergence.
- File organization / explicit separation of the Math/ namespace.

## Cross-references

- `notes/D1` (retracted), `D2` (complexity classification), `D3`
  (Real213 native), `E1` (roadmap), `E2-E5` (walls/resolution),
  `F0-F3` (synthesis), `F4` (this).
- `framework/E213/Math.lean` (library entry).
- 43+ Real213-related Lean modules under `framework/E213/Research/`.
