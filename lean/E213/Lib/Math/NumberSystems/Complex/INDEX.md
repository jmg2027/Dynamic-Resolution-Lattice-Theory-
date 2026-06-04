# Complex Analysis 213 — Module Index

Blueprint: `blueprints/math/04_complex_213.md` (retired).

## Modules

| File | Topic | Status |
|---|---|---|
| `ComplexCut.lean` | `(Cut, Cut)` pair; cAdd/cMul; zero/one/i; re/im | ∅-axiom |
| `Holomorphic.lean` | identity / constant / square holomorphic | ∅-axiom |
| `PowerSeries.lean` | polyId, polySquare, cExp(0) = 1 (rfl) | ∅-axiom |
| `Capstone.lean` | 3 cluster witnesses + total_witness | ∅-axiom |
| `Complex.lean` | umbrella | — |

## 213-native paradigm

  * ℂ = first Cayley-Dickson level on `Cut`. ZI (Gaussian integers)
    in `Lib/Math/CayleyDickson/ZI.lean`; this lifts to `Cut`-valued.
  * Holomorphic = Cauchy-Riemann via `partialAt` (Multivariable 213).
  * Power series = finite polynomial by Grade-N nilpotency
    (`Lib/Math/Cohomology/CutExpFiniteTruncation.lean`).
  * `cExp(0) = 1` reuses `Probability.Gaussian.expSumAtZero`.
