# DyadicFSM — Module Index (sub-organized 2026-05-13)

213-native number theory via dyadic FSMs — Pell, Fibonacci,
Tribonacci, Pisano, Legendre families.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `ArithFSM/` | 9 + 3 Mod buckets | per-modulus ArithFSM (Mod{Small,Medium,Large}) + Hierarchy + Hardness + V1/V3 helpers |
| `BitFSM/` | 2 | Bound, Converse |
| `Fib/` | 4 (post-consolidation) | Fibonacci FSMmod (8 primes 통합) + PellRelation + Pisano8 + PisanoCapstone |
| `Pell/` | 11 | Pell x²-Dy²=1 family + ProperMod (5 primes 통합) + Bounds/Lens |
| `Pisano/` | 9 | Pisano-period predictors (step-by-step extension chain) |
| `Trib/` | 4 (post-consolidation) | Tribonacci FSMmod (3 primes 통합) + CRT capstones |
| `Legendre/` | 1 (consolidated) | Legendre-symbol Pisano variants (Pisano/Ext/Small/V13_19/V213) |
| `Archive/` | 2 | EdgeSignature, SubwordComplexity (historical) |
| `Product/` | 7 | ProductFSM{,Period,PeriodDvd,Run}, ProductHelpers, LCMClosure, CrossClassLens |
| `Signature/` | 6 | Signature{,Predict,Bipartite}, Classifier, Conjecture, WalkUniversal |
| `Forward/` | 3 | ForwardClosure, ForwardEventual, ForwardPeriodicity |
| `Tier/` | 3 | Tier2Hardness, TierBridge, AlgebraicDegree |

## Top-level standalone

BitAuto2, ConcretePellSig, LucasFSMmod5, NumberTheory213,
ThueMorse, TwoLayerPredictor — independent files.

`DyadicFSM.lean` — top aggregator.

## 213-native paradigm

- **One bit = one dyadic bisection** (cf. Information/Bit.lean).
- Per-prime evidence via per-modulus FSM instances (mod p tightness
  via QR/NQR + Pisano period predictions).
- Number theory results all `#print axioms` empty.
