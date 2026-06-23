# DyadicFSM — Module Index

213-native number theory via dyadic FSMs — Pell, Fibonacci,
Tribonacci, Pisano, Legendre families.  G119 (Phase 3.2/3.3/4)
marathon adds FLT, Frobenius, F_{p²}, Binet-bridge infrastructure.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `ArithFSM/` | 10 + 3 Mod buckets | per-modulus ArithFSM (Mod{Small,Medium,Large}) + Hierarchy + Hardness + V1/V3 helpers + `InvertibleArithFSM2` (G119 Phase 2 abstraction) |
| `BitFSM/` | 2 | Bound, Converse |
| `Fib/` | 4 (post-consolidation) | Fibonacci FSMmod (8 primes 통합) + PellRelation + Pisano8 + PisanoCapstone |
| `Pell/` | 11 | Pell x²-Dy²=1 family + ProperMod (5 primes 통합) + Bounds/Lens |
| `Pisano/` | 9 | Pisano-period predictors (step-by-step extension chain) |
| `Trib/` | 4 (post-consolidation) | Tribonacci FSMmod (3 primes 통합) + CRT capstones |
| `Legendre/` | 1 (consolidated) | Legendre-symbol Pisano variants (Pisano/Ext/Small/V13_19/V213) |
| `Archive/` | 2 | EdgeSignature, SubwordComplexity (historical) |
| `Product/` | 7 | ProductFSM{,Period,PeriodDvd,Run}, ProductHelpers, LCMClosure, CrossClassLens |
| `Signature/` | 6 | Signature{,Predict,Bipartite}, Classifier, PeriodClosure, WalkUniversal |
| `Forward/` | 3 | ForwardClosure, ForwardEventual, ForwardPeriodicity |
| `Tier/` | 3 | Tier2Hardness, TierBridge, AlgebraicDegree |
| `FLT/` | 10 | FLT chain: Binomial / BinomialTheorem / BinomialTwoVar / ChooseFactorial / ChoosePrime / FreshmanDream / FLTPrimary / FLTMain / PhiFLT / Sum |

## Top-level standalone

BitAuto2, ConcretePellSig, ContinuedFraction, LucasFSMmod5,
FibApparitionMod5, NumberTheory213, ThueMorse, TwoLayerPredictor —
independent files.
`FibApparitionMod5` — Fibonacci rank of apparition `α(5) = 5` at the
ramified prime (`5 ∣ F_n ⟺ 5 ∣ n`) vs Lucas-never-zero (the
singular/regular Binet split at the double root).

Pell-matrix / modular bridges (top-level): BinetBridge,
PellFibBridge, PellMatrix{,Action,Cases,Inverse,Pigeonhole},
PhiMod5, PsiMod5, MulOrderPigeonhole, RankApparition,
KBonacci, KBonacciRecurrence, UniversalDispatch, UniversalInert,
UniversalSplit — bridges between Pell-matrix iteration and modular
arithmetic + the universal-over-primes closures.

`DyadicFSM.lean` — top aggregator.

## 213-native paradigm

- **One bit = one dyadic bisection** (cf. Information/Bit.lean).
- Per-prime evidence via per-modulus FSM instances (mod p tightness
  via QR/NQR + Pisano period predictions).
- Number theory results all `#print axioms` empty.
