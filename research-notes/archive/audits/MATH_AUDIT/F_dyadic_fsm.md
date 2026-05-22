# Chunk F — DyadicFSM audit

**Cluster**: DyadicFSM (116 files in 8 sub-dirs + 33 top-level).
가장 큰 단일 cluster.

**Audit date**: 2026-05-12.

## §0 Summary

| Sub-dir | Files | Lines | Topic |
|---|---|---|---|
| (top-level) | 33 | 3439 | mixed (FSM types + cross-class + predictors + capstones) |
| ArithFSM/   | 33 | 2276 | per-modulus ArithFSM (Mod{5,7,11,..,101}) + Hierarchy + Hardness |
| Pell/       | 15 |  849 | x²−Dy²=1, family + bounds + ProperMod{11,13,17,19,23} |
| Fib/        | 11 |  749 | Fibonacci FSMmod{3,5,7,11,13,17,19,23} + PellRelation, Pisano8 |
| Pisano/     |  9 |  793 | Pisano-period predictor (Predictor{6,7,8,11,14,17,20,22}) |
| Trib/       |  6 |  456 | Tribonacci FSMmod{3,5,7} + CRT4/CRT/Capstone |
| Legendre/   |  5 |  289 | Legendre-symbol Pisano variants (Pisano, PisanoExt, Small, V13_19, V213) |
| BitFSM/     |  2 |  191 | Bound, Converse |
| Archive/    |  2 |  143 | EdgeSignature, SubwordComplexity (historical) |

Total **116 files, 8376 lines**.  **0 ring violations**.

## §1 Ring violations

**0** — chunk F 는 perfectly clean.  Math 의 큰 cluster 중에서도
spec discipline 정확히 준수한 것.

## §2 Cluster docstring overview

### Top-level 33 files — 5 종류

**(a) Core FSM types / abstractions** (2):
- BitFSM (100) — finite-state bit stream generator
- ArithFSM (152) — 2-component state Pell-like recurrence

**(b) Sub-cluster aggregators** (7):
- ArithFSM, Fib, Legendre, Pell, Pisano, Trib, Archive

**(c) Signature / classifier infrastructure** (5):
- Signature, SignaturePredict, SignatureBipartite,
  Classifier, Conjecture

**(d) Product / closure / cross-class** (6):
- ProductFSM, ProductFSMPeriod, ProductFSMPeriodDvd,
  ProductFSMRun, ProductHelpers, LCMClosure

**(e) Forward periodicity / event** (3):
- ForwardClosure, ForwardEventual, ForwardPeriodicity

**(f) Misc capstone / predictor / theory** (10):
- AlgebraicDegree, BitAuto2, ConcretePellSig, CrossClassLens,
  LucasFSMmod5, NumberTheory213, ThueMorse, Tier2Hardness,
  TierBridge, TwoLayerPredictor, WalkUniversal

### Sub-dir structure

매우 systematic:

- **ArithFSM/** — primary 33 files, 거의 모두 `Mod{N}.lean` 형식
  (per-modulus FSM 정의).  + Hardness, Hierarchy.
- **Pell/** — Family/Bounds/Capstone + 5 per-modulus Proper* +
  Lens / LensPairs / LensTriple.
- **Fib/** — 8 per-modulus FSM + PellRelation + Pisano8 +
  PisanoCapstone.
- **Pisano/** — 8 Predictor{N} variants.
- **Trib/** — Tribonacci 3 per-modulus + CRT 캡스톤들.
- **Legendre/** — 5 variants.

명확한 패턴: per-modulus, 그러나 sub-dir 별로 다른 modulus set
(Fib 의 {3,5,7,11,...23} vs Pell 의 {11,13,17,19,23} 등).

## §3 Naming + 조직 평가

### Top-level 33 의 정리 가능성

Top-level 에 5 종류 (Core FSM / Aggregator / Signature /
Product+Closure / Forward / Misc) 가 평탄히 섞임.  정리 후보:

**Option A** — 신규 sub-dirs:
```
DyadicFSM/
├── Core/             — BitFSM.lean, ArithFSM.lean (FSM type 정의)
├── Signature/        — Signature, SignaturePredict, SignatureBipartite, Classifier, Conjecture, WalkUniversal
├── Product/          — ProductFSM{,Period,PeriodDvd,Run}, ProductHelpers, LCMClosure, CrossClassLens
├── Forward/          — ForwardClosure, ForwardEventual, ForwardPeriodicity
├── Tier/             — Tier2Hardness, TierBridge, AlgebraicDegree, ConcretePellSig
├── Misc/             — BitAuto2, LucasFSMmod5, NumberTheory213, ThueMorse, TwoLayerPredictor
├── (기존) ArithFSM/, Pell/, Fib/, Pisano/, Trib/, Legendre/, BitFSM/, Archive/
```

→ top-level 33 → ~7 aggregator + new sub-dirs.

**Option B** — 일부만 정리:
- ProductFSM 4 파일 (Product, ProductPeriod, ProductPeriodDvd,
  ProductRun) + ProductHelpers, LCMClosure → `Product/` sub-dir
- Signature 3 + Classifier + Conjecture + WalkUniversal →
  `Signature/` sub-dir

Option B 가 minimal 그리고 충분.

### Naming OK

- DyadicFSM cluster name 명확 (dyadic + FSM = FSM-generated dyadic
  bit stream).
- Sub-dir names (ArithFSM, BitFSM, Fib, Pisano, Pell, Trib,
  Legendre) 모두 명확.
- 33 top-level 의 names 도 모두 의미 명확.

### INDEX.md / API.lean 추가 권장

- DyadicFSM/INDEX.md 없음.  Top-level 33 files navigation 위해
  추가 권장.
- DyadicFSM/API.lean (or `aggregator.lean`) — HodgeConjecture/
  API.lean 패턴 따라 single-import entry 제공 가능.

## §4 Axiom status

Explore agent: **~95% PURE** — number-theoretic FSM 의 bit-level
proofs 가 거의 axiom-free.

- BitFSM / ArithFSM 의 transition / run 정의: structural recursion,
  PURE.
- per-modulus Mod{N} 파일들: decide 또는 `induction` 위 PURE.
- Signature / Classifier: PURE bit-level reasoning.

DIRTY 후보: pigeonhole 류 정리들 (ForwardPeriodicity 의 `Decidable.
byContradiction`) — 다만 Explore 가 별도 평가 없음.

## §5 처리 priority

### Quick wins

1. **DyadicFSM/INDEX.md 추가** — 33 top-level navigation.
2. **DyadicFSM/API.lean 추가** — HodgeConjecture pattern.

### Mid-term

3. **Top-level 33 정리** (Option B 권장):
   - 신규 `Product/` (~6 파일)
   - 신규 `Signature/` (~6 파일)
4. **Archive/ → 정리** — 2 files (EdgeSignature, SubwordComplexity)
   가 정말 historical 이면 명시 또는 delete.
   docstring 에 "deferred-cluster repair" 언급 — 정상 빌드 확인됨.

### Long-term

5. **per-modulus Mod{N}.lean 일관화** — ArithFSM 33 + Fib 8 +
   Pell 5 + Pisano 8 + Trib 3 + Legendre 5 = 62 per-modulus files.
   modulus 별 cross-reference (예: Fib의 mod-5 vs ArithFSM의 mod-5)
   가 활용되면 사용성 더 좋음.
6. **TierBridge 의 D2 hierarchy** — `research-notes/archive/D2_*`
   참조.  research-notes 와 cross-link.

## §6 결정 보류

§3 (Option A/B 선택), §5 priority 모두 **기록만**.

특이사항:
- **chunk F 의 0 violations + ~95% PURE** — Math 의 axiom hygiene
  best chunk (Cohomology 와 함께).
- DyadicFSM 가 213 의 number theory cluster — Pell/Fib/Trib/Pisano/
  Legendre 다양한 sequence family + per-modulus FSM 의 systematic
  접근.  Mathematically 가장 mature 한 cluster 중 하나.
- 116 files 가 한 디렉토리 (top-level 33 평탄 + 8 sub-dirs) —
  navigation 차원에서 정리 가치 있음, 다만 axiom hygiene 영향 없음.
