# Chunk C — Algebra audit

**Clusters**: CayleyDickson (56), Group (5), Polynomial213 (2),
Linalg213 (14 incl. Gap/ sub-dir).  Total **77 files**.

**Audit date**: 2026-05-12.

## §0 Summary

| Cluster | Files | Lines | Spec status |
|---|---|---|---|
| CayleyDickson/  | 56 | 5259 | **20 Ring violations** (largest single Math source) |
| Group/          |  5 |  260 | ✓ clean |
| Polynomial213/  |  2 |  105 | TBD (read) |
| Linalg213/      | 14 |  911 | TBD (Gap/ sub-cluster 안에 sorry "false positive" 확인) |

Chunk total = **20 violations of Math's 22 total**.

## §1 Ring violations (CayleyDickson dominant)

20 CayleyDickson files import Theory.Internal/Theory.Raw directly.
Catalog:

### Theory.Internal.Int213 reach-in (15 files)

가장 흔한 패턴 — Int 위 algebra structure 정의 시 `CommRing213
Int` instance 필요해서.

- ZIArith, ZIDomain, ZIHom, ZOmega, ZOmegaDouble — Z 류 quadratic
  integer ring 정의 (`Int.{add_comm, mul_comm, ...}` 사용)
- ZSqrt{2,Minus2}{Domain,Tower,Product} — ℤ[√n] family
- QuadIdentities — quad 정체성 (Norm bilinearity 등)
- LipschitzAlgebra213, LipschitzHeavy — Lipschitz quaternion order
- ZSqrtProduct — `Theory.Raw` 도 추가

### Theory.Internal.Algebra213 reach-in (7 files)

generic `Algebra213` typeclass tower (현재 Theory/Internal/Algebra*)
사용:

- LipschitzAlgebra213, LipschitzHeavy — CommStarRing213 instance
- PathionHeavy, SedenionHeavy, TrigintaduoionionHeavy — 16/32/64-dim
  StarRing213 instances (CD 4번째 doubling 이후)
- ZIAlgebra213 — ZI instance
- AlgebraTowerCapstone — `Theory.Internal.Algebra213CDDoubleStar`
  도 추가 (CDDoubleStar functor 적용)

### Theory.Raw reach-in (4 files, 전체 노출)

- F2CDTower — F_2 base CD tower
- LipschitzLens — Lens construction on Lipschitz
- R5Vacuity — R5 vacuity claim (Raw → α fold totality)
- AlgebraTowerCapstone — Theory.CDDouble.* + Lib.Math.Mobius213
  (5 imports 한꺼번에 — 가장 reach-heavy)

## §2 Cluster docstring overview

### CayleyDickson/ (56 files) — CD algebra tower

명확한 sub-groups (cluster 내 미분류):

| Sub-group | Files | Topic |
|---|---|---|
| Tower 패턴 | CDDouble, CDTower, F2CDTower, AlgebraTowerCapstone/Asymptote, TowerFixedPoint, UniversalOrderGrowth{,C} | CD-doubling iteration |
| ℤ-quad order | Z{I,Omega,Sqrt,Sqrt2,SqrtMinus2}{,Domain,Hom,Arith,Product,Algebra213,Instance,Double,L6Search,L6Witnesses,Tower} | concrete quadratic/quartic integer rings |
| CD level 1-3 | Cayley, CayleyHeavy, CayleyOrder4Monopoly | level-3 CD (octonions) |
| CD level 4 | Sedenion, SedenionHeavy, SedenionOrder4Monopoly | level-4 (sedenions) |
| CD level 5+ | Pathion, PathionHeavy, Trigintaduonion, TrigintaduoionionHeavy | level-5/6 |
| Lipschitz | LipschitzAlgebra213, LipschitzHeavy, LipschitzLens, LipschitzOrder4Monopoly | quaternion order |
| Hurwitz / Type | Hurwitz213, TypeAResidualClosedForm, TypeE_Rejection | special unit groups |
| Order4 universal | Order4Monopoly_L4T/L5T/L6T | universal Order-4 |
| Misc | QuadIdentities, R5Vacuity, ShiftRule_ZI_L3, ZSqrtMinus2L6Search/Witnesses | helpers + searches |

Heavy files (CayleyHeavy, LipschitzHeavy, SedenionHeavy, PathionHeavy,
TrigintaduoionionHeavy) — **~50% DIRTY** (propext via simp on polynomial identities).

### Group/ (5 files) — group theory

- Cyclic, Symmetric — basic group types
- GroupAction — action semantics
- SU5Channels — SU(5) channel structure (DRLT physics 연결)
- Capstone — bundle
- (INDEX.md 존재)

Spec ✓ clean — Theory import 없음.

### Polynomial213/ (2 files) — tiny cluster

- Sound — polynomial soundness
- Ineq — polynomial inequalities

Fold candidate: **→ Analysis/ 또는 Real213/** (사용 context 따라).

### Linalg213/ (14 files) — 213-native linear algebra

Top-level (9): Bridge, Capstone, Chiral, Gap (umbrella), Gram, Rank, Rank5Concrete, Span, Vector.

Sub-dir Gap/ (5): Capstone, Determinant, Eigen, MatrixMul, TensorProduct.

INDEX.md 없음.  Gap/ 의 의미가 *"Lean-core gap-fill"* — 213-native
재구현.  R5Vacuity 의 `sorry` mention 은 docstring (false positive).

## §3 Naming + 조직 평가

### CayleyDickson — sub-cluster 분할 권장

56 files 가 하나의 디렉토리에 평탄하게 있어 navigation 어려움.
권장 sub-cluster:

```
CayleyDickson/
├── Tower/       — CD{Double,Tower}, F2CDTower, AlgebraTower*, TowerFixedPoint, UniversalOrderGrowth*, Order4Monopoly_L{4,5,6}T
├── Integer/     — Z{I,Omega,Sqrt,Sqrt2,SqrtMinus2}{...}, Hurwitz213, ZSqrt{,2,Minus2}*
├── Levels/      — Cayley{,Heavy,Order4}, Sedenion{,Heavy,Order4}, Pathion{,Heavy}, Trigintaduonion{,Heavy}
├── Lipschitz/   — Lipschitz{Algebra213,Heavy,Lens,Order4Monopoly}
└── Misc/        — QuadIdentities, R5Vacuity, ShiftRule_ZI_L3, TypeAResidualClosedForm, TypeE_Rejection
```

### Polynomial213 — fold

2 files → Analysis/ 또는 Real213/Polynomial.lean 으로 통합 후 cluster
제거.

### Linalg213 — INDEX.md 추가 + Gap/ docstring 정리

14 files 큰 cluster.  INDEX.md 작성 + Gap/ sub-dir 의 역할 ("Lean-core
gap-fill") 명시 권장.

### Group — 그대로

5 files clean cluster.  INDEX.md 이미 있음.

## §4 Axiom status

- **CayleyDickson**: ~50% DIRTY (Heavy 5 파일 + Order4 family 일부).
  주된 leak: propext via simp on Int polynomial identities.  Theory.
  Internal.Algebra213 reach-in 으로 인한 abstraction barrier 가
  refactor 막음.
- **Group**: estimated 100% PURE (basic group theory, no quotient).
- **Polynomial213**: TBD (small).
- **Linalg213**: PURE 다수 (Gap/ 의 Lean-core 대체) + 일부 DIRTY
  (Rank, Eigen).

## §5 처리 priority

### Quick wins

1. **AlgebraTowerCapstone** 의 5 Theory reach-in (가장 reach-heavy) —
   `Theory.CDDouble.UniversalInduction` 의 Lib 이동 후 처리 가능
   (THEORY_AUDIT §4 의 이동 후보).
2. **Polynomial213 fold** — 2 files → Analysis/ 또는 Real213/ 로
   통합.
3. **Linalg213/INDEX.md 작성** + Gap/ docstring.

### Mid-term

4. **CayleyDickson sub-cluster 분할** (Tower / Integer / Levels /
   Lipschitz / Misc) — 56 files 평탄 → 5 sub-cluster.  내부 import
   대량 갱신 필요.
5. **Theory.Internal.Int213 reach-in 15 files** — `Theory.Internal.
   Int213` 를 `Lens/Codomain/Int213` (또는 비슷) 으로 promote 후
   해당 reach-in 들 새 위치로.
6. **Theory.Internal.Algebra213 reach-in 7 files** — typeclass tower
   를 `Lens/Algebra/` 또는 `Lib/Math/Algebra213/` 로 promote.

### Long-term

7. **Heavy files DIRTY → PURE** — propext-leaking simp 패턴 정리
   (CayleyHeavy, SedenionHeavy, PathionHeavy, TrigintaduoionionHeavy,
   LipschitzHeavy).  generic typeclass `IntegerNormed213.normSq_mul`
   이미 ∅-axiom 으로 abstract level 에서 증명됨 — instance 별
   leak 만 정리.

## §6 결정 보류

§3 (sub-cluster 분할), §5 (작업 priority) 모두 **기록만**.  실행은
Mingu Jeong 결정 후.

특이사항:
- CayleyDickson 의 reach-in 패턴 (Theory.Internal.Int213 / Algebra213)
  은 *Theory.Internal 의 promotion* 으로 해결 — 단순 import 갱신이
  아니라 type 의 위치 자체 결정 필요 (THEORY_AUDIT §4.2 의
  `Internal/` 3-성격 분리 와 연결).
- 즉 chunk C 의 위반 해결은 **Theory 의 Internal 정리와 함께** 가야 함.
