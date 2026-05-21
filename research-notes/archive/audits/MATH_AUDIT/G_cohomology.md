# Chunk G — Cohomology + HodgeConjecture audit

**Clusters**: Cohomology (94), HodgeConjecture (67).  Total **161 files**.
가장 큰 chunk.

**Audit date**: 2026-05-12.

## §0 Summary

| Cluster | Files | Lines | Spec status |
|---|---|---|---|
| Cohomology/   | 94 | 7156 | 1 violation (Surfaces/T2Minimal/CupPairing → Int213) |
| HodgeConjecture/ | 67 | 6880 | ✓ clean |

Chunk total = **1 violation** — 매우 깨끗.

## §1 Ring violations

- **Cohomology/Surfaces/T2Minimal/CupPairing.lean** → `Theory.
  Internal.Int213`.  T² 표면의 cup pairing 정의에 Int 사용.  Int213
  reach-in 패턴 — chunk C 의 Z-quad files 와 같이 처리.

HodgeConjecture: violations **0**.

## §2 Cluster docstring overview

### Cohomology/ (94 files, 10 sub-dirs + 29 top-level)

명확한 sub-cluster 분리:

| Sub-dir | Files | Topic |
|---|---|---|
| Cochain/   | 4 | 213-native cochain complex foundation |
| Delta/     | 5 | δ : Cᵏ → Cᵏ⁺¹ coboundary |
| Cup/       | 3 | strict cup product on Cochains |
| **CupAW/** | **21** | Alexander–Whitney cup (homotopy-coherent variant, 가장 큰 sub-cluster) |
| Bipartite/ | 3 | bipartite multigraph cohomology |
| Fractal/   | 3 | fractal-lens cardinality scaffold (N_U = 5²⁵) |
| Hodge/     | 9 | Δ-Laplacian + ⋆-involution machinery |
| Surfaces/  | 9 (incl. T2Minimal/, T2Squared/) | concrete surface examples |
| Universal/ | 8 | δ²=0 Prop-level universal lift |
| (top-level 29) | | aggregators + bridges + capstones |

**Top-level 29 files** 의 분류:

| 종류 | 파일 |
|---|---|
| Sub-cluster aggregator | Cochain, Cup, CupAW, Delta, Fractal, Hodge, Bipartite, Surfaces, Universal (9) |
| Concrete cohomology | BettiKernel, K5, DiamondShape, DiamondAudit, EulerClosed, TopologyCompare, EncodingBijection{,52}, SimplexBasis (~9) |
| Specific bridge / capstone | AlphaEMBridge, Real213Bridge, Paper1Chiral, ClosureExtension, CutExpFiniteTruncation, CutLog, LeibnizFinding, TrivialCases, WhyDimFive, XorPairCombine (~10) |
| Bundle | Capstone |

### HodgeConjecture/ (67 files, 7 sub-dirs + 8 top-level)

이미 잘 정리된 layered architecture (`API.lean` docstring 참조 —
"six functional layers").

| Sub-dir | Files | Topic |
|---|---|---|
| Foundation/    | 6 | 기초 layer |
| Structure/     | 5 | H* algebraic structure (cohomology ring, Poincaré, hard Lefschetz) |
| **Pairing/**   | **21** | Hodge index + Hodge–Riemann pairings (가장 큰 sub-cluster) |
| Refinement/    | 6 | neighbouring conjectures clarifying HC statement |
| **Bridge/**    | **11** | physics + stat-mech + CS bridges |
| MotivicBridge/ | 6 | motivic cohomology cross-references |
| Toolkit/       | 4 | reusable infrastructure |

**Top-level 8 files**: API + 7 sub-cluster aggregators (Foundation,
Structure, Pairing, Refinement, Bridge, MotivicBridge, Toolkit).

매우 잘 organized — Math 내에서 best-organized cluster 후보.
`HodgeConjecture/API.lean` 가 single import.

## §3 Naming + 조직 평가

### HodgeConjecture — exemplary

이미 6-layer architecture + API.lean.  Math 의 다른 cluster
정리시 참고 모델.

### Cohomology — top-level 29 files 의 정리 가능성

29 top-level files 중 9 가 sub-cluster aggregator.  나머지 20 은:
- 9 concrete cohomology examples (BettiKernel, K5, DiamondShape, ...)
- 10 specific bridges / capstones (AlphaEMBridge, Real213Bridge, ...)
- 1 final Capstone

**정리 후보**:
- 신규 `Cohomology/Examples/` (BettiKernel, K5, DiamondShape, DiamondAudit, EulerClosed, TopologyCompare, EncodingBijection{,52}, SimplexBasis, WhyDimFive) — 10 파일
- 신규 `Cohomology/Bridge/` (AlphaEMBridge, Real213Bridge, Paper1Chiral, ClosureExtension, CutExpFiniteTruncation, CutLog, LeibnizFinding, TrivialCases, XorPairCombine) — 9 파일
- Capstone, Cup/CupAW/Delta/Cochain/Fractal/Hodge/Bipartite/Surfaces/Universal aggregator (10) 만 top-level 유지

→ top-level 29 → 10 (모두 aggregator + Capstone)

### API.lean 추가 권장

- Cohomology/API.lean — HodgeConjecture/API.lean 형식 따라
  9 sub-cluster + Capstone re-export.  Single import for downstream.

### CupAW 의 규모 (21 files, 1929 lines)

가장 큰 sub-cluster.  내부 미분류 — 자체 sub-organization 검토 가치
있음 (Leibniz patterns, BilinearFunc, decomp, PointwiseBilinear,
etc.).  단 별도 audit 필요.

## §4 Axiom status

### Cohomology

Explore agent: ~80% PURE.  주된 leak:
- Cup products at propext boundary (CupAW 의 일부 BilinearFunc /
  Leibniz patterns)
- Cochain.add 의 funext-by-design (Lens combine 의 일부)

이미 marathon (HANDOFF.md) 에서 ~60 PURE conversion 달성 — CupAW
의 LeibnizAlgLift{,21,22,21Alpha,22Alpha}, Prop41/42, V5_2Decomp/
V5_1DecompR 등.

### HodgeConjecture

Explore agent 가 별도 평가 없음.  분명 추정 ~85%+ PURE
(structural cohomology, 깨끗한 algebra).  큰 cluster 인데
violations 0 — 잘 짜여진 증거.

## §5 처리 priority

### Quick wins

1. **Cohomology/Surfaces/T2Minimal/CupPairing.lean** Theory.
   Internal.Int213 reach-in — chunk C 와 함께 (Int213 promotion).
2. **Cohomology/API.lean 추가** — HodgeConjecture/API.lean 패턴
   따라.  9 sub-cluster aggregator + Capstone re-export.

### Mid-term

3. **Cohomology top-level 정리** — 29 → 10:
   - 신규 `Examples/` (~9 파일): BettiKernel, K5, Diamond{Shape,
     Audit}, EulerClosed, TopologyCompare, EncodingBijection{,52},
     SimplexBasis, WhyDimFive
   - 신규 `Bridge/` (~9 파일): AlphaEMBridge, Real213Bridge,
     Paper1Chiral, ClosureExtension, CutExp..., CutLog,
     LeibnizFinding, TrivialCases, XorPairCombine
   - top-level: 10 aggregator (Cochain, Cup, CupAW, Delta, Fractal,
     Hodge, Bipartite, Surfaces, Universal, Capstone) 만

4. **CupAW (21 files) sub-organization 검토** — 별도 audit pass.

### Long-term

5. **HodgeConjecture/Pairing (21 files) 의 내부 organization** —
   가장 큰 sub-cluster, 분할 가능성 검토.
6. **Cohomology / HodgeConjecture cross-ref 강화** — Hodge.lean 과
   HodgeConjecture/Structure 의 의미적 연결 명시.

## §6 결정 보류

§3 (Cohomology top-level 정리), §5 priority 모두 **기록만**.
Mingu Jeong 결정 대기.

특이사항:
- **161 files 의 1 violation** — chunk G 는 spec discipline 측면에서
  Math 의 best chunk.  HodgeConjecture 의 0 violations 가 특히 인상적.
- **HodgeConjecture/API.lean 패턴** 이 Math 전체 organization 의
  reference model — Cohomology + 다른 cluster 들도 같은 패턴 따를
  가치 있음.
- CupAW 의 marathon 흔적 (60 PURE conversion 의 majority 가 이
  cluster) — 큰 진전 이미 달성.
