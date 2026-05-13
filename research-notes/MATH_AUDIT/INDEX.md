# MATH_AUDIT/ — chunked audit of `lean/E213/Lib/Math/`

`Lib/Math/` is **797 .lean / 71,140 lines / 47 sub-clusters** —
too large for a single audit doc.  Per Mingu Jeong (2026-05-12)
plan, audited in **9 thematic chunks (A–I)**, each file ≤ 250
lines target.

## Chunk catalog (priority-ordered)

| # | File | Clusters | Files | Status |
|---|---|---|---|---|
| 1 | `C_algebra.md` | CayleyDickson, Group, Polynomial213, Linalg213 | 77 | ✓ initial pass (2026-05-12) |
| 2 | `A_foundations.md` | NatHelpers, Modulus, ModArith, Choice, AxiomSystems, Tactic, Logic, Search | 42 | ✓ initial pass (2026-05-12) |
| 3 | `G_cohomology.md` | Cohomology, HodgeConjecture | 161 | ✓ initial pass (2026-05-12) |
| 4 | `F_dyadic_fsm.md` | DyadicFSM | 116 | ✓ initial pass (2026-05-12) |
| 5 | `E_analysis.md` | Analysis, CascadeCalculus, ODE, Multivariable, Functional, Measure, Trajectory | 104 | ✓ initial pass (2026-05-12) |
| 6 | `B_numerical.md` | Real213, SignedCut, Cauchy, EpsilonDeltaModulus, Complex, Hyper, Infinity, Irrational, NumberGrid | 134 | ✓ initial pass (2026-05-12) |
| 7 | `D_topology.md` | Combinatorics, Topology, LevelTopology, OperationTopology, AngleStructure, TriangularTower, BipartiteDecomp, CartesianVsDisjoint, Diagonal | 42 | ✓ initial pass (2026-05-12) |
| 8 | `H_probability.md` | Probability, Information | 33 | ✓ initial pass (2026-05-12) |
| 9 | `I_misc.md` | Extras, DialogueAudit, GenerationRule, PatternCatalog, UniverseChain | 46 | ✓ initial pass (2026-05-12) |

## Phase 1 cross-Math summary (Explore pass 2026-05-12)

- **22 Theory.Internal violations** — CayleyDickson 압도 (~14),
  NatHelpers (~2), Cohomology (~2), 기타.
- **39 Theory.* direct imports** — 대부분 `Theory.Raw`/`Atomicity`
  (architectural OK), Closed.Nat213Bridge / Atomicity.Five 등 일부
  검토.
- **0** App / Lens.Internal / Term.Internal / Mathlib.
- **0 actual sorry** (R5Vacuity 의 "sorry" 는 docstring comment).
- **PURE 2654 / DIRTY 129 / 0 sealed** (~95% PURE).
- **16 tiny clusters** (1–4 files) — fold candidates.

## Audit 완료 — chunk-별 위반 분포 (2026-05-12)

| Chunk | Files | Violations | Notable |
|---|---|---|---|
| C (Algebra) | 77 | 20 | CayleyDickson 압도 |
| A (Foundations) | 42 | 7 | AxiomSystems/Choice 주제적 |
| G (Cohomology) | 161 | 1 | best-organized (HodgeConjecture API.lean) |
| F (DyadicFSM) | 116 | 0 | ~95% PURE |
| E (Analysis) | 104 | 0 | ODE 중복 (top-level vs Analysis 내부) |
| B (Numerical) | 134 | 5 | Infinity 의 Raw cardinality (주제적) |
| D (Topology) | 42 | 0 | ~100% PURE, 가장 깨끗 |
| H (Probability) | 33 | 0 | ~100% PURE |
| I (Misc) | 46 | 5 | UniverseChain (주제적, Raw axiom chain) |
| **Total** | **755** | **38** | **~95% files clean** |

Math 의 ring 위반 ~5% — Phase 1 의 "22 Theory.Internal" + 16
Theory.Raw 직접 reach (대부분 주제적).  실제 spec violations 중
정리 대상은 ~20 (CayleyDickson 의 Internal reach-in 그룹).

## Per-chunk content 형식

§0 Summary (cluster list + file/line counts)
§1 Ring violations (Theory.Internal / Theory.* / 기타 reach-in)
§2 Cluster docstring overview (1 line per cluster)
§3 Naming/조직 평가 (fold 후보, misalignment)
§4 Axiom status (PURE/DIRTY 분포)
§5 처리 priority (Quick wins / Mid / Long)
§6 결정 보류 marker

## Reference

- `research-notes/THEORY_AUDIT.md` (§1–4 stress-format)
- `research-notes/LENS_AUDIT.md` (2-tier API pattern)
- `lean/E213/ARCHITECTURE.md` (Ring discipline)
- `STRICT_ZERO_AXIOM.md` (PURE/DIRTY canonical)

## Cross-cutting recommendations (Mingu Jeong, 2026-05-12)

Math audit 9-chunk 결과 종합 + 사용자 추가 원칙.

### A. File consolidation — "예시와 일반 증명은 한 파일에"

여러 .lean 파일이 같은 주제의 *예시 + 일반 증명* 으로 흩어진
패턴 모음.  통합 후보:

| 현재 패턴 | 통합 후 |
|---|---|
| Irrational/Sqrt2{Cut,KernelFree,Pure}.lean (3 파일, 진화 단계) | `Irrational/Sqrt2.lean` 단일 |
| Cauchy/Euler{Seq,Sharper,SharperKernelFree,SharperPure,GenericPure,CombinatorialPure}.lean (6) | `Cauchy/Euler.lean` 또는 `{Euler.lean, EulerPure.lean}` 2 단계 |
| Cauchy/Wallis{Seq,Sharper,SharperKernelFree}.lean (3) | `Cauchy/Wallis.lean` 단일 |
| CayleyDickson/Cayley{,Heavy,Order4Monopoly}.lean (3 per level × N levels) | per level 한 파일 (`Cayley.lean` 안 §Heavy + §Order4) |
| Extras/CauchySchwarz{,2D,3D,4D,Inductive,List}.lean (6) | `CauchySchwarz.lean` 단일 (또는 Functional/ 로 이동 후) |
| Multivariable/Stokes{,2D,3D}.lean (3) | `Stokes.lean` 단일 |
| ArithFSM/Mod{5,7,11,13,17,19,23,29,31,...,101}.lean (~30) | 단일 `ArithFSM/PerModulus.lean` (사례 + 일반 정리) 또는 4–5 그룹 |
| DyadicFSM/Pisano/Predictor{6,7,8,11,14,17,20,22}.lean (8) | `Pisano/Predictor.lean` 단일 |
| Fib/FSMmod{3,5,7,11,13,17,19,23}.lean (8) | `Fib/FSMmod.lean` 단일 |
| Trib/FSMmod{3,5,7}.lean (3) | `Trib/FSMmod.lean` 단일 |
| Legendre/{Pisano,PisanoExt,Small,V13_19,V213}.lean (5) | `Legendre.lean` 단일 |

**원칙**: 같은 주제의 진화 단계 (Seq → Sharper → KernelFree → Pure)
또는 instance set (per modulus, per dimension) 은 *한 파일 안에서*
표현 — 별도 파일 X.

### B. `open` 반복 제거 — "한 파일 안에서 open 반복 X"

같은 namespace 안에서 `open E213.X`, `open E213.Y` 같은 import
opens 가 *namespace 블록마다 반복* 되는 패턴 제거.  파일 top 에서
한 번만 `open`, 또는 파일 전체에 단일 namespace 사용.

검출: `grep -c "^open " <file>` 가 1 이상 발생하는 위치들.

전형적 패턴 (정리 후보):
```lean
-- BEFORE (반복):
namespace E213.Foo
open E213.Theory E213.Lens
theorem t1 : ... := ...
end E213.Foo

namespace E213.Foo
open E213.Theory E213.Lens
theorem t2 : ... := ...
end E213.Foo

-- AFTER (한 번):
namespace E213.Foo
open E213.Theory E213.Lens
theorem t1 : ... := ...
theorem t2 : ... := ...
end E213.Foo
```

이 두 원칙 (A + B) 은 Math audit 의 각 chunk §3 (Naming/조직)
권장의 *cross-cutting* version — chunk 별 fold/통합 후보 위에서
적용.

## 종합 — 정리 우선순위 (post-audit)

### Phase α (Quick, low risk)

1. **6 tiny cluster fold** (chunk audit §3 별 표시):
   - Trajectory (1 → SignedCut), Diagonal (2 → Lens), Search (2 →
     PatternCatalog/Meta), Hyper (3 → Numerical sub), Complex (4 →
     Numerical sub), CartesianVsDisjoint (3 → Tower)
2. **INDEX.md / API.lean 추가** (다수 cluster):
   - Analysis, Real213, SignedCut, Probability, DyadicFSM,
     Cohomology (HodgeConjecture/API.lean 패턴 적용)
3. **Cauchy 진화 단계 정리** — Sharper/KernelFree/Pure 통합.
4. **Sqrt2/3/5 변형 통합**.

### Phase β (Mid, 이동 작업)

5. **CayleyDickson Internal.Int213/Algebra213 promotion** (chunk C
   §5) — THEORY_AUDIT §4.2 의 Internal 3-성격 분리 와 함께:
   - Int213 → Theory/Int213/ (또는 Lens.Codomain)
   - Algebra213 typeclass → Theory/Algebra/ (또는 Lens/Algebra)
6. **AxiomSystems / Choice / Infinity 거주 재검토** —
   주제적 Theory.Raw reach-in (chunk A + B):
   - Lens 또는 Theory.Atomicity cousin 으로
7. **CayleyDickson 56 files sub-cluster 분할** (Tower / Integer /
   Levels / Lipschitz / Hurwitz / Misc).
8. **Real213 / SignedCut sub-organization**.
9. **Extras/ 해체** — 16 files origin cluster 로 분산.
10. **Theory.Raw.Mobius → Lib.Math.Mobius213 이동** (THEORY_AUDIT
    §4) — 3 reach-in 파일 정리 (chunk C/I 의 OneAsGlue,
    RotationGeometry, AlgebraTowerCapstone).

### Phase γ (Long-term, design 결정)

11. **per-modulus FSM 파일 통합** (cross-cutting B-A) — DyadicFSM
    의 ~60 per-modulus 파일.
12. **G42–G49 series consolidation** (chunk D) — 6 cluster 단일
    `Tower/` 로.
13. **PatternCatalog, DialogueAudit, GenerationRule** 거주 재검토
    (Meta vs research-notes).
14. **Lens layer Tier 1/Tier 2 분리** (LENS_AUDIT 권장) + Math 에
    Codomain.lean 같은 entry.

## Sub-organization 진행 (2026-05-13)

평탄 cluster 들의 sub-directory 분할 + tiny cluster fold 적용:

| Cluster | 평탄 → sub-org |
|---|---|
| CayleyDickson (chunk C) | 57 → 5 sub-dirs (Tower/Integer/Levels/Lipschitz/Misc) |
| Real213 (chunk B) | 57 → 7 sub-dirs (Core/Sum/Mul/Lattice/Bisection/ExpLog/Cauchy) |
| SignedCut (chunk B) | 35 → 6 sub-dirs (Core/CD/Hurwitz/Level/Bridge/Octonion) |
| Probability (chunk H) | 25 → 5 sub-dirs (Foundation/Distribution/Inequality/Limit/Bridge) |
| Cohomology (chunk G) | top-level 29 → 10 + 2 sub-dirs (Examples/Bridge) |
| DyadicFSM (chunk F) | top-level 33 → 14 + 4 sub-dirs (Product/Signature/Forward/Tier) |
| Diagonal + EpsilonDeltaModulus | → Modulus (tiny fold) |

§5 priority 의 Phase β (sub-organization) 대부분 실행 완료.
