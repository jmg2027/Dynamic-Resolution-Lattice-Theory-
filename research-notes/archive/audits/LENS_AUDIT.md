# Lens/ Layer Audit

**Audit date**: 2026-05-12.

**Subject**: `lean/E213/Lens/` — 103 .lean files across 13 sub-
clusters + 16 top-level files; 9608 total lines.

**Reference**: `lean/E213/ARCHITECTURE.md` (canonical layer spec
2026-05-12, **2-tier API** for Lens layer specifically).

## 0. Summary

| Cluster (sub) | Files | Lines | Spec status |
|---|---|---|---|
| `Algebra/` | 4 | 303 | 1 violation (CardinalityLB → Lib) |
| `AxiomLenses/` | 7 | 235 | ✓ |
| `Characterisation/` | 2 | 302 | ✓ |
| `Compose/` | 7 | 852 | ✓ |
| `Instances/` | 29 | 3099 | 1 violation (Reach → Lib) |
| `Internal/Algebra/` | 4 | 217 | ✓ |
| `Lattice/` | 7 | 750 | ✓ |
| `Leaves/` | 5 | 987 | 3 violations (Mod3, ModNat, RefinesParity) |
| `Morphism/` | 8 | 752 | ✓ |
| `Properties/` | 10 | 580 | 1 violation (ABRefines) |
| `Refines/` | 2 | 62 | ✓ |
| `Universal/` | 2 | 225 | ✓ |
| top-level | 16 | (above) | (aggregators + 5 content files) |

**Total**: 103 files, 9608 lines.  **6 ring violations** (Lens → Lib).
0 Lens → App, 0 Lens → Meta (Meta 는 ring-independent 라 허용).

## 1. Ring violations (Lens → Lib)

```
┌─────────────────────────────────────────────────────────────────────┐
│ # │ File                          │ Lines │ Lib import             │
├─────────────────────────────────────────────────────────────────────┤
│ 1 │ Algebra/CardinalityLB.lean    │ 147   │ Infinity.LensCardinality, NatHelpers.{Gcd213, AddMod213} │
│ 2 │ Instances/Reach.lean          │ 383   │ NatHelpers.IntHelpers  │
│ 3 │ Leaves/Mod3.lean              │  84   │ NatHelpers.AddMod213   │
│ 4 │ Leaves/ModNat.lean            │ 192   │ NatHelpers.{Infinity.LensCardinality, AddMod213, Gcd213} │
│ 5 │ Leaves/RefinesParity.lean     │  94   │ NatHelpers.AddMod213   │
│ 6 │ Properties/ABRefines.lean     │ 109   │ NatHelpers.AddMod213   │
└─────────────────────────────────────────────────────────────────────┘
```

**공통 패턴**: 모든 위반이 `Lib.Math.NatHelpers.*` (modular arith
helpers: AddMod213, Gcd213, IntHelpers).  처리 옵션:

- (a) **NatHelpers 의 사용 fragment 를 Meta/Tactic/ 또는 Lens
      내부 helper 로 이동** — modular arith 가 lens-level 정리에
      필수면 Lens 가 자기 helper 보유.
- (b) **위반 파일을 Lib 로 이동** — `Lib/Math/Modular/`, 또는
      `Lib/Math/LensCardinality/` 같이.  특히 Algebra/CardinalityLB
      과 Leaves/ModNat 가 사실 Lib 콘텐츠 성격.
- (c) **NatHelpers 의 일부를 Term/ 또는 Theory/ 로 끌어내림** —
      modular arith 가 layer 아래 layer 의 도구라면.

## 2. 2-tier API discipline (ARCHITECTURE.md 2026-05-12)

### Tier 1 — Core API (`Lens/API.lean`)

본질 — 새 lens 추가시에도 안 바뀜:

- HV1: `Lens (α : Type)`, `Lens.view`, `Lens.mk`, projections
- HV2: `Lens.equiv`, `Lens.refines` + closures, `Lens.compose`
- HV3: `Universal.universalLens`, `Universal.Flat`,
       `Universal.factorization`

### Tier 2 — 확장 sub-API (필요시 import)

- `Lens/Instances.lean` — concrete lens catalog
- `Lens/Lattice.lean` — join/meet/Family
- `Lens/Compose.lean` — composition operators
- `Lens/Properties.lean` — predicate catalog
- `Lens/Codomain.lean` — *(TBD)* codomain type catalog

### 현재 API.lean 평가

현재 `Lens/API.lean` 이 HV1–HV6 (Type, Equivalence, Initiality,
Lattice, Composition, Canonical Form) 모두 expose — **Tier 1
+ Tier 2 가 섞임**.  새 framing 으로:

- Tier 1 으로 좁히기: HV1, HV2 (basic algebra 만), HV3 (universal)
- HV4 (Lattice), HV5 (Composition), HV6 (Canonical Form) 은 별도
  sub-API 로 분리

## 3. Top-level 16 files 의 성격

| 파일 | 줄수 | 분류 |
|---|---|---|
| `API.lean` | 75 | aggregator (Tier 1 + Tier 2 섞임 — 정리 후보) |
| `LensCore.lean` | 69 | **Tier 1 content** (Lens type + view) |
| `SemanticAtom.lean` | 425 | Theory-flavored thesis hub (atom-of-meaning) |
| `Initiality.lean` | 121 | **Tier 1 content** (universal property) |
| `EqPW.lean` | 187 | pointwise eq helper (funext-avoidance) |
| `Diagonal.lean` | 105 | sq L classification (Properties extension) |
| `Algebra.lean` | 25 | sub-cluster aggregator |
| `Characterisation.lean` | 14 | sub-cluster aggregator |
| `Compose.lean` | 22 | sub-cluster aggregator |
| `Instances.lean` | 72 | sub-cluster aggregator |
| `Lattice.lean` | 23 | sub-cluster aggregator |
| `Leaves.lean` | 18 | sub-cluster aggregator |
| `Morphism.lean` | 30 | sub-cluster aggregator |
| `Properties.lean` | 31 | sub-cluster aggregator |
| `Refines.lean` | 14 | sub-cluster aggregator |
| `Universal.lean` | 13 | sub-cluster aggregator |

10 / 16 이 sub-cluster aggregator.  실제 콘텐츠 파일은
LensCore, SemanticAtom, Initiality, EqPW, Diagonal 만.

## 4. Naming + sub-cluster 정리 후보

13 sub-cluster 는 **너무 세분화**.  실제 의미 기반 정리 후보:

| 통합 후 | 현재 sub-cluster | 의미 |
|---|---|---|
| `Core/` | (new) ← LensCore + Initiality + EqPW + SemanticAtom | Lens type + universal property + identity |
| `Algebra/` | Algebra + Refines + Lattice + Compose | Lens family 의 algebraic structure |
| `Universal/` | Universal | universal Lens construction |
| `Instances/` | Instances + Leaves | concrete lens catalog (Leaves 는 specific family) |
| `Properties/` | Properties + Characterisation + Morphism + Diagonal | predicates + characterizations + morphism shape |
| `AxiomLenses/` | AxiomLenses | Lean-axiom Lens witnesses (specific, 별도 유지) |
| `Internal/` | Internal/Algebra | internal proof infra |

**13 → 7 sub-clusters** 가능.

### 보조 — Universal Lens 의 위치

현재 `Meta/UniversalLens/` (universal Lens 의 metatheorem witnesses
— Nat2Inj, Q213Inj, TripleCapstone, Padding) 이 *Meta* 거주.  이는
ring-independent meta 라기보다 **Lens layer 의 핵심 정리** —
Universal Lens 의 instance/witness.

**이동 후보**: `Meta/UniversalLens/` → `Lens/Universal/` 안 sub-cluster
(또는 Lens/Universal/Witnesses/).

## 5. 처리 priority

### Quick wins (작음, 명확)

1. **위반 처리** (6 파일):
   - Algebra/CardinalityLB, Leaves/ModNat → Lib 로 이동 (Lib 콘텐츠
     성격이 더 강함)
   - 나머지 4 (Leaves/Mod3, Leaves/RefinesParity, Properties/
     ABRefines, Instances/Reach) — NatHelpers fragment 인라인 또는
     Lib 로 이동
2. **`Lens/API.lean` 의 2-tier 분리**:
   - Tier 1 만 API.lean 으로 좁히기 (HV1 + HV2 + HV3)
   - HV4, HV5, HV6 → `Lens/{Lattice, Compose, Properties}.lean` aggregator 들로

### Mid-term

3. **Meta/UniversalLens/ → Lens/Universal/** 이동
4. **Sub-cluster 통합** (13 → 7) — 큰 git mv + namespace 정리

### Long-term

5. **`Lens/Codomain.lean` 신규** — codomain type catalog (Bool213,
   Nat213, Int213 등) re-export
6. **Hook 확장**: Lens.<X> reach-in 차단 (Theory.Raw 와 같은 패턴)

## 6. 결정 보류

위 §4 (sub-cluster 통합) §5 (단계별 작업) 의 모든 작업은 **기록만**
한 상태.  Mingu Jeong 결정 대기.
