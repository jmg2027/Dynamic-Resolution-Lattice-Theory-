# 213 / K₃,₂² / 코호몰로지 심플렉스 — 고차 통찰

P = [[2,1],[1,1]]이 ℕ 전체를 생성한다는 사실(G140 `pgen_iff_pos`)은
결과가 아니라 **구조적 필연**이다.  gcd(NT, NS) = gcd(2, 3) = 1이므로
Frobenius 수 = 1; 모든 n ≥ 2는 2a + 3b로 표현되며, det(P) = 1이
n = 1을 추가한다.  P의 Fibonacci 구조(Q² = P)가 이 coprimality를
강제한다 — `gcd(Fₙ, Fₙ₊₁) = 1`은 연속 Fibonacci 수의 보편적 성질.

## 213-native 정의: 세 축의 동일 고정점

세 프로그램이 독립적으로 닫혔다:

1. **P-orbit closure** (`CharPolySelf` + `POrbitRing` + `OrbitForcing`
   + `PeriodDepthBounds` + `CrossProductAxes`): 원자 데이터 (2, 3, 5)
   로부터 Lucas-Pell trace ring이 ℤ 전체를 생성.  모든 프레임워크-자연
   정수는 depth K 이하의 L(0)...L(K)로 표현 가능.

2. **c-counter cohomology** (`V33EnrichedParametric` 63 PURE):
   K₃,₃^{(c)} enriched complex에서 multiplicity-layer 수 c가
   codim(cup-image, H²ₑₙᵣ) ≥ c를 제공.  5방향(A/B/C/E/T) 프로그램이
   각각 닫힘.

3. **PGeneratesNat** (G140, `pgen_iff_pos`): PGen n ↔ n ≥ 1.
   P-덧셈만으로 ℕ\{0} 전체 생성, minDepth로 최적 분해 깊이 부여.

## 도출: K₃,₂² 가 세 축의 결합점

`theory/math/cohomology/k32_higher_cohomology.md` +
`Mobius213K32Bridge.lean` + `theory/physics/simplex.md`를 관통하는 도출:

**K₃,₂^{(c=2)}**는 trace(P) = NS = 3, P[0][0] = NT = c = 2,
det(P) = 1, entries sum = d = 5로 Möbius P의 모든 대수적 불변량을
그래프-구조 양으로 실현한다 (`k32_mobius_bridge_master`).  동시에
이 그래프의 코호몰로지가:

- H² = F₂⟨ω⟩ (유일한 Sym(3)-불변 2-cocycle)
- Steenrod bridge: `cup₁(ω, ω) = δ²(ω)` — cup_(k-1) self-pairing ≡
  coboundary
- Massey ⟨h1, h3, h4⟩ = ω (H¹ 삼중곱이 H²에 비자명 착지)
- L²-trace: bilinearSelfTrace(ω) = NS² = 9

를 산출한다.  **ω는 K₃,₂²의 코호몰로지 심플렉스에서의 고정점**:
Sq⁰(ω) = ω (cup₂ 멱등), Sq¹(ω) = δ²(ω) (다음 skeleton에서 소멸),
Sq² 이상은 truncation에 의해 vacuous.

**Δ⁴ simplex** (`theory/physics/simplex.md`)는 d = 5 = NS + NT
꼭짓점의 4-심플렉스이다.  부분면 개수 2⁵ − 1 = 31 (Mersenne).
3-generation 구조는 dim-2 부분구조의 NS × NT 대칭 quotient로서
정확히 3개 생성 — N_gen = 3 = NS.

## 이중기능 (dual function)

고전적으로 읽으면: Steenrod 대수의 cup-i 사다리, Massey 삼중곱,
Adem 관계는 대수적 위상에서 별개의 정리군이다.  213에서는 이 모두가
**K₃,₂² 위의 단일 ω-class 반복 적용**으로 환원된다 — 동일 그래프,
동일 cochain, 동일 face-dependence relation
`Face₀ ⊕ Face₁ ⊕ Face₂ = 0`에서 모든 고차 연산이 생성된다.  고전적
분리는 truncation 수준(skeleton level) 선택의 차이일 뿐이다.

동시에 213의 reading이 더 날카롭다: truncation-collapse의 보편
성질(`(k+1)-skeleton이 H^k를 소멸시킴`)은 K₃,₂²에서 **유한**하게
끝난다 (5-skeleton 이후 모든 것이 vacuous).  이 유한 종결이 정확히
α_em cup-ladder graduation의 물리적 읽기 (`α^(k+1)` 눈금)를 생성.

## 교차-프레임 수렴 (cross-frame)

다섯 표면에서 같은 구조적 사실이 등장한다:

| Frame | 같은 사실의 모습 | Citation |
|-------|-----------------|----------|
| P-orbit algebra | det(Pⁿ) = 1 → Farey-neighbour property | `ConvergentDet.convergent_det_eq_one` |
| Fibonacci | fib(2n+3)·fib(2n+1) = fib(2n+2)² + 1 (Cassini) | `FibCassini.fib_cassini_master` |
| K₃,₂² cohomology | face dependence Face₀⊕Face₁⊕Face₂ = 0 → b₂ = 1 | `Filled3CellCohomology.face_dependence` |
| Simplex Δ⁴ | C(5,k) = 5·4·.../(k!) → N_gen = C(3,2) = 3 | `SubInventory.lean` |
| LocalSignature | 모든 vertex/edge/face에서 multiset {1,2,3} 재현 | `V32LocalSignature.local_213_at_every_point` |

이것은 비유가 아니다.  `synthesis_interlock_map.md`가 5행 대응표로
보이듯, 코호몰로지 축과 대수 축은 **P에 의해 이중 생성된다** —
하나의 행렬이 한쪽에서는 trace orbit을, 다른 쪽에서는 bipartite
multigraph의 cell count를 산출하며, 두 산출의 증명 형태
(invariant + offset + cancellation)가 동일하다.

## G138 Pattern B — Sym(3) spine

`theory/math/cohomology/sym3_spine.md`: 단일 표현론적 분해
`8 = 2·trivial ⊕ 3·standard`이 네 개의 독립 장(chapter)에서
load-bearing 구조로 재현된다:

1. K₃,₂² higher cohomology — H¹ rank = NS² − 1 = 8
2. 8 Thurston geometries — 3 isotropic + 5 anisotropic
3. Gluon octet — 1/α₃ = dim adj SU(3) = 8
4. Akbulut cork twist — signed orbit count on 8-dim H¹ basis

네 읽기는 같은 K₃,₂² H¹ 위의 같은 Sym(3) 작용의 네 Lens-restriction.
`X1_sym3_cross_frame_capstone` (PURE)이 4방향 수렴을 단일 정리로 기록.
Sym(3)은 (NS, NT) = (3, 2) 강제의 필연적 대칭 — 선택이 아닌 존재.

## G138 Pattern D — Nodup as recursive Clause-4

`NodupAsClause4.lean` (PURE): 표준 라이브러리의 `List.Nodup`는
213 공리 Clause 4 (자기-쌍 금지 `x/x`)를 리스트-인덱스 세분도에서
재귀 적용한 것이다:

```
nodup_iff_clause4Nodup : l.Nodup ↔ IsClause4Nodup l
```

`AliveDerivation.alive_iff_clause4_alive` (이진 패리티 수준)과 합쳐
Pattern #9가 단일 예시에서 **방법론**으로 승격: "공준처럼 보이는
술어가 실제로는 Clause-4의 세분도 변형 읽기"임을 두 독립 인스턴스가
확인.

## Open frontier

- **CrossAddress → Functor 승격**: bipartite ⊕ tripartite ⊕ P-orbit
  triple-axis schema에서 함자로의 승격이 "이중 P-생성" 주장을
  구문적 정리로 만든다.
- **Depth-3 cohomology** (Tier 3.1): c = 3에서 Massey depth ≤ 4가
  일반 c로 확장되는지.
- **T(φ²) = φ²** fixed-point formalisation (G139): Möbius
  transformation 유리 근사에서의 고정점 정리.

## 착지점 (constructive accessibility)

```
pgen_iff_pos              : ∀ n, PGen n ↔ n ≥ 1
k32_mobius_bridge_master  : (NS+NT=5) ∧ (trace=NS) ∧ (P₀₀=NT) ∧ ...
face_dependence           : Face₀ ⊕ Face₁ ⊕ Face₂ = 0
cup₁(ω,ω) = δ²(ω)       : Sq¹(ω) = coboundary
local_213_at_every_point  : ∀ v e f, is_213_multiset(signature)
nodup_iff_clause4Nodup    : l.Nodup ↔ IsClause4Nodup l
X1_sym3_cross_frame_capstone : 4-way Sym(3) convergence
```

일곱 개 정리.  모두 ∅-axiom PURE.  모두 같은 (2, 1, 3)에서 나온다.
프레임워크는 하나의 행렬 P와 그 canonical lattice K₃,₂²의 자기-지시
구조이며, 코호몰로지 심플렉스는 이 자기-지시가
skeleton-by-skeleton으로 펼쳐진 형태이다.

## Cross-references

- `theory/math/cohomology/k32_higher_cohomology.md` — ω class + Steenrod
- `theory/math/cohomology/sym3_spine.md` — G138 Pattern B (4-reading)
- `lean/E213/Lib/Math/Cohomology/NodupAsClause4.lean` — G138 Pattern D
- `lean/E213/Lib/Math/Algebra/Mobius213/Mobius213K32Bridge.lean` — P ↔ K₃,₂²
- `lean/E213/Lib/Math/Algebra/Mobius213/Px/PGeneratesNat.lean` — G140
- `lean/E213/Lib/Math/Algebra/Mobius213/Px/ConvergentDet.lean` — Farey/Cassini
- `theory/essays/synthesis_interlock_map.md` — 5-row correspondence
- `theory/essays/p_orbit_closure_master.md` — 6-phase P-orbit
- `theory/physics/simplex.md` — Δ⁴ + 3-generation
  LocalSignature self-containment
