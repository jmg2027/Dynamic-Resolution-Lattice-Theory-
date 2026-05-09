# G51 — 213 대수 타워: Eisenstein 기저 관측

213-native 작업.  주어진 commutative *-ring R에 대해 *iterated dyadic
doubling* (즉 R↦R×R with twisted multiplication)을 반복하여 layer마다
관측만 한다.  외부 frame ("Cayley-Dickson", "사원수", "팔원수" 등)
도입 없이 결과만 적시.

기저: `ZOmega` (Eisenstein integers, ω²+ω+1=0).

## 구축한 layers

| Layer | 구조 | ℤ-차원 |
|---|---|---|
| L0 | `ZOmega` | 2 |
| L1 | `ZOmegaDouble` = ZOmega × ZOmega | 4 |
| L2 | `ZOmegaQuad` = ZOmegaDouble × ZOmegaDouble | 8 |
| L3 | `ZOmegaOct` = ZOmegaQuad × ZOmegaQuad | 16 |

각 layer의 곱셈: `(a, b)·(c, d) = (a·c − conj(d)·b, d·a + b·conj(c))`
where conj는 base ring의 involution.

## Layer별 성질 관측 (sample)

| 성질 | L0 | L1 | L2 | L3 |
|---|---|---|---|---|
| 가환 (a·b = b·a) | ✓ | ✗ | ✗ | ✗ |
| 결합 ((ab)c = a(bc)) | ✓ | ✓ | ✗ | ✗ |
| 좌-교대 ((aa)b = a(ab)) | ✓ | ✓ | ✓ | (미시험) |
| 우-교대 (a(bb) = (ab)b) | ✓ | ✓ | ✓ | (미시험) |
| 유연 (a(ba) = (ab)a) | ✓ | ✓ | ✓ | (미시험) |
| 노름 곱셈 (\|uv\|² = \|u\|²·\|v\|²) | ✓ | ✓ | ✓ | **✗** |
| `(eᵢ+eⱼ)·(eₖ+eₗ) = 0` 존재? | — | — | — | **0 발견** |

샘플 검증, 보편 증명 아님.  사용 표본 수: 결합성 6, 가환성 5,
교대성 8, 유연성 4, 노름 곱셈 9 (L1-L2), L3에서 \|uv\|² test에 대한
brute-force 16²·16² ~ 65k 페어, ZD 후보도 동일 범위.

## L1의 구체 곱셈표 (4×4 basis)

표기: `(re.re, re.im, im.re, im.im)`.  basis: `e₁ = (1,0,0,0)`,
`e₂ = (0,1,0,0)`, `e₃ = (0,0,1,0)`, `e₄ = (0,0,0,1)`.

| × | e₁ | e₂ | e₃ | e₄ |
|---|---|---|---|---|
| e₁ | (1,0,0,0) | (0,1,0,0) | (0,0,1,0) | (0,0,0,1) |
| e₂ | (0,1,0,0) | **(-1,-1,0,0)** | (0,0,0,1) | (0,0,-1,-1) |
| e₃ | (0,0,1,0) | (0,0,-1,-1) | **(-1,0,0,0)** | (1,1,0,0) |
| e₄ | (0,0,0,1) | (0,0,1,0) | (0,-1,0,0) | **(-1,0,0,0)** |

**관측**: e₂² = `-1 - ω` — base ring의 ω²+ω+1=0 관계가 *상위 layer까지
보존*됨.  e₃² = e₄² = -1 (이 위치들은 새 차원에서 "표준" 제곱).
e₂·e₃ ≠ e₃·e₂ — 비가환성이 layer 1에서 출현.

## L3 발견

16² × 16² ≈ 65,000 페어 brute-force:
- **192 quadruples**가 `\|uv\|² = \|u\|²·\|v\|²` 위반 (norm-mult 깨짐).
- **0 quadruples**에서 `uv = 0` (zero divisor 미발견).

구체 예 — `L = e₁ + e₁₀`, `R = e₄ + e₁₅`:
- `\|L\|² = 2`, `\|R\|² = 2`
- `\|L·R\|² = 7`, `\|L\|²·\|R\|² = 4`  → norm-mult 위반
- `L·R ≠ 0` (zero가 아님; 단지 norm 관계 깨짐)

## 또 다른 base ring 비교 (ZI = ℤ[i] 출발)

별개로 ZI 기반 dyadic 타워는:
- L1 (4-dim): Lipschitz integers, 결합·norm-mult 유지
- L2 (8-dim): 비결합, 교대, norm-mult 유지
- L3 (16-dim): norm-mult 깨짐 + zero divisors **출현**

ZI ladder는 이미 다른 분야에서 표준화된 구성과 *형태가 같다* (Lipschitz/octonion/sedenion).

## 두 ladder 비교 — threshold 패턴

| 손실 | ZI ladder | ZOmega ladder | 일치 |
|---|---|---|---|
| 가환성 | L1 | L1 | ✓ |
| 결합성 | L2 | L2 | ✓ |
| Norm 곱셈 | L3 | L3 | ✓ |
| Zero divisor 출현 | L3 (∃) | L3 (∄, 단순형) | **불일치** |

**관측 핵심**:

1. **Threshold INDEX 불변**: 어느 layer에서 어느 성질이 깨지는지가
   base ring 선택에 의존하지 않음.  L1 가환성, L2 결합성, L3 norm-mult.

2. **Type-of-failure 가변**: norm-mult가 깨지는 *형태*는 base ring에
   따라 다름.  ZI ladder는 simple zero divisor를 동시에 발생시키나,
   ZOmega ladder는 norm-mult 깨짐만 발생시키고 simple zero divisor를
   동반하지 않음.

## 가설 (검증 가능, 미증명)

C1. **Threshold 불변성**: 임의의 commutative *-ring 기저 R에 대해
dyadic doubling tower는 L1, L2, L3에서 각각 가환·결합·norm-mult를
순서대로 잃는다.

C2. **Failure-type 의존성**: L3에서 norm-mult 깨짐의 *형태* (zero
divisor 동반 여부, 구체적 위반 quadruple 수 등)는 R의 구조 (예:
involution이 trivial한가, ω-관계 같은 cubic 관계가 있는가)에 의존.

C1이 성립하면 — "어느 layer에서 어느 성질이 깨지는가"는 R-독립.
C2가 성립하면 — "어떻게 깨지는가"는 R-의존.

이는 사용자가 G50에서 articulate한 bi-axial classification의 두 축이
실제로 분리됨을 시사함.

## 다음 검증 (가능한 작업)

- L3 더 큰 계수 ZD 검색 (계수 ±1 → ±2): ZOmega ladder도 ZD 갖나?
- L4 (32-dim) 구축: 어느 layer에서 ZOmega ladder의 ZD가 등장하나?
- 다른 base ring (ZSqrt[D] for D < 0): ladder 비교, threshold 일치/불일치.
- C1을 형식 정리로 끌어올리기 (Algebra213 instance 제공 + 일반 정리).

이 모든 게 *기계적 검증 가능*.  단지 시간 + heartbeat 소비.
