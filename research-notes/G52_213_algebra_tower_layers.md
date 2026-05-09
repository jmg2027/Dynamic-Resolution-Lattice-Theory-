# G52 — 213 대수 타워 레이어별 관측

각 레이어를 *2ⁿ개 nat 컴포넌트* 구조로 indexing.  L0~L5 둘러봤다.

## 레이어 구조 (2ⁿ-component scheme)

| 층 | nat 수 | 용어 | 가능한 base |
|---|---|---|---|
| L0 | 1 | 양수 | ℕ (유일) |
| L1 | 2 | 부호화 정수 | ℤ (유일, Grothendieck) |
| L2 | 4 | (분기점) | ZI = ℤ[i], ZOmega = ℤ[ω], ZSqrt[D] |
| L3 | 8 | (L2 × L2) | Lipschitz / ZOmegaDouble / ... |
| L4 | 16 | (L3 × L3) | Cayley / ZOmegaQuad / ... |
| L5 | 32 | (L4 × L4) | Sedenion / ZOmegaOct / ... |

L0, L1은 base 분기 없음. L2부터 갈라짐.

## 각 레이어 관측

### L0: ℕ
- 1 nat 성분.
- 가환 monoid (덧셈, 곱셈).
- 음수 부재 → ring 아님.
- `3 - 5` 결과: `0` (truncated).

### L1: ℤ
- 2 nat 성분 (Grothendieck pair).
- 가환환 (모든 ring axiom).
- conj: identity (involution trivial).
- normSq: `a²` (자체 제곱).

### L2 (분기점)
**ZI = ℤ[i]** vs **ZOmega = ℤ[ω]** 첫 비교:

| 성질 | ZI | ZOmega |
|---|---|---|
| ω의 minimal polynomial | x² + 1 = 0 | x² + x + 1 = 0 |
| `(1+ω)(1-ω)` | 2 | 2 + ω |
| `(1+ω)²` | 2i | ω |
| `\|3+4ω\|²` | 25 | 13 |
| **유닛 수 (\|x\|²=1)** | **4** (±1, ±i) | **6** (±1, ±ω, ±ω²) |
| 격자 형태 | 정사각 | 육각 |

L2 분기는 본질적으로 **유닛 군 위수**의 차이 (Z₄ vs Z₆).

### L3 (L2 × L2)
**ZI 갈래 (Lipschitz)** vs **ZOmega 갈래 (ZOmegaDouble)**:

공통:
- 비가환 (Layer 1 손실)
- 결합성 유지
- 좌·우-교대성, 유연성
- 노름 곱셈

다른 점:
- 곱셈표 구조 다름.  ZI에서 `e₂² = -1` 균일.  ZOmega에서 `e₂² = -1 - ω` (base 관계 보존됨).
- 동일 좌표 `(1,1,1,1)`의 norm: ZI에서 4, ZOmega에서 2.
- L3 전체 유닛 군 위수도 다를 것 (확인 안 함).

### L4 (L3 × L3)
**Cayley** vs **ZOmegaQuad**:

공통:
- 비가환, **비결합** (Layer 2 손실)
- 교대성, 유연성 유지
- 노름 곱셈 유지

### L5 (L4 × L4)
**Sedenion** vs **ZOmegaOct**:

공통:
- 비결합 (이전 layer에서 이미 손실)
- 교대성도 깨짐
- **노름 곱셈 깨짐** (Layer 3 손실)

다른 점:
- Sedenion: simple zero divisor `(eᵢ + eⱼ)·(eₖ + eₗ) = 0` 존재.
- ZOmegaOct: 16²·16² ≈ 65k brute-force 결과 simple zero divisor **0개**.
- norm-mult 깨짐의 *형태*가 다름.

## 패턴 정리

**Threshold INDEX 불변** (base 무관):
- L1: 음수 도입.
- L3: 가환성 손실.
- L4: 결합성 손실.
- L5: 노름 곱셈 손실.

**Layer 분기점**:
- L2 분기: 어떤 minimal polynomial로 ω 정의? (i² = -1 vs ω² + ω + 1 = 0 vs √D² = D ...)
- L2 분기 → L3, L4, L5 전체 algebraic 구조에 *영향*은 가지만 *threshold INDEX 변경하지 않음*.

## 사용자 가설 (G50-G51에서 articulate한)

> 2-axis (CD level) + 3-axis (base) bi-axial classification

**부분 검증됨**:
- 2-axis가 threshold INDEX 결정 ✓ (양 ladder에서 일치)
- 3-axis가 specific algebra + failure type 결정 ✓ (Sedenion vs ZOmegaOct에서 ZD 출현 차이)

**미검증**:
- 다른 base (ZSqrt[D], 다양한 D)에서도 같은 패턴인가?
- L4, L5에서 두 base의 algebra가 어떤 구체 isomorphism / Brauer-class에 해당하나?
- "3-axis"를 어떤 *invariant*로 표현 가능한가? (격자 군의 위수? Galois 군? minimal polynomial 차수?)

## 다음 가능 작업 (mechanical)

1. **L2 다른 base들** (ZSqrt[-2], ZSqrt[-7], ZSqrt[-11] 등) 비교: 어느 D 값이 어느 layer에서 어떤 행동을 일으키나?
2. **L5 ZD 검색을 더 큰 계수로**: 계수 ±1, ±2 조합에서 ZOmegaOct에 ZD 있나?
3. **L6 (64-dim)**: 두 ladder 모두에서 어떤 추가 손실 일어나나? 표준에서는 trigintaduonion 차원.
4. **유닛 군 layer별 trace**: 각 base의 unit group 위수를 layer별로 추적, 유닛 군이 어떻게 변하는지 관측.

이 모두 *213-native*: 특정 외부 frame (Hurwitz, Frobenius 등) 없이 각 layer의 자체 데이터만 봄.
