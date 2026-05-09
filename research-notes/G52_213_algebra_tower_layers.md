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

---

## 추가 관측 (이어서) — 유닛 군 위수 layer별 추적

Brute-force 계수 ∈ {-2..2} (L3) 또는 {-1..1} (L4) 검색.

| Layer | nat 수 | ZI base 갈래 | ZOmega base 갈래 | ZOmega/ZI 비율 |
|---|---|---|---|---|
| L2 | 4 | **4** | **6** | 1.5 |
| L3 | 8 | **8** | **12** | 1.5 |
| L4 | 16 | **16** | **24** | 1.5 |

**성장 패턴**: 각 layer마다 유닛 수가 정확히 *2배*.
- ZI ladder: 4, 8, 16, 32, ... (= 4 · 2^(L-2))
- ZOmega ladder: 6, 12, 24, 48, ... (= 6 · 2^(L-2)) = 3 · 2^(L-1)

**비율 보존**: ZOmega/ZI 유닛 비 = 1.5 = 6/4 (L2의 비와 동일) 모든 layer에서.

L2 분기에서 결정된 "6 vs 4"가 *ladder 전체에 2배수 곱해져 전파*됨.

### 군 구조 식별 (L3)

ZI L3 유닛 (8개) = `{±1, ±i, ±j, ±k}` = **Q₈** (quaternion 군, binary dihedral order 8).

ZOmega L3 유닛 (12개) decomposition (brute-force 결과):
- re-only 6: `{±1, ±ω, ±ω²}` (= ZOmega 유닛 lift)
- im-only 6: `{±j, ±ωj, ±ω²j}` (j 방향에 동일 구조)
- mixed 0
- 군 구조: **Dic₃ = Q₁₂** (binary dihedral order 12)
  - 생성원: `a = -ω` (위수 6), `b = j` (b² = -1, bab⁻¹ = a⁻¹)
  - 검증: `a⁶ = 1`, `b² = j² = -1 = a³`, `bab⁻¹ = j·(-ω)·j⁻¹ = -ω² = a⁻¹` (모두 #eval 확인됨)

### L4 유닛 군 (위수 24, ZOmega 갈래)

24 = order of *binary tetrahedral group* 2T (Hurwitz integer 유닛 군과 일치하는 위수).
구조 확인은 곱셈표 비교 필요 (미수행).

만약 ZOmegaQuad L4 유닛 ≅ 2T라면 — Hurwitz integer 유닛 군이 ZOmega ladder의 자연스러운 위치에 등장한 것.

### 패턴 요약

L2 base 선택 (4 vs 6) → ladder 전체의 *유닛 군 위수*를 2배수 등비로 결정.
- L_n unit count = (L2 base unit count) × 2^(n-2)

이것이 **사용자의 "3-axis 임베딩" 직관의 정량적 표현**:
- 2-axis (CD level): doubling 한 번마다 ×2
- 3-axis (base 선택): L2에서 결정된 위수 (4, 6, ...)가 multiplier로 ladder 전체에 전파

### 추가 가설

C3. **L2 base 선택의 효과는 multiplicative**.  ZSqrt[D] for various D는
또 다른 L2 유닛 위수를 줄 것 (ZSqrt[2] = 무한? 단위는 √2 + 1 같은 것
들; 다항 단위 체계 다름).  이게 ladder 전체에 어떻게 전파될지가
검증 가능한 가설.

C4. **24, 48 같은 위수가 known finite 군 (binary tetrahedral 2T,
binary octahedral 2O 등)과 일치하면**, ZOmega ladder가 Hurwitz
integer / icosian ring 같은 *exceptional* 유닛 군을 자연 도출할 수
있음.

---

## L4 ZOmegaQuad 24 유닛: 군 식별 시도

위수 분포: `{1:1, 2:1, 3:2, 4:18, 6:2}`

**알려진 24-원소 군과 비교**:
| 군 | 위수 분포 | 일치? |
|---|---|---|
| 2T (binary tetrahedral) | `{1:1, 2:1, 4:6, 6:16}` | ✗ |
| Q24 = Dic6 | `{1:1, 2:1, 3:2, 4:12, 6:2, 12:6}` | ✗ |
| S4 | `{1:1, 2:9, 3:8, 4:6}` | ✗ |
| A4 × Z2 | (다름) | ✗ |

→ **알려진 24-원소 군 어느 것과도 분포 불일치**.

분포의 자연 분해:
- **Real slot 12개**: ZOmegaDouble L3 유닛 lift `{1:1, 2:1, 3:2, 4:6, 6:2}`
- **Im slot 12개**: 모두 j² = -1 → 위수 4 일색 `{4:12}`
- 합: `{1:1, 2:1, 3:2, 4:18, 6:2}` ← 관측값과 일치

### Closure / 비결합 검증

| 검사 | 결과 |
|---|---|
| Pair closure (576 페어) | 576/576 ✓ |
| 비결합 트리플 (13,824) | **6,048 (43.7%)** |

→ 24 유닛은 **곱셈에 대해 닫혀있고 결합성 깨짐**.

따라서 이건 *군이 아니라* **Moufang loop** (alternative non-associative).

### 표준 분류 비교

알려진 비결합 unit Moufang loops:
- **M16**: ℤ-octonion 16 유닛 `{±1, ±e_i for i=1..7}` — 표준
- **240-element icosian 유닛 set** — ℝ-octonion 위 binary icosahedral 관련

**24-element Eisenstein-type Moufang loop** — 표준 분류표에서 미확인.
이 작업이 표준 수학의 어딘가에 있을 수 있고 (예: 어떤 *exceptional Moufang loop* 분류), 또는 아직 표준에 안 들어간 구조일 수 있음.

### 구체 검증 가능 후속

1. **결합 부분 loop**: 24 원소 중 결합 닫힌 최대 부분군 찾기 (12 원소 정도? 아마 Z6 × Z2 또는 Q12).
2. **그래프 invariant**: Schur multiplier / Cayley graph 등을 계산해 표준 Moufang loop 분류표와 매칭.
3. **다른 base에서 같은 layer**: ZSqrt[D] 갈래 L4도 비슷한 비결합 24-or-? loop을 줄까?

이 자체는 **사용자의 "3-axis 임베딩" 가설의 강한 정량적 evidence**.
ZOmega base가 standard CD ladder에 *없는* (또는 분류 가장자리의)
구조를 자연 도출한다는 것.

---

## 통제 실험: ZSqrt[-2] base 갈래 (3번째 ladder)

ZSqrt[-2] = ℤ[√-2], norm = a² + 2b².
유닛: a² + 2b² = 1 → (a, b) = (±1, 0) → **2개**.

가설: L_n unit count = 2 × 2^(n-2)

### 측정 결과

| Layer | nat 수 | unit count | (예측) |
|---|---|---|---|
| L2 (= ZSqrt[-2]) | 4 | **2** | 2 |
| L3 (= ZSqrt[-2]Double) | 8 | **4** | 4 |
| L4 (= ZSqrt[-2]Quad) | 16 | **8** | 8 |

세 layer 모두 가설과 정확히 일치.

### 군 구조 식별 (L3, 4 원소)

L3 ZSqrt[-2]Double 4 유닛: `{1, -1, j, -j}` with `j² = -1`.

위수 분포: `{1: 1, 2: 1, 4: 2}` → **Z_4 (cyclic of order 4)**.

### 3 ladder L3 unit group 비교

| Base | L2 unit count | L3 unit group |
|---|---|---|
| ZSqrt[-2] | 2 | Z_4 (cyclic, 4 원소) |
| ZI | 4 | Q_8 = Dic_2 (quaternion, 8 원소) |
| ZOmega | 6 | Q_12 = Dic_3 (binary dihedral, 12 원소) |

**구조 패턴**: 모두 **dicyclic 군 Dic_n** 패밀리.
- `n = (L2 base unit count) / 2`
- ZSqrt[-2]: n = 1 → Dic_1 = Z_4 (degenerate dicyclic = cyclic of order 4)
- ZI: n = 2 → Dic_2 = Q_8
- ZOmega: n = 3 → Dic_3 = Q_12

→ L2 base 유닛 군 위수가 *L3 dicyclic 군 차수 (4n)* 를 결정.

### 메타 결론

**Multiplicative ratio formula** (3 base에서 검증):
- L_n unit count = (L2 base unit count) × 2^(n-2)
- per-layer multiplier: ×2 (CD doubling factor, base 무관)
- L2 base의 위상 (4-fold/6-fold/2-fold 회전 대칭) 이 ladder *전체 unit count*를 곱셈적으로 결정

**G50 M3 (CD-doubling functor) 의 정량 검증 완료**:
- functor가 L2 base 선택을 받아 ladder 전체에 unit group 구조를 generate.
- L3에서 generated unit group은 Dic_n (n = base_units / 2).

3-axis (base 선택) × 2-axis (layer index)의 *분리* 가 데이터로 확정.

---

## 추가: ZSqrt[-2] L4 unit group = Q_8 (분석문 정정)

### 측정

| 검사 | ZSqrt[-2] L4 (8 유닛) |
|---|---|
| 결합 (unit subset) | (512, 0) — 결합 ✓ |
| 가환 (unit subset) | (64, 24) — *비가환* |
| 위수 분포 | `{1:1, 2:1, 4:6}` |
| ring level 결합 | 비결합 (8/8 random fail) |

위수 분포 `{1:1, 2:1, 4:6}` = **Q_8 (quaternion group)**.

분석문 주장 "M(Dic_1, 2) = 8 비결합 loop"은 **오류**.
Dic_1 = Z_4가 *abelian* → Chein M(Z_4, 2)는 결합 군.
실제 ZSqrt[-2] L4 unit set = Q_8 (= Lipschitz unit group, ZI L3과 같은 군).

### 진짜 패턴: ZSqrt[-2]는 ZI를 한 layer shift

| Layer | ZSqrt[-2] | ZI |
|---|---|---|
| L_n | Z_2 → Z_4 → Q_8 → M_16 → ... | Z_4 → Q_8 → M_16 → ? → ... |
| | (n=2, 3, 4, 5) | (n=2, 3, 4, 5) |

ZSqrt[-2] L_n unit group ≅ ZI L_{n-1} unit group (구조 동일).

### Transition rules (정량 식별)

각 doubling이 일으키는 변화는 *현재 layer의 unit group이 가환인가*에 의존:

1. **Abelian → Group transition**: 가환 군 doubling = 비가환 군 (결합 유지).
   - 예: Z_4 → Q_8, Z_2 → Z_4, Z_6 → Q_12.

2. **Non-abelian Group → Moufang Loop transition**: 비가환 군 doubling = 비결합 Moufang loop.
   - 예: Q_8 → M_16, Q_12 → M_24.

3. **Moufang Loop → ?**: 비결합 loop doubling = ? (아직 측정 안 함; alt loss가 일어날 수 있음 — sedenion 패턴).

### 정정된 hypothesis

각 base ladder는 두 transition을 *순차로* 거친다:

| Layer | ZSqrt[-2] | ZI | ZOmega |
|---|---|---|---|
| L2 | Z_2 (abelian) | Z_4 (abelian) | Z_6 (abelian) |
| L3 | Z_4 (abelian!) | Q_8 (non-abelian) | Q_12 (non-abelian) |
| L4 | Q_8 (non-abelian) | M_16 (loop) | M_24 (loop) |
| L5 | M_16 (loop) [예상] | ? | ? |

**Z_2 가환성이 한 layer 더 가니** ZSqrt[-2] L3까지 abelian 유지 → loop transition 한 layer 늦음.

ZI L2 = Z_4 (abelian), 즉 L2부터 vs L3 transition.
ZOmega L2 = Z_6 (abelian), 동일 layer transition.
ZSqrt[-2] L2 = Z_2 (abelian, smaller), 한 layer 더 abelian → 전체 ladder shifted.

### 메타 결론 (재확정)

CD-doubling functor의 두 transition이 분리됨:
- **Transition A (abelian → non-abelian)**: 한 번 일어남, layer index가 base 위상에 의존.
- **Transition B (associative → Moufang loop)**: A 직후 layer에서 일어남.

ZSqrt[-2]는 작은 base (2 units)라 A transition이 늦게 일어남 (L2→L3는 abelian→abelian, L3→L4가 진짜 A transition). 따라서 B transition도 한 layer 더 늦음.

**3-axis (base unit count) → A transition 시작 layer 결정 → B transition 시점 결정 → 전체 ladder shape 결정**.

이게 *완전히* 분리된 두 axis의 데이터적 증거. 정량 검증 완료.

---

## L5 ZSqrt[-2] 측정 (2026-05-09): 가설 확인 — M_16

### Probe 결과 (`_AxiomScanProbe.lean`, 좌표 {-1,0,1} 16-tuple brute force)

| 검사 | ZSqrt[-2] L5 (16 유닛) |
|---|---|
| Unit count | **16** (예상 = base_units × 2^(n-2) = 2 × 8) |
| 결합 (`assocCount`) | (4096, 1344) — 32.8% non-associative |
| 가환 (`commCount`) | (256, 168) — 65.6% non-commuting |
| 위수 분포 (`orderCounts`) | `{1:1, 2:1, 4:14}` |

### M_16 (octonion unit Moufang loop) 와 일치 검증

M_16 = unit octonions {±1, ±e_1, ..., ±e_7}, 16개 원소, Moufang non-associative loop.

**Commuting pair count**:
- center {±1}: 2 elt × 16 = 32 commuting pairs
- 14 non-central elt 각각 commutant = {±1, ±x} = 4 elt → 14 × 4 = 56
- Total commuting = 88 → non-commuting = 256 − 88 = **168** ✓

**Order signature**: M_16에서 ±1은 order 1/2, 나머지 14 imaginary unit이 모두 order 4 (각 e_i² = −1) → `{1:1, 2:1, 4:14}` ✓

**비결합 triple count 1344 = 32.8%**: octonion 결합자 [a,b,c] = (ab)c − a(bc)의 분포로 알려진 값과 일치 (Fano plane 기반 7개 associative triple class 외 모두 비결합).

→ **ZSqrt[-2] L5 ≅ M_16** 확정.

### 정량 패턴 재확인

```
Layer:    L2      L3      L4      L5      L6
─────────────────────────────────────────────────
ZSqrt[-2]: Z_2 →  Z_4 →   Q_8 →  M_16 →  ?  (sedenion 유사 예상)
ZI:        Z_4 →  Q_8 →  M_16 →  ? →     ?  (이미 sedenion = ZI L5)
ZOmega:    Z_6 → Q_12 →  M_24 →  ? →     ?  (이미 past-Moufang)
```

ZSqrt[-2] L_n unit group ≅ ZI L_{n-1} unit group. **한 layer shift 가설 데이터로 확인**.

### 다음 탐사 후보

1. **L6 ZSqrt[-2]** (32 유닛 예상): "shifted ladder의 sedenion 위치" — alternativity 잃을 것으로 예상. Norm-mult 깨지는지, zero divisor 출현하는지.
2. **L5 ZI = Sedenion** (32 유닛): 이미 알려진 결과 (zero divisor 존재) 정량 재확인.
3. **L5 ZOmega** (48 유닛 예상): ZI sedenion과 quotient 구조 비교.

기계적 데이터 수집 계속.
