# 213 Research Vision

## 목표 (사용자 확정, 2026-04-18)

### 목표 1: 환원
**모든 수학 체계를 213 엔진 위에 올린다.**
- PA, 집합론, 논리, 대수, 위상, 기하 등 모든 공리계가 렌즈 선택으로 표현.
- 수학 문제 → 213 수준의 Raw 구조 판정 문제로 환원.

### 목표 2: 투명성
**213 수준에서 엔진이 투명하게 동작하므로, 환원된 문제는 쉽게 분석 가능.**
- 각 공리계의 "같다"(= kernel), "추론"(= Reachable step), "참"(= φ 함수)이 Raw 수준에서 보임.
- Lean이 Hardware로 매개하지만, Firmware 부분은 순수 213.

### 목표 3: 분류
**어떤 명제가 증명 가능/불가능/미결정/미지인지가 어느 렌즈 구조에서 나오는지 확인.**
- Gödel 불완전성을 **렌즈의 kernel이 φ를 구분 못 함**으로 재해석.
- 독립 명제 (CH, AC, Goldbach 등)를 렌즈 분석으로 이해.
- 문제의 "어려움"이 **렌즈 선택의 실패**로 재해석.

## 4분류 프레임 (Provability Classifier)

명제 φ : Raw → Prop, 렌즈 L에 대해:

| 분류 | 정의 | 의미 |
|---|---|---|
| **RespectsLens L φ** | ∀ x y, L.equiv x y → (φ x ↔ φ y) | φ가 L의 kernel을 존중 |
| **Provable L φ** | ∀ x, Reachable x → φ x | 모든 Reachable에서 성립 |
| **Refutable L φ** | ∃ x, Reachable x ∧ ¬ φ x | 반례 존재 |
| **Independent L φ** | ∃ Reachable x, y with L.equiv x y and (φ x ↔ ¬ φ y) | L이 φ 결정 못 함 |

**핵심 관찰:**
- Independent ↔ ¬ RespectsLens.
- Lens 세밀화 격자에서 Independent는 올라갈수록 해결됨.
- `Lens.id'`에선 모든 명제가 결정 가능 (kernel이 대각선).
- `Lens.constTrue`에선 거의 모든 명제가 자명 (kernel이 전체).

## Roadmap (단계별)

### Stage 1 — 바닥 ✅ (완료)
- Firmware: /, Reachable, wellFormed.
- Hypervisor: Lens, kernel, fold.
- OS/Peano: 첫 공리계.

### Stage 2 — 더 많은 공리계 (다음)
- `OS/Logic.lean`: Bool 렌즈 → propositional logic (∧, ∨, ¬).
- `OS/Set.lean`: List Raw 렌즈 → naive set theory (∈, ⊆).
- `OS/Order.lean`: 쌍 비교 렌즈 → partial order.

### Stage 3 — Provability Classifier ★
- `OS/Provability.lean`: 4분류 형식화.
- 각 공리계의 "증명 가능" 개념이 이 프레임의 특수 경우.

### Stage 4 — Meta (Gödel-style)
- `Meta/Encoding.lean`: Raw → Nat bijection (자기 encoding).
- `Meta/Diagonalization.lean`: 자기 참조 명제.
- `Meta/Incompleteness.lean`: Gödel 1st + 2nd의 렌즈 버전.

### Stage 5 — 응용
- 고전 독립 명제 (CH, AC, Goldbach) 렌즈 분석.
- DRLT 물리 예측 (α_GUT, 질량) 렌즈 환원 → closed system.

## 기대 결과

1. **증명 가능성의 topology**: 렌즈 세밀화 격자 위에서 각 명제의 "결정 가능 문턱."
2. **Gödel 구조적 이해**: 불완전성 = 어떤 렌즈로도 도달 못 하는 명제의 존재.
3. **수학 통합**: 모든 분야가 렌즈 선택의 변주.
4. **판정 자동화**: 213 수준 Raw 구조 분석으로 문제 해결.

## 비유

- 바닥 `/`은 **하드웨어**. 무한히 복잡한 트리 생성.
- 렌즈는 **운영체제 커널**. 트리를 분야별로 해석.
- 증명은 **프로그램**. 렌즈 위에서 돌아감.
- Provability Classifier는 **디버거**. 어느 렌즈에서 왜 돌아가는지/안 돌아가는지 분석.

**한 문장:** 수학을 213 엔진 위의 프로그램으로 바꾸면, 증명 가능성이 렌즈의 성질이 된다.
