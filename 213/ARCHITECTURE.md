# 213 Architecture

## 5-Layer Stack

```
Layer 4: Application    — 응용 (암호학, 물리, 공학)
Layer 3: OS             — 정리/증명/추측 (Goldbach, Fermat, ...)
Layer 2: Hypervisor     — 공리체계/수학이론 (PA, ZFC, 군론, ...)
Layer 1: Firmware        — 213 (gen, mul, relify, chain)
Layer 0: Hardware        — Lean (타입 검사, 예외처리)
```

## Layer 0: Hardware (Lean)

역할: 213 프로그램이 돌아가는 토대. 예외처리.
제공: `inductive`, `theorem`, `def`, `native_decide`.
검증: 타입 검사 통과 여부만 확인. 의미는 모름.

## Layer 1: Firmware (213)

역할: 의미의 명령어 집합. 모든 상위 계층이 이 API만 사용.

### API

| 명령어 | 시그니처 | 의미 |
|--------|---------|------|
| `gen` | `Fin 3 → Obj` | 원소 선택. 존재 선언. |
| `mul` | `Obj → Obj → Obj` | 이항 비교. 관계 생성. |
| `relify` | `(α→α→α) → Triple α → Triple α` | 모든 쌍에 mul 분배. |
| `chain` | `(α→α→α) → Triple α → Nat → Triple α` | relify 반복. |

### 제약 (ISA 규칙)

| 규칙 | 형식 | 의미 |
|------|------|------|
| 자기유지 | `C(3,2) = 3` | Triple만 닫힘. |
| 붕괴 | `C(2,2) = 1 < 2` | Pair 독립 불가. |
| 폭발 | `C(4,2) = 6 > 4` | Quad 과잉. |
| 완전성 | `all_generated` | gen+mul이 전부. |
| 비생성 | `no_third_constructor` | ¬는 생성자 아님. |
| 순서 | `× → + → =` | ×가 가장 근본. |
| 방향 | `C(3,k)>1 ↔ k∈{1,2}` | 2방향만. |

### 불변량

- `pairs 3 = 3` (안정)
- `pairs 2 < 2` (붕괴)
- `pairs 4 > 4` (폭발)
- `chain_add` (체인 합성 = ℕ 덧셈)

## Layer 2: Hypervisor (공리체계)

역할: Firmware API를 수학적 개념으로 해석. 자체 API 제공.

### PA (Peano Arithmetic)

| Firmware API | PA 해석 | PA API |
|-------------|---------|--------|
| `chain level` | ℕ | `0, succ, +, ×` |
| `chain 0` | 0 | |
| `chain (k+1)` | succ k | |
| `chain_add` | m + n | |
| `relify` | 분배법칙 | |

### ZFC (집합론)

| Firmware API | ZFC 해석 | ZFC API |
|-------------|---------|---------|
| `gen` | 원소 | `∈, ⊆, ∪, ∩` |
| `mul` | 소속 판정 | |
| `Triple` | 3-원소 집합 | |

### 군론

| Firmware API | 군 해석 | 군 API |
|-------------|---------|--------|
| `mul` | 군 연산 | `·, e, ⁻¹` |
| `relify` | 분배(환) | |
| depth 2 | 결합법칙 | |

## Layer 3: OS (정리/증명)

역할: Hypervisor API를 사용하여 구체적 결과 도출.

### 비둘기집

- 사용 API: PA(ℕ), 213(C(n,2))
- 진술: Fin 3 → Fin 2 단사 없음.
- 증명: 전수검사 (native_decide).

### 골드바흐

- 사용 API: PA(ℕ, isPrime, +), 213(C(k,2), pair⊂triple)
- 진술: ∀ even n > 2, ∃ p q prime, p+q=n.
- 상태: 유한 검증 완료 (500). 보편 증명 미완.
- ISA 분석: C(2,2)=1 붕괴. E의 삼중 결핍. ¬ 비생성.

## Layer 4: Application (응용)

역할: OS의 정리를 실세계에 적용.

(현재 구현 없음. 향후 확장.)

## API 경계 규칙

1. **각 계층은 바로 아래 API만 호출.** 레이어 건너뛰기 금지.
2. **Firmware → Hypervisor 번역은 명시적.** (e.g., chain → ℕ.)
3. **Hypervisor → OS 번역도 명시적.** (e.g., ℕ + isPrime → goldbach.)
4. **검증은 Hardware가 담당.** 모든 정리가 Lean 타입 검사 통과.
5. **ISA 위반 = 레이어 경계 침범.** 감사 기준.

## 파일 분류

### Firmware (Layer 1)
```
Axiom.lean, Profile.lean, Arithmetic.lean, Chain.lean,
Closure.lean, WhyTwo.lean, Simplex.lean, CayleyDickson.lean,
FiniteSpaces.lean, Negation.lean, PairInTriple.lean, Primality.lean,
Infinities.lean, Meaning.lean, Coordinates.lean
```

### Firmware ↔ Hypervisor 번역
```
Translate.lean, EpsilonDelta.lean, Decompose.lean,
ConstructiveGap.lean, LevelReduction.lean, GoldbachFromObj.lean
```

### Hypervisor (Layer 2)
```
(아직 별도 구현 없음. PA, ZFC를 213 위에 구현하는 파일 필요.)
```

### OS (Layer 3)
```
Pigeonhole.lean, Goldbach/*.lean (14파일)
```

### Meta
```
Architecture.lean, LayerCheck.lean
```
