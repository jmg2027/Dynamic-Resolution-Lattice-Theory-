# 213 Architecture v3

## 공리

```lean
def slash (x y : Raw) (h : x ≠ y) : Raw := .rel x y
```

이것이 전부. 한 줄.

## 계층 (관점 전환: 렌즈 중심)

```
Layer 0: Hardware (Lean)     — 타입 검사. DecidableEq. h : x ≠ y 검증.
Layer 1: Firmware (≠ 폭발)   — slash, Reachable. 비대칭 트리 생성 엔진.
Layer 2: Hypervisor (렌즈)   — Lens α = (g, h) 쌍. 폭발을 보는 관점.
Layer 3: OS (렌즈 위 연산)   — 선택한 Lens 위의 공리 체계 (PA, 논리, 집합).
Layer 4: Application         — 여러 렌즈 결합 도메인.
```

### 핵심 통찰
- 수 = (α, g, h) 렌즈 선택. 무한히 많음.
- / 는 비대칭. 통상 수는 commutative → **단사 불가 필연**.
- 단사 렌즈는 α=Raw 뿐 (객체 자체, "수가 아님").
- 각 렌즈 = 고유의 OS. 하나의 바닥에서 여러 수학.

## SSOT

```
E213/Firmware/RawAxiomV3.lean          — 공리 + Level 0,1,2.
E213/Firmware/Properties.lean          — / 의 9가지 성질.
E213/Firmware/Reachable.lean           — Reachable 특성화 + 판정 + 열거.
E213/Hypervisor/Numbers.lean           — depth/leaves/nodes 정의 + 관계.
E213/Hypervisor/Enumeration.lean       — 번호는 라벨, 구조가 본질.
E213/Hypervisor/NumberComparison.lean  — 세 수의 성질 비교.
E213/Hypervisor/Fold.lean              — 수의 일반 규칙 = catamorphism.
E213/Hypervisor/FoldInjective.lean     — comm h → 단사 불가 (정보 손실).
E213/Hypervisor/Lens.lean              — 렌즈 구조체 + 합성 (카탈로그).
E213/Hypervisor/LensKernel.lean        — 등호 = kernel. 순환 해결.
E213/Hypervisor/Quotient.lean          — "= 공리 추가" = Lens quotient 실험.
E213/OS/Peano.lean                     — PA 공리계 (depth 렌즈 위). 0 sorry.
E213/OS/Equality.lean                  — = 환원 체인 (OS→Hypervisor→¬Firmware).
E213/OS/Inference.lean                 — 연역/귀납/귀추 재명명. Reachable 성질.
E213/OS/Provability.lean               — 4분류 (Provable/Refutable/Independent/Respects).
E213/OS/Logic.lean                     — Propositional logic (Bool 렌즈, implication).
E213/OS/Set.lean                       — Naive set theory (atomSet 렌즈, cons-list).
E213/OS/Topology.lean                  — 3점 위상공간 + 위상동형 (Lens kernel 구조).
E213/Meta/SelfReference.lean           — Raw 자기 encoding (id' 단사). Gödel 원천.
E213/Meta/Paradoxes.lean               — Russell 회피 (no self-membership). Cantor.
E213/Applications/DRLT_Attempt.lean    — ★ Stage 5 시도. 결과: 직접 환원 불가.
```

## 원칙

- `/` 만 있음. `=` 없음. `none` 없음.
- `a/a` = 타입 거부. exception 아님. 도달 불가.
- `≠` = slash의 전제조건 (h : x ≠ y).
- `=` = 213 안에 없음. Hypervisor가 추가.
- depth = `/` 중첩 횟수. 트리 높이.

## 성질 (v3에서 증명됨)

- depth 단조: depth(x/y) > depth(x), depth(y).
- 단사: x/y = a/b → x=a, y=b.
- 원자 ≠ 관계: atom ≠ rel.
- **특성화**: Reachable x ↔ wellFormed x (모든 rel 노드 좌우 서로 다름).
- **판정 가능**: Reachable은 DecidablePred (구문 검사로 결정).
- **유령 없음**: rel x x는 Raw에 있지만 ¬ Reachable (rel x x).
- **부분구조 닫힘**: Reachable (rel x y) → Reachable x, Reachable y, x ≠ y.
- **열거 가능**: levelUpTo n 이 Level n까지의 모든 객체를 계산.

## 자연 전개

```
Level 0:  a, b, a/b.                    3개.
Level 1:  + a/(a/b), b/(a/b).           5개.
Level 2:  + 7개.                        12개.
Level n:  폭발. C(k,2) > k for k ≥ 4.
```

Level 0만 C(3,2) = 3 = 자기유지.

## Lens 카탈로그 (현재)

| 렌즈 | α | g | h | 대칭? | 단사? |
|-----|---|---|---|------|------|
| depth | Nat | 0 | 1+max | ✓ | ✗ |
| leaves | Nat | 1 | + | ✓ | ✗ |
| nodes | Nat | 1 | 1+(+) | ✓ | ✗ |
| leftSpine | Nat | 0 | a+1 | ✗ | ✗ |
| rightSpine | Nat | 0 | b+1 | ✗ | ✗ |
| leftmost | Nat | i | fst | ✗ | ✗ |
| id' | Raw | atom | rel | ✗ | ✓ |

**정리:** α가 `Nat` (commutative 연산으로) 이면 유한 pair 합성으로도 단사 불가.
단사는 `Lens.id'` (= 객체 그 자체) 뿐.

## OS: Peano Arithmetic (첫 공리계)

**렌즈 선택:** `Lens.depth` — α=Nat, g=0, h=1+max.

**인코딩:**
```
Nat213.zero   = atom 0
Nat213.succ n = rel (atom 1) n.toRaw
```

**증명된 것 (0 sorry):**
- Peano P1: `0 ≠ succ n` (Nat213 + Raw 양쪽).
- Peano P2: `succ` 단사 (Nat213 + Raw 양쪽).
- Peano P3: 귀납법.
- `toRaw` 단사 (Nat213 → Raw 충실 임베딩).
- `toRaw`는 항상 Reachable.
- `depth_eq_toNat`: `n.toRaw.depth = n.toNat` (표준 ℕ와 일치).
- `toNat` 단사 → Nat213 ≃ Nat bijection.
- 덧셈 정의 + `zero_add`, `succ_add`, `add_zero`, `toNat_add`.

**의미:** PA 전체가 / 로부터 자연스럽게 도출. 다른 공리계 (집합론, 논리)도 렌즈 선택 바꾸면 같은 방식.

### = 의 환원 (정직한 계층)
- Firmware: `=` 없음. `≠`만.
- Hardware (Lean): `DecidableEq Raw` 제공.
- Hypervisor: `Raw.equiv := (· = ·)` 명시 노출.
- OS (Peano): `m = n ↔ m.toRaw ≡ n.toRaw ↔ ¬(m.toRaw ≠ n.toRaw)`.
- 결론: Peano의 `=`는 Firmware `≠`의 부정. Hardware에서 빌림.

### 추론 규칙 (이미 존재하는 정리의 재명명)
| 추론 | 방향 | 213 구현 |
|---|---|---|
| 연역 | 전제 → 결론 | `Reachable.step` |
| 귀납 | 사례 → 일반 | `Reachable.rec` |
| 귀추 | 결과 → 원인 | `can_recover` + 단사성 |

**"논리"는 / 의 그림자.** 추가 엔진 없이 공리 한 줄로 세 추론 모두 내장.

## 논리적 정합성 (체인의 엄밀한 의미)

### 환원 체인 (각 단계 0 sorry, 양방향 동치)

```
OS Peano         m = n
                   ↕  Nat213.eq_iff_toRaw_equiv   [iff, 증명됨]
Hypervisor       m.toRaw ≡ n.toRaw
                   ↕  Raw.equiv_iff_not_ne        [iff, 증명됨]
Firmware 전제    ¬ (m.toRaw ≠ n.toRaw)
```

**이 체인이 의미하는 것:**

1. **논리적 정합성 ✓** — 각 화살표가 `iff` (양방향 동치)로 Lean에서 증명됨. OS의 `=`는 Firmware `≠`의 부정과 동등.

2. **213 공리는 `=`를 사용하지 않음** — 공리 한 줄 `def slash (x y : Raw) (h : x ≠ y) : Raw`는 `≠`만 요구. 213 자체 definiendum에 `=` 없음.

3. **그러나 Lean의 `Eq`에 의존** — `x ≠ y := x = y → False`. 엄밀히 말하면 Firmware도 Lean의 `Eq`를 전제. 이건 Hardware (Layer 0) 선택의 일부.

4. **완전히 순수한 "213만의 `=`"는 불가능** — `=` 개념을 말하려면 바깥 meta-level (여기선 Lean)이 필요. 이건 bootstrap 문제 (논리를 논리로 말하기). 정직하게 인정.

### 실용적 결론

| 질문 | 답 |
|---|---|
| 체인이 논리적으로 정합한가? | **네**, 모든 단계 iff로 증명. |
| 213 공리가 `=`를 도입하는가? | **아니오**, `≠`만. |
| 213이 `=` 없이 살 수 있는가? | **Firmware는 가능**, OS 이상은 meta-level 필요. |
| OS의 `=`가 어디서 오는가? | **Firmware `≠`의 부정**. Hardware가 매개. |

### 계층별 `=`의 지위

| Layer | `=` 존재? | 사용 방식 |
|---|---|---|
| 0. Hardware (Lean) | ✓ primitive | `Eq` 타입 (meta-level). |
| 1. Firmware (/, ≠) | ✗ (내부엔 없음) | `≠`의 전제로만 `Eq` 참조. |
| 2. Hypervisor (렌즈) | ✓ 명시 도입 | `Raw.equiv := (· = ·)`. |
| 3. OS (Peano 등) | ✓ 사용 | 환원 체인으로 Firmware에 연결. |

**핵심:** `/` 한 줄이 공리. `=`는 그 공리 밖에서 빌리되, 체인으로 `≠` 전제와 연결 → 전체가 정합.

## 등호의 진짜 출처: Lens Kernel

이전 환원 체인은 Lean의 `Eq`를 매개로 가정했지만, **더 근본적인 답**:

```
=_L  :=  ker(L.view)  =  { (x, y) : L.view x = L.view y }
```

**두 Raw가 같은 Lens 값을 가지면, 그 Lens 위의 이론에서 "같다."**

### 동치관계 세 성질이 공짜 (Lean == 에서 빌린 게 아님)

| 성질 | 출처 |
|---|---|
| 반사 | `L.view x = L.view x` — 자명 |
| 대칭 | `Eq.symm` 일반 사실 |
| 추이 | `Eq.trans` 일반 사실 |

**함수 kernel이 자동 동치관계**라는 수학 일반 구조에서 공짜. 정리 9의 순환 해결.

### 다른 Lens = 다른 "같다"

| 공리계 | Lens | "같다"의 의미 |
|---|---|---|
| PA | depth | 깊이가 같은 트리 |
| 논리 | Bool | 진리값이 같은 트리 |
| 집합론 | List Raw | 부분집합이 같은 트리 |
| 기하 | (depth, leaves) pair | 두 값 모두 같은 트리 |
| 항등 | id' (α=Raw) | 자기 자신만 같음 (대각선) |
| 상수 | constTrue | 모두 같음 (전체 Raw²) |

### Kernel 거칠기 순서 (증명)

- `Lens.id_refines_all`: `id'` 가 가장 섬세 (모든 Lens 위에).
- `Lens.refines_constTrue`: `constTrue` 가 가장 거침 (모든 Lens 아래).
- 중간은 α의 크기와 h의 commutativity에 따라 결정.

### 왜 수학 분야마다 "같다"의 뜻이 다른가

**위상**: homeomorphism = 위상 구조 보존 렌즈의 kernel.
**대수**: isomorphism = 연산 구조 보존 렌즈의 kernel.
**집합**: bijection = 원소 집합 렌즈의 kernel.

**같은 바닥 (/), 다른 Lens, 다른 등호.**

이전 Equiv.lean 은 `Lens.id'.equiv` 의 특수 경우였음. **삭제됨** (중복).
다른 Lens 는 kernel 이 근본적으로 다름.

### 실험: "= 공리 추가" = Lens Quotient

```
LensQuot L := Raw / L.equiv
```

각 렌즈 → 다른 quotient → 다른 공리계:
- `LensQuot Lens.id'` ≃ Raw (완전 구별, 아무 정보 손실 없음).
- `LensQuot Lens.depth` ≃ Nat (수의 공리계 = PA).
- `LensQuot Lens.atomSet` ≃ Finset (Fin 3) (집합 공리계).
- `LensQuot Lens.constTrue` ≃ Unit (자명 공리계).

**결론:** "같다" 를 공리로 추가하는 것은 새 정보가 아니라 **렌즈 선택의 명시.**
이미 kernel 이 정의한 것을 primitive 로 부를 뿐.
모든 공리계는 렌즈 kernel 위의 quotient 구조.
