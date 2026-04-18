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
E213/Hypervisor/Equiv.lean             — ≡ 동치관계 + slash congruence.
E213/Hypervisor/Numbers.lean           — depth/leaves/nodes 정의 + 관계.
E213/Hypervisor/Enumeration.lean       — 번호는 라벨, 구조가 본질.
E213/Hypervisor/NumberComparison.lean  — 세 수의 성질 비교.
E213/Hypervisor/Fold.lean              — 수의 일반 규칙 = catamorphism.
E213/Hypervisor/FoldInjective.lean     — comm h → 단사 불가 (정보 손실).
E213/Hypervisor/Lens.lean              — 렌즈 구조체 + 합성 (카탈로그).
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
