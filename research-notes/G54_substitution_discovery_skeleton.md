# G54: Substitution-Discovery Algorithm — skeleton + algebra tower 적용

## 1. Skeleton (개념)

수학 발견 = 무한 → 유한 substitution 의 *재귀* 적용.

핵심 components:

| Component | 역할 | 우리 구현 status |
|---|---|---|
| Sample(level) | finite enumeration at level k | Rust probe (✓ auto) |
| DescLang(level) | level k 의 description 후보 | manual ✗ |
| find_pattern | candidate 중 fit 검색 | findStructure ✓ |
| convergence_detector | data 안정성 판단 | manual ✗ |
| level_escalate | level k 패턴 → level k+1 데이터 | manual ✗ |

→ 4개 중 1개만 algorithmic. **Automation gap = level k 자동 escalation**.

## 2. 우리 algebra tower 의 level 진척

### Level 0 — base × layer enumerate
- Status: ✓ (Rust probe 완전 자동)
- Output: per-layer measurements (unit count, Mou fail, order dist, ...)

### Level 1 — pattern in level-0 data (per Type)
- ✓ Diff ratio → 1/2 (모든 Type)
- ✓ Asymptote 존재
- ✓ Order-4 monopoly + cyclotomic 보존
- Status: empirical 발견 + 일부 ∅-axiom Lean pin

### Level 2 — pattern across Types (CURRENT BOTTLENECK)
- Data: 4 type 의 (asymptote, base structure) 쌍
- DescLang_2: ✗ 빈약 — candidate function form 자동 enumeration 없음
- 시도된 manual candidates:
  - (size − 2)/size: A 만 fit (0.5 ✓), C/D 빗나감
  - rational fitting on 3 points: 자유도 너무 큼
- Status: **gap**

### Level 3+ — pattern in level-2 patterns
- 미접근

## 3. 코끼리 vs 다리

다리 (잡았음):

| 다리 | 발견 | 본질 |
|---|---|---|
| 4-row matrix | Dirichlet 한계 | base 양자화 |
| Order-4 monopoly | i² = -1 메커니즘 | CD 직교성 |
| Diff ratio → 1/2 | dyadic structure | binary slash |
| Asymptote per Type | 0.5, ~0.69, ~0.81 | base 결정 |
| Cyclotomic 보존 | base freezing | 비-축 보존 |

본체 (아직):

| 본체 | 질문 |
|---|---|
| **f(base) = asymptote** | 어떤 base invariant 가 결정? |
| **Universal mechanism** | 4 다리 모두 한 원리에서? |
| **Raw → algebra projection** | 어떤 정확 함수? |

→ 셋이 *동일 unified mechanism* 일 가능성 큼. 발견하면 4 다리 동시에 closed form.

## 4. 즉시 가능한 다음 step — Level 2 자동 검색

DescLang_2 candidate function enumerator 를 작성하고 4 type 의 asymptote
값에 fitness check 하는 driver 만들기:

```
data_points = [(A, 0.5000),  (B, 0.5000),
               (C, 0.6892),  (D, 0.8093)]   -- L9 + 1×diff 추정값

candidate_features per base:
  - unit count            (4, 2, 6, 24)
  - cyclotomic order      (4, 2, 6, 12)    -- 2T 에 12 가능
  - non-abelian fraction  (0, 0, 0, 0.292) -- 2T 만 non-abelian
  - generator count       (1, 1, 1, 4)     -- approximate
  - center size           (2, 2, 2, 2)     -- 모두 동일
  - ...

candidate functions:
  - linear: a + b·feature_i
  - rational: (a + b·f_i) / (c + d·f_i)
  - (size − k) / size for various k
  - 1 - (k/size)^p
  - ...
```

각 candidate 에 4-point fit 시도. 잘 맞는 것 = level 2 substitution 후보.

## 5. Code 인프라 제안

```
lean/E213/Lib/Math/Discovery/
  Skeleton.lean         -- 개념 type signatures
  
rust-engine/crates/app/src/bin/
  level2_search.rs      -- candidate function enumerator + fitness
```

Rust 가 numerical search 에 적합. Lean 은 발견된 substitution 을
∅-axiom decide 로 pin.

## 6. Open

- Level 2 description language 의 *자동 enumerate*: 어떤 expressions 까지 시도?
- Convergence detector: 더 많은 데이터 (L11+, ZOmega L10+) 가 substitution 을
  뒷받침해야 — 현재 4 점 만 → 자유도 제어 어려움
- 코끼리 본체 후보: Raw 의 three commitment 하나로 환원되는 단일 mechanism 식별

**다음 push**: Rust binary `level2_search.rs` 작성, candidate function
generator + fitness. 결과 도출되면 Lean ∅-axiom decide 로 confirm.

## 7. Step A 첫 실행 결과 (2026-05-09)

`level2_search.rs` 가 17 candidate function 중 데이터에 가장 잘 맞는 것 검색.

**Best fit**: `1 − φ(u)/u` (Euler totient)
```
A (u=4):  0.5000 ✓ exact (φ(4) = 2)
B (u=2):  0.5000 ✓ exact (φ(2) = 1)
C (u=6):  0.6667 vs 0.6892 (off +2.2%)
D (u=24): 0.6667 vs 0.8093 (off +14%)
```

**해석**:
- Type A, B (cyclic Z_4, Z_2) 정확히 일치
- Type C (cyclic Z_6) 근사
- Type D (2T 비-순환) 빗나감

→ φ 공식은 *cyclic 단위군 base* 의 substitution. Non-cyclic 에는
다른 invariant 필요.

**다음 step**: Type D 용 추가 candidate 들 (group-theoretic invariants:
maximal cyclic subgroup size, x² ∈ {1, -1} elements 개수, commutator
subgroup, 등)을 enumerator 에 추가하고 다시 search.

또한 ZOmega L10+ 측정으로 Type C 의 정확한 asymptote 결정 (φ 공식 정확히
맞는지 vs 약간 다른 값인지) 확정 필요.
