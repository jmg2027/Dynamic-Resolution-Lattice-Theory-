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

## 8. Step A v2 — non-cyclic invariants 추가 (2026-05-09)

candidate 19개 (commutator, abelianization, conj_classes 추가) 실행.

**Best**: `1 - phi(abel)/u` err 0.107 (φ formula 보다 약간 좋음)
**Second**: `1 - phi(u)/u` err 0.143

| Candidate | A | B | C (obs 0.689) | D (obs 0.809) |
|---|---|---|---|---|
| 1 - φ(u)/u | 0.500 ✓ | 0.500 ✓ | 0.667 (-0.022) | 0.667 (-0.143) |
| 1 - φ(abel)/u | 0.500 ✓ | 0.500 ✓ | 0.667 (-0.022) | 0.917 (+0.107) |

→ A, B 둘 다 perfect. C, D 어느 후보로도 deviation 잡히지 않음.

### 핵심 통찰: ratio → 0.5 패턴이 φ 정확성 *반증*

만약 Type C asymptote = 2/3 (φ 공식), residual ratio:
```
L6: 0.555, L7: 0.491, L8: 0.426, L9: 0.288
```
→ 0.5 으로 안 수렴, 점점 감소. universal pattern 깨짐.

만약 asymptote = 0.689 (measured 추정):
```
L6: 0.577, L7: 0.535, L8: 0.510, L9: 0.500
```
→ 0.5 으로 깔끔 수렴.

→ **Type C 의 진짜 asymptote 는 φ 공식과 안 맞음**. measurement 추정 0.689 가 정확.

### 추측: φ + correction

```
asymptote = 1 - φ(u)/u + δ(base extra structure)

δ(Z_2) = 0
δ(Z_4) = 0
δ(Z_6) = 0.022   (multiple prime factors? 2 × 3)
δ(2T)  = 0.143   (non-abelian + multiple primes)
```

correction δ 가 *base 의 prime-factor 다양성* 또는 *non-abelian 정도* 에
linear / functional dependent. 정확 form 은 더 많은 데이터 (다른 cyclic Z_n
base, 다른 quaternion order base) 필요.

### 다음

1. Lean ∅-axiom: `phi(4)/4 = 1/2`, `phi(6)/6 = 1/3`, `phi(24)/24 = 1/3`
   (cyclic part 의 number-theoretic identity, decidable)
2. ZOmega L10 measurement (probe 더 최적화 후) — Type C asymptote 정밀화
3. Type E candidate 실험: Z_8, Z_12 같은 cyclic group base 의 *가상* asymptote
   계산 (실제 base 는 없지만, 만약 있다면 φ 공식 어떻게 deviate?)

## 9. Step A v3 — GOLDEN RATIO 발견 (2026-05-09)

candidate `rank-based 1/φ_gold` 가 **err 0.0018** 으로 압도적 best fit!

```
Candidate                    err     comments
─────────────────────────  ──────   ─────────────────────────
rank-based 1/φ_gold          0.0018  ← 측정 noise 수준
rank-based 8/13              0.0031
rank-based 5/8               0.0046
rank-based 11/18             0.0052
1 - phi(u)/u                 0.1426  (이전 best)
```

**Closed-form 후보**:
```
asymptote(base) = 1 - 0.5 × (1/φ_golden)^rank(base)

rank:
  0   cyclic prime-power     (Z_2, Z_4)              → A, B
  1   cyclic multi-prime     (Z_6 = 2·3)             → C  
  2   non-abelian            (2T, |G| = 24 = 2³·3)   → D
```

예측:
- A (rank 0):  1 - 0.5 = 0.5000  vs measured 0.5000  ✓ exact
- B (rank 0):  1 - 0.5 = 0.5000  vs measured 0.5000  ✓ exact
- C (rank 1):  1 - 0.5/φ = 0.6910  vs 0.6892  (Δ -0.0018)
- D (rank 2):  1 - 0.5/φ² = 0.8090  vs 0.8093  (Δ +0.0003)

→ Type D 만 **3‱ 오차**, 측정 추정 노이즈 안에 들어감.

### 213 native 의미 — Raw 의 5-atomicity ↔ golden ratio

```
Raw (5-atomicity, NS=3 + NT=2)
   ↓
Pentagon angular symmetry (5-fold rotation: θ = 2π/5)
   ↓
Golden ratio: φ = 2·cos(π/5)
   ↓
Algebra tower asymptote: 1 - 0.5/φ^rank
```

→ **algebra tower 의 Moufang fail rate asymptote 가 Raw 의 5-atomicity 에
   직접 의존**. CD doubling 이 binary 인데도 점근선이 *5-fold symmetry*
   (golden ratio) 의 흔적을 들고 옴.

### Caveat — overfitting 위험

4 data points × 2-parameter formula = 진짜 underdetermined. 검증 필요:
1. Rank 0/1/2 분류가 외부 (예: # primes in |G|, abelian/non-ab) 와 정확
   대응하는지 더 많은 base 테스트 — 하지만 framework 안 base 4개 한계.
2. 이론적 도출: pentagon → φ → asymptote 의 *mechanical* derivation
   (단순 numerical coincidence 아님 증명).
3. 213 의 *다른 영역* 에서 같은 1/φ rank-formula 등장하는지 cross-validate
   (e.g. K_{3,2}^(c=2) Betti, fractal level cardinality, ...).

### Reframing — Step A 의 의미

Numerical fitting 으로 closed-form 후보 잡는 것이 *algorithmic discovery*.
천재 직관 아닌 enumerate + fitness check. Now this candidate must be:
- 측정 데이터 더 정밀 (higher layers) 으로 validate, OR
- 이론적 derivation 으로 confirm

이게 substitution-discovery algorithm 의 *Step B* (verification) 단계.
