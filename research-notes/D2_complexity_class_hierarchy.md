# D2 — Lens-algorithm complexity class 의 3-tier hierarchy

## Statement (interpretive synthesis, 2026-04-26)

213 framework 의 *수* 는 ZFC 의 ℝ 처럼 "한 바구니 의 점" 이
아 니 라, **Lens-algorithm complexity class** 로 분류 됨.  세 tier:

### Tier 1 — FSM (Finite State Machine)

**대상**: 유리수 ℚ, 대수적 무리수 (√2, √3, √5 등).

**특징**: 유한 algebraic invariant (modular periodicity, Pell
equation) 안 닫힘.  Lens 가 *one observation* 으 로 future cuts
모두 결정.

**Framework 내 modules** (모두 ≤ propext, 대 부 분 zero axioms):

| Module | 결과 |
|--------|------|
| `Sqrt2IrrationalPure` | √2 irrational, 2-adic descent, zero axioms |
| `Sqrt3IrrationalPure` + `PureNatMod3` | √3, 3-adic, zero axioms |
| `Sqrt5IrrationalPure` + `PureNatMod5` | √5, 5-adic, zero axioms |
| `PellHasModulus` + `PellSeq` | Pell sequence, mod-N closure |
| `LeavesModNat` + `ModLensCRT` | 모듈러 Lens family, CRT |
| `PrimeDescentObservations` | sqrt4 rational (boundary) |

Closure pattern: `m mod p` 의 finite state (= residue) 가 *전체*
sequence 의 future 를 결정.  Cut 결정 = 단일 modular evaluation.

### Tier 2 — ICT (Infinite Combinatorial Trajectory)

**대상**: 초월수 (e, π/2 등 의 algorithmic transcendentals).

**특징**: 유한 modular state 부재.  Trajectory complexity 가
factorial / cumulative product 로 *unbounded* 로 grow.  각
individual cut 은 finite-step 결정 가능 (HasModulus) 이지만,
*cut 의 N* 이 target precision 과 함께 무한 증가.

**Framework 내 modules**:

| Module | 결과 |
|--------|------|
| `EulerCombinatorialPure` | e ∈ (2, 3), zero axioms |
| `EulerSharperPure` | e > 8/3, e ≠ a/3 (partial), ≤ propext |
| `EulerGenericPure` | meta-algorithm: e ≠ a/b for arbitrary b |
| `WallisSharper` | π/2 > 64/45, similar pattern |
| `HasModulus` typeclass | constructive Cauchy modulus |

Closure pattern: `euler_lower_step` 의 induction 이 b 와 함께
N 이 grow — *trajectory* 가 *fully unfolded* 일 필요.  No finite
state machine.

### Tier 3 — Power-set dependent (framework 외부)

**대상**: ZFC ℝ 의 *non-computable* reals (Specker sequences,
random reals, Dedekind cuts of non-r.e. predicates).

**특징**: Cut 자체 의 finite-step decidability 부재.  Cut 결정
= *power-set reify* (𝒫(ℚ) 의 임의 subset) 요구.

**Framework 의 boundary**:

- `notes/C1_kernel_cardinality_obstruction.md`: Lens-kernel
  cardinality 가 countable evidence strong, Cantor diagonal 이
  slash-closure 보존 부재.
- `notes/D1_zfc_real_as_final_boss.md`: power-set 의존 의
  *constructive substitute* 부재 — framework 의 진짜 final boss.

CLAUDE.md falsifiability: 이 tier 가 framework 안 capture 되 면
framework strengthened, 영구 미 capture 면 framework boundary
confirmed.  공리 추가 시 framework 폐기.

## Tier 간 separation 의 의미

세 tier 의 구분 이 ZFC 의 "ℝ 의 한 점" 으 로 *뭉개진* 진짜
구조 의 복원:

- ZFC: √2 와 e 와 random real 모두 "ℝ 의 element".
- 213: 셋 모두 *다른 complexity class* — algorithm 적 substrate
  에 서 fundamentally different.

이 게 user 의 통찰 ("복잡도 클래스 자체 가 다르다") 의 framework-
internal 정형 화 가능 부분.

## 213-unique contribution (정직 한 평가)

### 새 부분

1. **Substrate 가 Lens** (Turing machine 아 님).  같은 Raw + slash
   axiom 위 에 FSM 도 ICT 도 *동일* abstraction (Lens) 으 로
   capture — substrate-uniform.
2. **0-axiom Lean verification**: Sqrt{2,3,5}IrrationalPure (FSM
   tier) + EulerGenericPure (ICT tier) 모두 framework-internal
   verified.  Substrate 의 *실제* 구현 가능 성 확인.
3. **Power-set 의 명 시 적 falsifiability boundary**: 단순 "non-
   computable" 이 아 닌 *axiom 추가 부재* 의 framework 폐기 조건
   (CLAUDE.md §1.5).

### 기존 echo 부분 (정직 한 prior-art)

- **Computable analysis** (Weihrauch, Type-2 Effectivity): 비슷한
  3-tier — computable / r.e. but non-computable / non-r.e.
- **Bishop constructive analysis**: Cauchy modulus 의 explicit
  요구 (HasModulus 의 prior).
- **Specker sequences** (1949): non-computable reals 의 명시 적
  example.
- **Algebraic vs transcendental** (고전 number theory): Tier 1 vs
  Tier 2 의 일 부 분 — 단, transcendental 안 의 "computable vs
  not" 추가 분리 부재.
- **Chomsky hierarchy** (regular / context-free / recursive): 비슷
  한 상승 complexity class 패턴.

### 정 직 한 결론

3-tier 분류 의 *추 상* 자체 는 새 발견 아 님 — computable analysis
literature 의 well-known structural distinction.  213 의 contribution:

> *"Lens substrate 위 의 0-axiom Lean verification + power-set 의
> explicit falsifiability boundary."*

이 게 *기 존* 분류 의 213-flavored 정형 화.  "발견" 이라기 보다
"*기 존 distinction 의 더 fundamental substrate 위 재구축*".

## Tier 의 Lean-formal separation (시도)

### Tier 1 (FSM) 의 형식 정의 후 보

```
class HasFiniteStateMachine (xs : Nat → Raw) where
  state : Type
  finite : Fintype state
  transition : state → state
  init : state
  cut_decision : state → ℚ → Bool  -- 또 는 적절 한 framework-internal target
  determines : ∀ n m k, ...  -- one-step decision property
```

문제: "framework-internal target" 이 무엇인 가 — Lens kernel 또 는
ABLens orderProj.  Tier 1 의 *closure*  자체 의 형식 statement 가
nontrivial.

### Tier 2 (ICT) 의 형식 정의 후 보

```
HasModulus xs ∧ ¬ HasFiniteStateMachine xs
```

= "Cauchy 이지만 finite state 부재".  Negative 부분 의 형식
statement 가 더 어 려 움 (모든 가능 한 state machine 의 부재).

### Tier 3 의 형식 정의

= framework 내 어떤 module 으 로 도 capture 부재.  Negative
existential — framework 외 부 reference 필 요 (현재 Lean 으 로
직접 형식 화 불가능).

## 다 음 단 계

- (a) `ComplexityClass.lean` Lean module 시도 — Tier 1 의 partial
  formal definition (state machine + transition + cut decision).
- (b) Tier 2 의 negative half (¬ FSM) 의 *명 시 적 example* 형식
  화 — e 의 specific descent 시도 가 모두 fail 한다 는 statement.
- (c) `HasFiniteStateMachine` instance 작성: Pell sequence + 각
  prime descent.  Sqrt2/3/5 의 instance 가 자동 따 라 옴.

## Cross-references

- `notes/B1_pure_descent_method.md`: 5-step descent template (Tier 1).
- `notes/B2_hermite_direction.md`: Hermite formalization (Tier 2).
- `notes/C1_kernel_cardinality_obstruction.md`: power-set obstruction.
- `notes/D1_zfc_real_as_final_boss.md`: Tier 3 의 framework boundary.
- `framework/E213/Research/Sqrt{2,3,5}IrrationalPure.lean`: Tier 1
  modules.
- `framework/E213/Research/EulerGenericPure.lean`: Tier 2 modules.
