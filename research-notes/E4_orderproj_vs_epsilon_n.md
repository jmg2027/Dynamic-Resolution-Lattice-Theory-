# E4 — orderProj-Cauchy vs ε-N Cauchy 의 deep tension

## 발 견 (2026-04-26)

E3 의 해결 방향 (B) — StrongModulus typeclass — 의 *근 본 적*
limitation 발 견.

## 두 Cauchy form

### orderProj-Cauchy (기존 HasModulus)

```
∀ m k, k ≥ 1, ∃ N, ∀ i, j ≥ N,
  orderProj m k (view xs i) = orderProj m k (view xs j)
```

= "모든 rational m/k cut 에 서 view 가 eventually 같은 side".

### ε-N Cauchy (StrongModulus)

```
∀ k ≥ 1, ∃ N, ∀ i, j ≥ N, |view i / view j ratio difference| ≤ 1/k
```

= "ratio 가 eventually within 1/k 거 리".

## 두 form 의 *non-equivalence*

**orderProj-Cauchy ⇎ ε-N Cauchy**.

Counterexample: ratio 가 p/q 에 양 쪽 으 로 진동 하 며 수렴.
Even n: ratio = p/q - 1/n.  Odd n: ratio = p/q + 1/n.
- ε-N Cauchy: |ratio_i - ratio_j| → 0.  ✓
- orderProj at (p, q): even true, odd false.  Never stable.  ✗

ε-N Cauchy 이 지 만 NOT orderProj-Cauchy.

## 의의

두 Cauchy form 이 *다 른 mathematical objects* 를 정의:

- orderProj-Cauchy: 213 의 native — Dedekind cut 형 limit.
- ε-N Cauchy: Bishop standard — value-convergence 형 limit.

이 둘 의 기 본 differ on **rational limit points**.

ZFC ℝ 안 에 서 는 둘 이 equivalent (둘 다 같은 ℝ 의 element 정의)
because rationals 는 measure-zero "irrelevant" — set-theoretic 평탄
화.  213 안 에 서 는 두 form 이 *다 른 objects* 를 정의.

## Phase B (arithmetic) 에 의 함의

- orderProj-Cauchy 위 의 addition: rational point 에 서 ill-defined
  (위 counterexample).  → 진 짜 obstruction.
- ε-N Cauchy 위 의 addition: standard Bishop, working.  하 지 만
  213 의 *native* form 이 아 님.

## 가능 한 해결

### (i) Rational point 회 피

Real213 의 정의 자체 에 서 rational limit point 배 제.  e.g.,
"sequence 가 (m, k) 에 서 *strict 로* 수렴 — eventually ratio < m/k
또 는 eventually ratio > m/k 또 는 eventually ratio = m/k 의
*trichotomy*".

### (ii) 두 form 의 union

Real213 = (xs, hasModulus, strongModulus).  Both required.
Rational point 의 ambiguity 제거.

### (iii) 다 른 cut form

orderProj 를 *strict* form ("< m/k" 또 는 "> m/k") 으 로 split.  Both
sides 따 로 Cauchy.  Complex but more refined.

## 결정

이 obstruction 이 *framework boundary* 의 신호 인 가, *engineering
challenge* 인 가?

**Engineering challenge** 으 로 보이지 만, *deep 한* engineering — 두
Cauchy form 의 tension 의 design 결정 요구.  Bishop 의 program 자체
는 ε-N 으 로 진 행 — 213 안 에 서 도 ε-N 채택 시 standard 흐름.

하 지 만 213 의 *native* preference 인 orderProj-Cauchy 가 rational
point 에 서 break 하 는 것 자체 가 framework 의 *primitive* 가
무엇인 가 의 question.

## 결론 (잠 정)

Phase B (arithmetic) 의 *진 짜* progress 는 이 design 결정 후 가능.
이 session 까 지 의 progress: kernel 까 지 정리, deep obstruction 진단.

다 음 session: design 결정 — orderProj vs ε-N vs union vs strict.

## Cross-references

- `notes/E2_phase_b_obstruction.md` (Raw realization).
- `notes/E3_modulus_kernel_deep_obstruction.md` (single-precision
  query 부족).
- `framework/E213/Research/Real213ModulusCombiner.lean` (kernel).
- `framework/E213/Research/StrongModulus.lean` (ε-N form 시도).
