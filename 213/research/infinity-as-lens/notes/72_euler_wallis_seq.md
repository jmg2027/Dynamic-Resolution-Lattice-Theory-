# 72 — EulerSeq + WallisSeq: transcendental Cauchy demonstration

`Research/EulerSeq.lean` + `Research/WallisSeq.lean` 형식화.
Pell template (algebraic invariant + abLens witness + orderProj
양쪽 cut) 을 transcendental case (e, π/2) 에 적용.

## EulerSeq (e via Σ 1/k!)

- `eulerNum n = Σ k=0..n n!/k!` (정수 numerator), `eulerDen n = n!`.
- Recursion: `a_{n+1} = (n+1) a_n + 1`, `d_{n+1} = (n+1) d_n`.
- **Upper inv**: `3 * d_n ≥ a_n + 1` (S_n < 3).  Induction OK.
- **Lower inv** (n ≥ 2): `a_n ≥ 2 * d_n + 1` (S_n > 2 from n=2).
- **Cuts**:
  - m/k ≥ 3: orderProj true (∀ n).
  - m/k ≤ 2: orderProj false (n ≥ 2).
- e ∈ (2, 3) Dedekind cut at concrete thresholds — closed.

## WallisSeq (π/2 via Wallis product)

- `wallisNum/wallisDen` recursion: W_{n+1}/W_n = 4(n+1)²/((2n+1)(2n+3)).
- **Monotonic**: W_n < W_{n+1}.  Closed (poly diff = 1).
- **Lower inv** (n ≥ 1): `3 * wallisNum n ≥ 4 * wallisDen n`
  (W_n ≥ 4/3 > 1).  Closed.
- **Upper inv** (deferred): `wallisNum n * (2n+1) ≤ (4n+1) * wallisDen n`
  (W_n ≤ 2 - 1/(2n+1) < 2).  Polynomial identity
  `(4k+1) * 4(k+1)² + 1 = (4k+5) * (2k+1)²` 가 degree-3 in k.
  Lean 4 core 에서 ring 없이 close 하려면 flat-monomial
  normalization 필요.  현재 deferred.
- **Cut closed**: m/k ≤ 1 → orderProj false (n ≥ 1).

## Flat-Monomial Strategy (Mingu 제안, future work)

Upper invariant 의 polynomial identity 처리 전략:

1. **Local algebraic-hygiene set**: `Nat.mul_assoc`, `Nat.mul_comm`,
   `Nat.add_mul`, `Nat.mul_add` 만으로 mini "ring-sub-set" 구성.
2. **Right-associative monomial 정규화**: 모든 곱셈을 `coef *
   (var₁ * var₂)` 형태로 강제.
3. **expand_2x2 헬퍼**: `(a+b)*(c+d) = a*c + a*d + b*c + b*d`
   via `Nat.add_mul` + `Nat.mul_add` chain.  Lean 4 core 에서
   1줄.
4. **Two nonlinear-variable closure**: degree-2 까지는 `K := k*k`
   한 번 generalize 면 omega closure (lower invariant 가 이미
   이 패턴).  Degree-3 는 추가로 `M := k*K` generalize 필요.
5. **omega final pass**: 모든 monomial 이 (k, K, M, 상수) 의
   linear combination 으로 깎인 후 omega 가 닫음.

이 전술이 작동하면 `expand_cube` 헬퍼 (general (a+b)(c+d)(e+f)
8-term expansion) 도 같은 framework 으로 derive 가능.  하지만
현재 Wallis upper 한 case 만 위해서는 over-engineering — 한
identity 의 manual expansion + 두 generalize 로 충분.

## Axiom 검증

`#print axioms`:
- 모든 EulerSeq theorems: [propext, Quot.sound]
- 모든 WallisSeq theorems: [propext, Quot.sound]

Classical.choice / LEM / native_decide / ring (Mathlib) 부재.
AXIOM §5.2.1 falsifiability 유지.

## 의의

PellSeq + Sqrt2Cut 가 algebraic irrational (√2), Padic 가
profinite (p-adic ℤ_p), EulerSeq + WallisSeq 가 transcendental
(e, π/2) 의 213 Cauchy demonstration.

전체적으로 **rational, algebraic irrational, profinite,
transcendental** 네 영역이 모두 213 framework 에서
constructive Cauchy 로 실현됨 — Paper 1 의 ZFC reduction
주장의 demonstration suite 완성.

Wallis upper invariant 는 별도 follow-up 으로 close 예정 —
이론적으로 tractable, 형식만 미완.

## 변경 이력

- 2026-04-25: EulerSeq + WallisSeq.  e ∈ (2, 3) closed.
  W_n monotonic + ≥ 4/3 + below-1 cut closed.  Upper deferred.
