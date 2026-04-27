# Multivariable Calculus 213 — Blueprint

**우선순위**: ★★★ (분석학 213 의 직접 확장)

---

## 1. 왜 이 분야인가

분석학 213 은 1변수 (Cut → Cut) 함수만 다룸.  학부 2학년/공학
미적분의 핵심:
- partial derivative ∂f/∂xᵢ
- gradient ∇f, divergence ∇·F, curl ∇×F
- multiple integral ∫∫ f dA, ∫∫∫ f dV
- Stokes' theorem (general dimension)

213 는 *이미 cohomological 구조* 를 갖고 있어서 multivariable
은 별로 어렵지 않을 수 있음 — 1변수 framework 의 product space
로 자연 확장.

## 2. 213-native 등장

### 2.1 Multi-Cut

```
MultiCut n := Fin n → Cut
  -- n-차원 점 = n개의 cut 의 tuple
```

Function: `MultiCut n → Cut` 또는 `MultiCut n → MultiCut m`.

### 2.2 Partial derivative

i-번째 cut 만 가변, 나머지 고정:

```
def partialAt (f : MultiCut n → Cut) (i : Fin n) (x : MultiCut n)
    : (Cut → Cut) :=
  fun y => f (x.update i y)
```

이게 1변수 함수 → IsDifferentiable 적용 가능.

### 2.3 Gradient as MultiCut-valued

```
def gradient (f : MultiCut n → Cut) (x : MultiCut n) : MultiCut n :=
  fun i => (partialAt f i x).derivative ?
```

Output 도 n-tuple.  벡터 미적분 자연 확장.

### 2.4 Divergence + curl via cohomology

213 의 `localDivergence` 는 1차원.  n차원 일반화:
```
def divergence (F : MultiCut n → MultiCut n) (x : MultiCut n) : Cut :=
  Σᵢ (partialAt (Fᵢ) i x).derivative
```

= ∑ ∂Fᵢ/∂xᵢ — 표준 정의.  **1차원 FluxCut 의 자연 일반화**.

### 2.5 Multiple integral via tensor Riemann

```
def riemannMulti (f : MultiCut n → Cut) (db : Fin n → DyadicBracket) (depth : Nat)
    : Cut := Σ over product grid
```

Product of dyadic brackets → multi-dimensional Riemann sum.

## 3. 이미 깔린 빌딩 블록

| 도구 | 활용 |
|---|---|
| `IsDifferentiable f` | 각 partial 마다 1변수 적용 |
| `IsAntiderivative` | iterated integral (Fubini) |
| `FluxCut` | 1차원 1-cochain → n차원 (n-1)-cochain |
| `dyadicIntervalAB` | n-cube product |
| `cutPow x n` | 다변수 다항식 (개별 변수마다) |

## 4. Phase 계획

### Phase MA — MultiCut 기초 (3-5 commits)

1. `MultiCut n := Fin n → Cut`
2. `MultiCut.update`, `MultiCut.const`, `MultiCut.basis`
3. Vector arithmetic: `multiAdd`, `multiSub`, `multiScale`
4. `unitNCube n` — [0,1]^n product bracket

### Phase MB — Partial derivative

1. `partialAt f i x` 정의
2. `IsPartiallyDifferentiable f i` — i-번째 partial IsDifferentiable
3. `IsCInfDifferentiable f` — 모든 partial 미분 가능
4. 다항식 partials: ∂(x²y)/∂x = 2xy 형식 propEq

### Phase MC — Gradient + divergence + curl

1. `gradient f` : MultiCut n → MultiCut n
2. `divergence F` : MultiCut n → Cut (sum of partials)
3. `curl F` (n=3) : MultiCut 3 → MultiCut 3
4. Identity: ∇·(∇×F) = 0 (curl of grad is zero)

### Phase MD — Multiple integral

1. `riemannMulti f db_n depth`
2. Fubini propEq: 순서 무관 (특수 case 부터)
3. Iterated `IsAntiderivative` 형식
4. n-cube 위 ∫ const = product of edge lengths

### Phase ME — Stokes' theorem (cohomological)

분석학 213 의 1차원 FTC 가 *Stokes' theorem 1-d 버전*.
n차원 자연 일반화:
- ∫_M dω = ∫_∂M ω
- 213-native: localDivergence integrated over volume = boundary flux

### Phase MF — Capstone

학부 2학년 미적분 / 공학수학 핵심.

## 5. 다른 트랙 연결

- **Yang-Mills**: 4차원 ∫ F ∧ *F (= 작용)
- **Cosmology**: 3+1 차원 시공간 적분
- **Quantum gravity**: 시공간 창발 → multivariable 자연
- **Atoms**: Wedge screening = 4차원 simplex 적분
- **DHA**: 다변수 Fourier

## 6. 미해결 / Open

- **Coordinate change** (Jacobian) — 213-native?
- **Manifold** 정의 — 213 dyadic 위 어떤 manifold?
- **Riemannian metric** — cohomological?
- **Differential form** general — exterior algebra 213-native

## 7. 핵심 인사이트 (★)

★ **n차원 = n개 1차원의 product** — 분석학 213 framework 가
직접 lift.

★ **Stokes' theorem = cohomological FTC 의 n차원** — 이미
FluxCut + localDivergence 가 1d 의 그것.

## 8. 첫 마라톤 명령

```
"Phase MA 시작.  MultiCut n 정의 + vector arithmetic + unitNCube"
```

