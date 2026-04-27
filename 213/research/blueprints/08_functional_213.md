# Functional Analysis 213 — Blueprint

**우선순위**: ★ (학부 3-4년 수학, 양자역학 응용)

---

## 1. 왜 이 분야인가

ZFC functional analysis:
- Banach space (norm), Hilbert space (inner product)
- Operator theory, spectral theorem
- Hahn-Banach, open mapping (Choice 의존!)

213 의 자연 등장:
- **분석학 213** 의 Cut 공간이 자연 functional space
- **CayleyDickson** 의 ℤ[i] etc. 가 inner product space candidates
- σ-algebra 거부했듯이 **non-constructive 정리 거부**

## 2. 213-native 등장

### 2.1 Cut 공간 = function space

`Cut → Cut` 자체가 함수공간.  norm, inner product 정의 가능:

```
def cutNorm (f : Cut → Cut) : Cut := ...   -- sup over dyadic
def cutInner (f g : Cut → Cut) : Cut := ∫ f * g dx
```

### 2.2 Banach 공간 — Cauchy complete

분석학 213 의 `CauchyCutSeq` 가 이미 Cauchy 완비성.  Banach
space = 함수의 Cauchy 완비.

### 2.3 Hilbert 공간

Inner product = `cutInner`.  `IsAntiderivative.integral` 직접
활용.  L² 공간 자연.

### 2.4 Operator + spectrum

Linear operator T : Cut → Cut.  Spectrum = `cohomEquiv` 형식
eigenvalue.

### 2.5 Hahn-Banach 거부

ZFC 의 Hahn-Banach 는 Choice 의존.  213 에선 **directly
constructible extension** 만.  이게 *제한* 아니라 *feature*.

## 3. 빌딩 블록

- 분석학 213 (cut, IsDifferentiable, Cauchy)
- 측도 213 (Lebesgue 213)
- 복소 213 (complex Hilbert)

## 4. Phase 계획

### Phase FA — Norm + Cauchy (3-5 commits)

1. `cutNorm` 정의 + propEq sup
2. Cauchy 완비 (분석학 213 활용)
3. Banach skeleton

### Phase FB — Inner product + Hilbert

1. `cutInner` via integral
2. Cauchy-Schwarz propEq
3. Orthogonal projection

### Phase FC — Operator + spectrum

1. Linear operator on Cut → Cut
2. Bounded operator
3. Spectrum (eigenvalue) — finite dim 부터

### Phase FD — Capstone

학부 functional analysis 1년차.

## 5. 다른 트랙 연결

- **Atoms**: orbital = Hilbert space 원소
- **Quantum gravity**: amplitude
- **Yang-Mills**: gauge field 공간
- **DHA**: Fourier basis = orthonormal

## 6. 미해결 / Open

- **Hahn-Banach** — Choice 부재 → constructive 부분만
- **Open mapping theorem** — 마찬가지
- **Spectral theorem 일반** — 일부분만

## 7. 핵심 인사이트 (★)

★ **Banach completion = Cauchy** — 분석학 213 직접 활용.

★ **L² = cutPow integrable** — 측도 213 + 분석학 213 결합.

★ **Choice 거부 = 제약 vs feature** — constructive 만으로 양자역학
formal 가능성 시험.

## 8. 첫 마라톤 명령

```
"Phase FA 시작.  cutNorm + Banach skeleton on Cut → Cut"
```

