# Linear Algebra 213 — Blueprint

**우선순위**: ★★ (대부분 분야의 빌딩 블록)

---

## 1. 왜 이 분야인가

ZFC linear algebra:
- Vector space, basis, dimension
- Linear transformation, matrix
- Eigenvalue/eigenvector, diagonalization

213 의 자연 등장:
- **multivariable 213** 의 `MultiCut n = Fin n → Cut` 이
  자연 vector space
- **finite 차원** 부터 시작 — atomic structure d=5 직접 활용
- 무한 차원은 functional 213 으로 lift

## 2. 213-native 등장

### 2.1 VectorCut n = MultiCut n

```
VectorCut n := Fin n → Cut    -- n-차원 cut vector
```

이미 multivariable 213 (blueprint 02) 에서 기초 형성.

### 2.2 Matrix = `Fin m → VectorCut n`

```
MatrixCut m n := Fin m → VectorCut n
```

Matrix multiplication: composition of linear maps.

### 2.3 Determinant via atomic counting

213 의 d=5, 4-simplex 의 *오리엔테이션* 이 자연 sign.
Permutation parity = atomic counting.

### 2.4 Eigenvalue — discrete spectrum

Finite-dim diagonalization 은 polynomial root finding.  분석학
213 의 polynomial chain (cutPow) 활용.

### 2.5 Tensor product

`(VectorCut m) ⊗ (VectorCut n) = MultiCut (m+n)` 또는 product.
Atomic 5 ⊗ 5 = 25 (d²) 자연 등장 — 213 의 GUT 채널.

## 3. 빌딩 블록

| 도구 | 활용 |
|---|---|
| `MultiCut n` (blueprint 02) | vector |
| `cutSum, cutMul` | vector arithmetic |
| `cutPow` | matrix power |
| atomic structure d=5 | natural dim |
| App/Simplex.lean | 4-simplex 직접 |

## 4. Phase 계획

### Phase LA — VectorCut + arithmetic (3-5 commits)

1. `VectorCut n` 정의
2. `vAdd`, `vScale`, `vDot`
3. Basis: `e_i` 정의
4. Linear independence

### Phase LB — Matrix + transformations

1. `MatrixCut m n`
2. Matrix multiplication
3. Identity, transpose
4. Linear map ↔ matrix correspondence

### Phase LC — Determinant + inversion

1. det via permutation expansion (atomic counting)
2. det of triangular matrix
3. Cofactor + adjugate
4. Inverse formula

### Phase LD — Eigen

1. Characteristic polynomial (cutPow chain)
2. Eigenvalue propEq for diagonal
3. Diagonalization for symmetric (real eigenvalue)

### Phase LE — Tensor + Capstone

1. Tensor product
2. d ⊗ d = d² (atomic, GUT 연결)
3. Capstone — 학부 선형대수 1년차

## 5. 다른 트랙 연결

- **Standard Model**: CKM/PMNS = 3×3 unitary matrix
- **Atoms**: orbital matrix
- **Yang-Mills**: gauge group representation
- **DHA** (S₅): permutation matrix
- **Group theory** (blueprint 11): GL(n)

## 6. 미해결 / Open

- **SVD** — singular value decomposition
- **Jordan canonical** — eigenvalue with multiplicity
- **Tensor algebra** — exterior, symmetric

## 7. 핵심 인사이트 (★)

★ **dim = atomic** — d=5 가 자연 dim, 더 큰 차원은 product.

★ **Det = atomic permutation** — orientation cohomological.

★ **GUT 채널 25 = d² = 5 ⊗ 5** — linear algebra 가 직접 표준
모형 그룹 구조 등장.

## 8. 첫 마라톤 명령

```
"Phase LA 시작.  VectorCut n + vAdd/vScale + linear independence"
```

