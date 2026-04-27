# Number Theory 213 — Blueprint

**우선순위**: ★★ (213 의 atomic structure → 정수론 자연)

---

## 1. 왜 이 분야인가

ZFC 정수론:
- ℤ, ℚ → ℝ → ℂ chain
- Primes, divisibility
- Diophantine equations
- Algebraic number theory (ℤ[i], ℤ[√d])

213 의 자연 등장:
- **Raw 공리 자체가 atomicity** — primes 의 의미가 다름
- **CayleyDickson** 이미 ℤ[i], ℤ[√2], ℤ[ω] 형식화 (29 파일)
- **Padic** 이미 형식화
- **dyadic prime 2** 가 213 자체

특히 *Critical line* 트랙 (RH/GRH) 와 깊이 연결.

## 2. 213-native 등장

### 2.1 Atomic primes — 2와 3

213 atom pair {2, 3} → 두 atomic prime.  d = 5 = 2 + 3.

소수 정의 = atomic counting:
- 2 = base of dyadic
- 3 = NS (atom 한쪽)
- 5 = d (전체)
- 다른 소수 = 213 의 *유도*

### 2.2 Divisibility on dyadic tree

a | b 가 ZFC 에선 ∃ k, b = a·k.
213-native: bisection trajectory 의 *주기성*.

### 2.3 Modular arithmetic

ℤ/nℤ = atomic counting modulo n.  Pigeonhole (이미 OS 형식화)
직접 활용.

### 2.4 Continued fractions

dyadic tree 에서 binary expansion 의 일반화.  이미 분석학 213
의 cut representation 이 그것.

### 2.5 Algebraic numbers

`Sqrt2Cut`, `Sqrt3IrrationalPure`, `Sqrt5IrrationalPure`,
`PellSeq`, `Padic` 이미 형식화.  일반화 필요:
- ℤ[√d] for general d
- Galois extension (critical-line/ 트랙 이미)

### 2.6 Riemann zeta + RH

Critical-line 트랙 (193 파일!) 이 이미 작업 중.  분석학 213
+ 복소 213 (blueprint 04) 결합 시 더 깊은 도구.

## 3. 빌딩 블록

| 도구 | 활용 |
|---|---|
| Raw 공리 + atomicity | atomic primes 2, 3 |
| `OS/Pigeonhole.lean` | modular arithmetic |
| `OS/PrimitiveSizes.lean` | counting |
| CayleyDickson `ZSqrt*` | algebraic integers |
| `Padic` | p-adic numbers |
| `EulerSeq` | e (transcendental) |
| `WallisSeq` | π/2 (transcendental) |
| critical-line/ track | RH/GRH 형식화 진행 중 |

## 4. Phase 계획

### Phase NA — Atomic primes (3-5 commits)

1. `AtomicPrime := { 2, 3 }` (Raw 공리 직접)
2. `Prime n := atomic-counting derivable`
3. 5 = 2 + 3 (atomic decomposition propEq)
4. d^d = 5^5 = 3125 (자연 발생)

### Phase NB — Divisibility + modular

1. `Divides a b` via dyadic
2. `ModN n` arithmetic (Fin n 활용)
3. Fermat little theorem skeleton
4. CRT (Chinese remainder) — atomic 활용

### Phase NC — Algebraic numbers

1. ℤ[i], ℤ[√d] 일반화 (CayleyDickson 위)
2. Norm, trace propEq
3. Unit group 구조

### Phase ND — p-adic + Continued fractions

1. p-adic valuation propEq
2. p-adic limit (이미 Padic 보유)
3. Continued fraction expansion (binary)

### Phase NE — Zeta + RH connection

1. Riemann zeta as Dirichlet series (분석학 + 복소 213)
2. RH skeleton
3. critical-line/ 트랙과 통합

### Phase NF — Capstone

학부 정수론 + 첫 algebraic number theory.

## 5. 다른 트랙 연결

- **Critical Line / RH** (193 파일!): 직접 통합
- **CayleyDickson** (29 파일): 이미 algebraic number ring
- **Atoms**: atomic counting
- **Standard Model**: prime 분포 → mass spectrum

## 6. 미해결 / Open

- **무한 prime** — 213 의 atomicity 가 *유한* 측면
- **Class field theory** — Galois extension 의 213-native?
- **Modular forms** — 복소 213 활용

## 7. 핵심 인사이트 (★)

★ **Prime 2, 3 = atomic** — 213 자체의 *씨앗*.  나머지 prime 은
유도.

★ **Padic 213-native** — 이미 형식화 완료.

★ **Critical-line 트랙 = 정수론 213 의 RH 측면** — 통합 가능.

## 8. 첫 마라톤 명령

```
"Phase NA 시작.  AtomicPrime 정의 + 5 = 2 + 3 propEq + d^d propEq"
```

