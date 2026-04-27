# Combinatorics 213 — Blueprint

**우선순위**: ★★★ (213 atomic structure 가 *직접 조합론*)

---

## 1. 왜 이 분야인가

ZFC combinatorics:
- Counting (binomial, multinomial)
- Permutations, partitions
- Graph theory (vertex, edge, cycle)
- Generating functions

213 의 자연 등장:
- **Raw 공리 + atomicity** = counting 의 본질
- **K_{3,2} bipartite** 이미 형식화 (물리트랙 Phase 2)
- **4-simplex Δ⁴** = 5 vertex K_5
- **Pigeonhole** 이미 OS layer 형식화

조합론은 **213 이 가장 자연스러운 분야** 중 하나.

## 2. 213-native 등장

### 2.1 Atomic counting

물리트랙이 이미 형식화:
- 5 vertices (d=5)
- C(5,2) = 10 pairs
- 3 AA + 1 BB + 6 AB partition
- 4-simplex face counts: 1+5+10+10+5+1

이게 **조합론의 첫 정리들** 직접 propEq.

### 2.2 Permutation = bisection trajectory

n elements 의 permutation = path in dyadic tree depth log(n!).
S₅ 의 |S₅| = 120 자연 등장.

### 2.3 Graph theory

Vertex set + edge set = 213 atomic structure.  K_5, K_{3,2}
이미 형식화.  Cycle space = cohomology (FluxCut 활용).

### 2.4 Generating functions

f(x) = Σ aₙ xⁿ = power series (분석학 213 활용).

### 2.5 Pigeonhole (이미 형식화)

OS/Pigeonhole.lean 이 이미 213 의 atomic counting 활용.

### 2.6 Catalan, Stirling, Bell numbers

Recursive 정의 → induction propEq.  cutPow 와 partialSum 결합.

## 3. 빌딩 블록

| 도구 | 활용 |
|---|---|
| Raw 공리 | atomicity |
| `OS/Pigeonhole.lean` | 이미 형식화 |
| `App/Simplex.lean` | 4-simplex |
| 물리트랙 `Pairs.lean` | K_{3,2}, 10 pairs |
| `cutPow x n` | binomial via series |
| `partialSum` | sum identities |
| `Fin n` | finite set |

## 4. Phase 계획

### Phase CoA — Binomial + permutation (3-5 commits)

1. `binomial n k` 정의 (Pascal recursion)
2. C(n+1, k) = C(n, k-1) + C(n, k) propEq
3. `factorial n`, permutation count
4. Binomial theorem (cutPow expansion)

### Phase CoB — Graph theory

1. `Graph V` (vertex + edge set)
2. K_n complete graph
3. K_{3,2} bipartite (이미)
4. Cycle, path, tree

### Phase CoC — Catalan + Stirling

1. Catalan number recursion
2. Stirling first/second kind
3. Bell number

### Phase CoD — Generating functions

1. Formal power series (cutPow + partialSum)
2. exp/log generating function
3. Convolution

### Phase CoE — Capstone

학부 조합론 1년차.

## 5. 다른 트랙 연결

- **물리트랙 Phase 2**: K_{3,2}, atomic counting (직접 활용)
- **DHA**: S₅ 표현론 (permutation 그룹)
- **Atoms**: orbital 계수 = 조합 (n, l, m)
- **Yang-Mills**: gauge 채널 = path counting
- **Standard Model**: 25 GUT 채널 = 5 ⊗ 5

## 6. 미해결 / Open

- **Ramsey theorem** — 213-native?
- **Erdős–Ko–Rado** — finite combinatorics
- **Probabilistic method** — Probability 213 활용

## 7. 핵심 인사이트 (★)

★ **조합론 = 213 의 본업** — atomic counting 그 자체.

★ **K_{3,2} = 6 cross pairs** — 이미 propEq 형식화 (물리).

★ **Catalan/Stirling 가 213 trees 의 자연 단위** — bisection
tree 와 직접 매핑.

## 8. 첫 마라톤 명령

```
"Phase CoA 시작.  binomial n k + Pascal recursion propEq"
```

