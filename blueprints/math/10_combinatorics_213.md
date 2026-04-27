# Combinatorics 213 — Blueprint

**Priority**: ★★★ (213 atomic structure *is* combinatorics directly)

---

## 1. Why This Field

ZFC combinatorics:
- Counting (binomial, multinomial)
- Permutations, partitions
- Graph theory (vertex, edge, cycle)
- Generating functions

Natural emergence in 213:
- **Raw axiom + atomicity** = the essence of counting
- **K_{3,2} bipartite** already formalized (physics track Phase 2)
- **4-simplex Δ⁴** = 5 vertex K_5
- **Pigeonhole** already formalized in OS layer

Combinatorics is one of **213's most natural fields**.

## 2. 213-native Emergence

### 2.1 Atomic counting

Physics track already formalized:
- 5 vertices (d=5)
- C(5,2) = 10 pairs
- 3 AA + 1 BB + 6 AB partition
- 4-simplex face counts: 1+5+10+10+5+1

These are **the first theorems of combinatorics** directly as propEq.

### 2.2 Permutation = bisection trajectory

Permutation of n elements = path in dyadic tree depth log(n!).
S₅'s |S₅| = 120 naturally appears.

### 2.3 Graph theory

Vertex set + edge set = 213 atomic structure.  K_5, K_{3,2}
Already formalized.  Cycle space = cohomology (using FluxCut).

### 2.4 Generating functions

f(x) = Σ aₙ xⁿ = power series (using Analysis 213).

### 2.5 Pigeonhole (already formalized)

OS/Pigeonhole.lean already uses 213's atomic counting.

### 2.6 Catalan, Stirling, Bell numbers

Recursive definition → induction propEq.  Combine cutPow and partialSum.

## 3. Building Blocks

| Tool | Use |
|---|---|
| Raw axiom | atomicity |
| `OS/Pigeonhole.lean` | already formalized |
| `App/Simplex.lean` | 4-simplex |
| Physics track `Pairs.lean` | K_{3,2}, 10 pairs |
| `cutPow x n` | binomial via series |
| `partialSum` | sum identities |
| `Fin n` | finite set |

## 4. Phase Plan

### Phase CoA — Binomial + permutation (3-5 commits)

1. Define `binomial n k` (Pascal recursion)
2. C(n+1, k) = C(n, k-1) + C(n, k) propEq
3. `factorial n`, permutation count
4. Binomial theorem (cutPow expansion)

### Phase CoB — Graph theory

1. `Graph V` (vertex + edge set)
2. K_n complete graph
3. K_{3,2} bipartite (already done)
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

First year undergraduate combinatorics.

## 5. Connections to Other Tracks

- **Physics track Phase 2**: K_{3,2}, atomic counting (direct use)
- **DHA**: S₅ representation theory (permutation group)
- **Atoms**: orbital count = combination (n, l, m)
- **Yang-Mills**: gauge channels = path counting
- **Standard Model**: 25 GUT channels = 5 ⊗ 5

## 6. Open Problems

- **Ramsey theorem** — 213-native?
- **Erdős–Ko–Rado** — finite combinatorics
- **Probabilistic method** — use Probability 213

## 7. Key Insights (★)

★ **Combinatorics = 213's home field** — atomic counting itself.

★ **K_{3,2} = 6 cross pairs** — already propEq formalized (physics).

★ **Catalan/Stirling are natural units of 213 trees** — bisection
tree directly mapped.

## 8. First Marathon Command

```
"Start Phase CoA.  binomial n k + Pascal recursion propEq"
```

