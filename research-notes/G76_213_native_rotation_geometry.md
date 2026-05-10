# G76: 213-native expression of rotation/spiral

## User directive (2026-05-09)

> "이걸 Raw의 Nat213렌즈의 네이티브로 된 토폴로지나 그래프이론
>  혹은 코호몰로지든 선대수든 으로 이런 모양이다 그리고 회전이
>  뭐고 어케 꼬이는거고 이런걸 보이는거임 — 그게 진정한 이해의 시작"

Express the Möbius P / 1-glue / NS-NT rotation using **213-native
mathematical structures** (graph, topology, cohomology, linear
algebra), so we can SEE the shape and UNDERSTAND the rotation.

## Three 213-native realizations

### (A) Graph realization: K_{3,2}^{(2)} bipartite multigraph

**Existing infrastructure**: `Lib/Math/Cohomology/Bipartite/V32.lean`

K_{3,2}^{(2)} = bipartite multigraph with:
- **5 vertices** = d (3 S-vertices + 2 T-vertices)
- **12 edges** = NS · NT · 2 (each S-T pair has 2 parallel edges,
  reflecting the binary-base structure of Möbius P)

Atomicity correspondence:
| Graph quantity | Value | Atomicity |
|---|---|---|
| Total vertices | 5 | d |
| S-vertices | 3 | NS |
| T-vertices | 2 | NT |
| Total edges | 12 | NS · NT · 2 |
| Edges per S-T pair | 2 | NT (binary multiplicity) |

The graph IS the 213 universe.  The 1-glue manifests as the
**bipartite-edge structure** (every S connects to every T).

### (B) Linear algebra: Möbius P as SL(2, ℤ) generator

**Existing infrastructure**: `Theory/Raw/Mobius.lean`

P = `[[2, 1], [1, 1]]` ∈ SL(2, ℤ) since det(P) = 1.

The "rotation" mathematically:
- Eigenvalues: φ² (= (3 + √5)/2 ≈ 2.618) and 1/φ² (= (3 − √5)/2 ≈ 0.382)
- Eigenvalues PRODUCT = φ² · 1/φ² = det = 1 (norm-preserving)
- Eigenvalues SUM = φ² + 1/φ² = trace = 3 = NS

So the "rotation by golden angle" in the (NS, NT) basis is
encoded by P's spectrum.  Each iteration:
- Stretches one axis by φ²
- Compresses the other by 1/φ²
- NET: pure rotation in (φ², 1/φ²)-eigenbasis

### (C) Pell-Fib spiral: iteration trajectory

**Existing infrastructure**: `Lib/Math/DyadicFSM/Fib/PellRelation.lean`

Iterating P on `(1, 1)` produces the Pell-Fib sequence:

```
(1, 1) → (3, 2) → (8, 5) → (21, 13) → (55, 34) → ...
   ▲       ▲       ▲          ▲           ▲
   │       │       │          │           │
   │       └── F_4, F_3       └── F_8, F_7
   └── F_2, F_1   F_6, F_5    F_10, F_9   ...
```

These are PAIRS of consecutive odd-indexed Fibonacci numbers.
Each iteration:
- Doubles the index by 2
- Ratio approaches φ ≈ 1.618

The spiral grows in **φ²-radius per step** but stays on the
**golden-section line** (= rotation through golden angle).

## Synthesis: how the three connect

```
K_{3,2}^{(2)} graph     ←──── 213 atomicity (NS, NT, d, NS·NT·2)
       ↓
       │ encoded as
       ↓
Möbius P matrix [[2,1],[1,1]]   ←─── trace=3, det=1, disc=5
       ↓
       │ iterates as
       ↓
Pell-Fib spiral (1,1)→(3,2)→(8,5)→...   ←─── golden rotation
```

**The "rotation" is**:
- At graph level: cyclic permutation of K_{3,2} vertices via Z_5
- At matrix level: P-action on ℤ² preserving det = 1
- At iteration level: Pell-Fib spiral approaching φ-ratio

## What "꼬이는" (twisting) means

User's "어케 꼬이는거고": the spiral TWISTS because:

1. **Eigenvector mixing**: P has TWO eigenvectors (for φ² and 1/φ²).
   Generic vectors are LINEAR COMBINATIONS of both.  Iteration
   amplifies the φ²-component and shrinks the 1/φ²-component →
   trajectory rotates toward the φ²-eigenvector.

2. **Bipartite graph traversal**: in K_{3,2}, walking edges
   alternates S→T→S→T...  The 1-glue (= every S-T edge) is what
   enables this back-and-forth = the "twist".

3. **Det = 1 preservation**: at every iteration, the matrix's
   action preserves area (det = 1).  So the spiral conserves a
   specific INVARIANT (like angular momentum) — this is the
   "twist axis" of the rotation.

The TWIST is mathematically the **eigenvector convergence**: the
iteration "spirals into" the φ²-eigenvector, with each turn
preserving det.

## What we still need to formalize

To complete the user's vision:

1. ★ **K_{3,2}^{(2)} count theorems** connecting (5, 12) to (d, NS·NT·2)
2. **P spectral decomposition** (eigenvalues φ², 1/φ², trace = 3, det = 1)
3. **Concrete Pell-Fib iteration**: show P · (1, 1) = (3, 2),
   P · (3, 2) = (8, 5), etc.
4. **Z_5 rotation on K_{3,2}** vertices (cyclic permutation as
   "rotation")
5. **Eigenvector convergence**: as n → ∞, P^n · v approaches
   φ²-eigenvector direction

## Lean ∅-axiom witnesses (this commit)

`Theory/Nat213/RotationGeometry.lean` (NEW):
- K_{3,2} vertex count = d
- K_{3,2} edge count = 12 = NS · NT · 2
- Bipartite split = (NS, NT)
- Concrete P iteration: (1, 1) → (3, 2) → (8, 5) → (21, 13)
- Trace = 3 = NS, det = 1 = glue (re-witnesses)

## See also

- `lean/E213/Lib/Math/Cohomology/Bipartite/V32.lean` — K_{3,2}^{(2)}
- `lean/E213/Theory/Raw/Mobius.lean` — Möbius P
- `lean/E213/Lib/Math/DyadicFSM/Fib/PellRelation.lean` — Pell-Fib
- `research-notes/G70-G75` — atomicity, glue, det chain
