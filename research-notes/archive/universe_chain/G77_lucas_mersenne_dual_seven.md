# G77: P^k power formulas — Lucas-like + Mersenne dual at 7

## User exploration (2026-05-09)

User computed:
- P^(-1) = [[1, -1], [-1, 2]] ✓
- P^2 = ?, P^3 = [[13, 8], [8, 5]] ✓
- "P^5 + P^(-1) = 14 7 7 7 = 7P" — INCORRECT (actual: 18·P^2)
- "node lens 1, 3, 7 = 2^k - 1" (Mersenne)

The user's intuition about "7" was correct in spirit but the
specific identity was off.  The actual structures explain BOTH
the 7 and the broader pattern.

## Correction: P^5 + P^(-1) = 18·P^2

By Cayley-Hamilton (P satisfies x² - 3x + 1 = 0):
- P² = 3P - I
- P³ = 8P - 3I
- P⁴ = 21P - 8I
- P⁵ = 55P - 21I
- P^(-1) = 3I - P  (from x⁻¹ = 3 - x)

So P^5 + P^(-1) = (55P - 21I) + (3I - P) = 54P - 18I = 18·(3P - I) = 18·P²

Concrete: P^5 + P^(-1) = [[90, 54], [54, 36]] = 18 · [[5, 3], [3, 2]] = 18·P²

## Where 7 ACTUALLY lives: Lucas-like sequence

For matrix M with characteristic poly x² - Tx + D = 0 (here T=3, D=1):

  **M^k + M^(-k) = L_k · I**

where L_k satisfies the same recurrence:
  L_{k+1} = T · L_k - D · L_{k-1} = 3·L_k - L_{k-1}
  L_0 = 2, L_1 = 3, L_2 = 7, L_3 = 18, L_4 = 47, L_5 = 123, ...

These are eigenvalue power sums: L_k = α^k + β^k where
α = φ², β = 1/φ² = α^(-1).

### Concrete:
- P + P^(-1) = 3·I = L_1·I  (top-left: 2+1=3, bot-right: 1+2=3)
- P² + P^(-2) = 7·I = L_2·I  ★ (top-left: 5+2=7)
- P³ + P^(-3) = 18·I = L_3·I
- ...

So 7 first appears as L_2 = trace of P² + traceless inverse component.

## Where Mersenne 1, 3, 7 lives: node lens

The "node lens" applied to canonical full binary Raw trees gives
node count = `2^(depth+1) - 1` (Mersenne):

| Depth | Tree | Node count = 2^(d+1) - 1 |
|---|---|---|
| 0 | atom | 1 = M_1 |
| 1 | slash(a, b) | 3 = M_2 |
| 2 | slash(slash(a,b), slash(a,b)) | 7 = M_3 |
| 3 | full depth-3 | 15 = M_4 |
| ... | ... | 2^(k+1) - 1 |

So Mersenne arises naturally as **depth-counting of binary Raw**.

## The dual appearance of 7

| Sequence | Index | Value |
|---|---|---|
| Lucas L_k (Möbius P trace power) | k=2 | **7** |
| Mersenne M_k (Raw depth-node count) | k=3 | **7** |

**Same number 7, two completely different fold structures**.

This is significant because:
- Lucas L_k = α^k + β^k = φ²-based growth (golden ratio)
- Mersenne M_k = 2^k - 1 = pure binary doubling
- They COINCIDE at small k: L_1 = 3 = M_2, L_2 = 7 = M_3

After k=2 they diverge (L grows ~2.618^k, M grows ~2^k).

The coincidence at k ∈ {1, 2} is **the binary-golden bridge** —
the small-scale structure where binary atomicity (NT=2 → Mersenne)
and golden-spiral atomicity (P matrix → Lucas) AGREE.

## Structural meaning

**3 = NS = L_1 = M_2**: emerges in BOTH:
- Binary tree depth-1 has 3 nodes (Mersenne)
- Möbius P trace = 3 (Lucas L_1)

**7 = L_2 = M_3**: emerges in BOTH:
- Binary tree depth-2 has 7 nodes (Mersenne)
- P^2 + P^(-2) = 7·I trace (Lucas L_2)

After 7, the two sequences DIVERGE because:
- Mersenne is "discrete binary doubling"
- Lucas is "continuous golden rotation"

The bridge at 3 and 7 happens because at small scale, both
structures haven't yet "exploded" enough to differentiate.  The
golden spiral hasn't yet shown its non-binary nature.

## What user intuited about "−7"

User's "−7이 어디 있었는디" (where was -7?):

In `P^k - P^(-k)` (anti-symmetric), the off-diagonal entries are
non-zero (antisymmetric matrix).  Specifically:
- P - P^(-1) = 2P - 3I = [[1, 2], [2, -1]] — has -1, not -7
- P^2 - P^(-2) = [[3, 6], [6, -3]] — has -3 (= -L_1·1)

For -7 specifically, it might appear in:
- (P + P^(-1)) - (P^2 + P^(-2)) = 3I - 7I = -4I (no -7)
- L_2 - L_3 = 7 - 18 = -11 (no)
- More subtle: -7 could appear in **anti-symmetric component of
  Lucas-like sequence over ℤ[√5]**, but not directly in matrix
  entries.

So -7 is NOT in the immediate matrix calculations — it would require
extension to ℤ[φ] or similar to surface naturally.

## Lean ∅-axiom witnesses (this commit)

5 new theorems in `Theory/Nat213/RotationGeometry.lean`:
- p_plus_p_inv_top_left: 2 + 1 = 3 (= L_1)
- p2_plus_p_inv2_top_left: 5 + 2 = 7 (= L_2) ★
- mersenne_2_eq_ns: 2² - 1 = 3 = NS
- mersenne_3_eq_lucas_2: 2³ - 1 = 7
- ★★★ seven_dual_appearance: BOTH Lucas L_2 AND Mersenne M_3 = 7

## What this means for 213

The dual appearance 3 = M_2 = L_1 and 7 = M_3 = L_2 tells us:

> **At small scale (k=1, 2), the binary-doubling structure
> (Mersenne, NT-rooted) and the golden-rotation structure
> (Lucas, NS-trace) AGREE.  After k=2 they diverge, with golden
> growing faster than binary.**

This is the **binary-golden bridge** of 213: at the bottom (small k),
both atomicity readings give the same numbers (3, 7).  Higher up,
the φ-rotation overtakes binary doubling.

**5-perspective manifold (G74 conjecture)** could be related:
5 perspectives might correspond to k=0, 1, 2, 3, 4 of these
sequences before they fully decouple.

## See also

- `lean/E213/Theory/Nat213/RotationGeometry.lean` — 12 theorems
- `lean/E213/Theory/Nat213/OneAsGlue.lean` — det = glue
- `research-notes/G75` — det as axis-generator fold
- `research-notes/G76` — 213-native rotation geometry
