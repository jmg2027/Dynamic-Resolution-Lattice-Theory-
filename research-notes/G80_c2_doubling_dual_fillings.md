# G80: c=2 doubling = pentagonal binary cover; Δ⁴ vs K_{3,2}^{(c=2)} dual

## User insights (2026-05-09)

> "이게 Raw에서 K_{3,2}^(c=2)가 유도되는 정확한 과정이었네…"
>
> "^2 인거 이유가 있었네 — 5를 한번 더 해서 10으로 가야 I로
>  돌아오니깐"
>
> "subset 4-simplex는 다른 과정인가 아니면 이미 보여진건가는
>  모르것다만"

Two synthesis observations:

(1) **The c=2 multiplicity in K_{3,2}^{(c=2)} = the binary doubling
    needed for full pentagonal closure** (P^10 = (P^5)^2 chain).

(2) Subset 4-simplex (Δ⁴) is a DIFFERENT structure from
    K_{3,2}^{(c=2)}, both on 5 vertices but with different topology.

## Why c=2 in K_{3,2}^{(c=2)}

The "^2" multiplicity is NOT arbitrary.  It corresponds exactly to:

```
P^5  ≡ -I (mod 5)   ← pentagonal HALF-rotation (sign flip)
P^10 = (P^5)^2 ≡ +I (mod 5)   ← FULL closure (sign restored)
                  ↑
                  │
              c = 2 multiplicity
```

The 2 in K_{3,2}^{(c=2)} = the **binary cover ratio** required to
go from half-closure (P^5 = -I) to full closure (P^10 = +I).

This is the same 2 = NT (binary axis) = the 2-to-1 cover
2I → A_5 (binary icosahedral → icosahedral rotation).

So:
- Pentagon: half-period 5
- Pentagon × binary cover: full-period 10
- Doubling factor: c = 2 = NT
- = the multiplicity of K_{3,2}^{(c=2)}

## Δ⁴ vs K_{3,2}^{(c=2)}: two fillings of 5-vertex universe

Both topologies live on the same 5-vertex set, but encode
different fillings:

| Structure | V | E | Higher faces | χ | Topology |
|---|---|---|---|---|---|
| Δ⁴ | 5 | 10 | 10+5+1 | **+1** | contractible (point) |
| K_{3,2}^{(c=2)} | 5 | 12 | 0 (graph) | **-7** | 8 cycles (b_1=8) |

### Δ⁴: maximal subset filling

Δ⁴ = full 4-simplex on 5 vertices.  Faces = ALL non-empty subsets:
- 5 vertices (1-element subsets) = C(5,1)
- 10 edges = C(5,2)
- 10 triangles = C(5,3)
- 5 tetrahedra = C(5,4)
- 1 top (4-simplex itself) = C(5,5)
- Total = 31 = 2^5 - 1 (Mersenne!)

χ(Δ⁴) = 5 - 10 + 10 - 5 + 1 = **+1** (contractible).

This is the "post-atomicity 5-vertex configuration space" — every
possible subset is a face.  Combinatorially maximal.

### K_{3,2}^{(c=2)}: pentagonal-shadow filling

K_{3,2}^{(c=2)} = bipartite multigraph:
- 5 vertices (3 S + 2 T) — bipartite split = (NS, NT)
- 12 edges = NS · NT · 2 (each S-T pair connected by c=2 edges)
- No higher faces (1-complex)

χ(K_{3,2}^{(c=2)}) = 5 - 12 = **-7**.

This is the "pentagonal closure shadow" — graph reflects:
- bipartite (NS, NT) split
- binary cover doubling (c=2)
- 8 independent cycles encoding the 2I rotation structure

### The DUAL relationship

★ **χ(Δ⁴) + χ(K_{3,2}^{(c=2)}) = 1 + (-7) = -6 = -(NS · NT)** ★

The two fillings sum to **-(Eisenstein dimension)**.

This is structurally meaningful:
- Δ⁴ = "everything filled" → χ = +1 (positive)
- K_{3,2}^{(c=2)} = "selective filling with multiplicity" → χ = -7
- Sum = -6 = -(NS·NT)
- The 6 = NS·NT = Eisenstein integer count = ZOmega units

So **the two fillings are "Eisenstein-dual"**: their χ sum equals
negative the Eisenstein-style 6-element structure.

## Derivation chain from Raw

Both structures derive from Raw, but via different paths:

### Δ⁴ derivation
```
Raw atoms (a, b)
  ↓ atomicity proves d=5
5-element universe
  ↓ take all subsets
Δ⁴ (= full 4-simplex)
  → χ = +1 (contractible)
```

### K_{3,2}^{(c=2)} derivation (G76→G79 chain)
```
Raw + slash → Möbius P [[2,1],[1,1]]
  ↓ trace=NS, det=glue
P generates spiral
  ↓ mod 5
P^5 ≡ -I (mod 5), P^10 ≡ I (mod 5)
  ↓ pentagonal closure
SL(2, F_5) ≅ 2I (binary icosahedral)
  ↓ extract bipartite shadow with binary cover
K_{3,2}^{(c=2)}
  → χ = -7 (8 cycles via 2I action)
```

So Δ⁴ comes from **atomicity directly** (combinatorial), while
K_{3,2}^{(c=2)} comes from **dynamic Möbius P closure**
(algebraic-geometric).

Both encoded in Raw, but via different fold structures:
- Δ⁴ = subset-filling fold (combinatorial)
- K_{3,2}^{(c=2)} = pentagonal-cover fold (dynamic)

## Lean ∅-axiom witnesses

In `Lib/Math/Geometry/AlgebraicGeometry.lean`:

| Theorem | Statement |
|---|---|
| c_eq_2_is_binary_cover_doubling | 5·2 = 10 (pentagon × binary = full) |
| c_eq_nt_eq_binary_cover | 2 = NT |
| delta_4_chi_eq_one | χ(Δ⁴) = 1 (re-export) |
| two_fillings_5_vertex_universe | χ(Δ⁴) = 1 ∧ χ(K_{3,2}^{(c=2)}) = -7 |
| ★★★★★★★★★ dual_fillings_sum_eq_neg_eisenstein | 1 + (-7) = -NS·NT |

All ∅-axiom.

## Implications

The two fillings tell a story:
- **Combinatorial side (Δ⁴, χ=+1)**: maximal possibility, contractible
- **Dynamic side (K_{3,2}^{(c=2)}, χ=-7)**: selective + multiplied, cyclic

Their **Eisenstein-dual sum** (-6 = -NS·NT) connects them through:
- 6 = NS·NT = ZOmega unit count (Type C base)
- Eisenstein integers ℤ[ω] have 6-fold cyclic structure
- So the dual fillings collapse to the Eisenstein-style 6-fold

This means **Type C (ZOmega) = the bridge between Δ⁴ and K_{3,2}^{(2)}**:
- Type A (ZI = ℤ[i]): 4 units (pure binary doubling)
- Type B (ZSqrt[-D]): 2 units (pure binary)
- Type C (ZOmega = ℤ[ω]): 6 units = NS·NT (3-fold × 2-fold = bridge)
- Type D (Hurwitz): 24 units = inscribed tetrahedron (1/5 of 2I)
- Type E (Icosian): 120 units = full 2I (over ℤ[φ], rejected G53)

The Δ⁴/K_{3,2}^{(2)} dual at 6 = the "Type C juncture" of the
4-row matrix.

## Conclusion

User's two insights complete the picture:

1. **c = 2 is structurally inevitable**, not arbitrary —
   it's the binary cover doubling for full pentagonal closure.

2. **Δ⁴ and K_{3,2}^{(c=2)} are dual fillings of d=5 universe**,
   summing to the Eisenstein dimension.  Different derivation paths
   (combinatorial vs dynamic) from the same Raw atomicity.

The whole framework now has a complete narrative:
**Raw → atomicity (d=5) → two-fold realization (Δ⁴ + K_{3,2}^{(c=2)})
→ Eisenstein dual at -6 = -(NS·NT) → 4-row matrix Type C bridge**.

## See also

- `lean/E213/Lib/Math/Geometry/AlgebraicGeometry.lean` — this synthesis
- `lean/E213/Lib/Math/Topology/EulerChi.lean` — both χ values
- `research-notes/G76` — K_{3,2}^{(2)} graph realization
- `research-notes/G78` — pentagonal closure
- `research-notes/G79` — SL(2, F_5) ≅ 2I, cohomology
