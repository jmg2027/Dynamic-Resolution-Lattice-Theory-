# Bipartite/Parametric/Betti — universal Betti numbers of K_{NS,NT}^{(c)}

The universal `b₀` / `b₁` of the complete-bipartite coboundary, ∅-axiom
for every connected deployment (NS ≥ 1, NT ≥ 1, c ≥ 1).  Finite
cardinalities are counted as `List.length` over `Combinatorics.BoolEnum`
enumerations — no `Fintype`, `funext`, or core `Nat.div`.

## File map

| File | PURE | Content |
|---|---|---|
| `KerSizeUniversal.lean` | 4 | **b₀ on the flat operator**: `ker_iff_constant` — `(∀ e, CochSpaces.delta0 σ e = false) ↔ (∀ i j, σ i = σ j)` for the canonical flat coboundary (edges `Fin (c·NS·NT)`), via `Meta.Nat.NatDiv213` pure division |
| `KernelConstancyUniversal.lean` | 20 | **b₀ product-indexed companion**: `delta0Tri` (edges `Fin NS × Fin NT × Fin c`, division-free) + `isKer_iff_const` / `isKer_const_false_or_true` / `isKer_root_determines` (dim ker = 1) + `Combinatorics.GraphConnectivity` instantiation (`bipAdj_connected`) |
| `PathCoboundary.lean` | 5 | **`\|im δ⁰\| = 2^(V−1)` general**: `im_count_inj_complement` — any complement-invariant + head-`false`-injective map has image `2^(V−1)` (rank-nullity `2^V/2`); `im_pathDelta_card` is the path-graph instance |
| `KEdgeCochain.lean` | 14 | **`\|im δ⁰_K\| = 2^(V−1)` for the genuine K coboundary**: list-valued `edgeCochain` (`σ[s]⊕σ[NS+t]`) + `edgeCochain_complement` + `edgeCochain_inj_headFalse` (connectivity reconstruction) → `im_edgeCochain_card` + `im_edgeCochain_K32` (`2^4`) |
| `BettiOneUniversal.lean` | 3 | **b₁ = E − V + 1**: assembles the cardinalities (`\|C⁰\| = 2^V`, `\|ker\| = 2`, `\|im\| = 2^(V−1)`) + rank-nullity / first-iso arithmetic.  `betti_one_universal` + `betti_one_K32` (`b₁ = 8 = NS² − 1 = 1/α₃`) |

## Dependency chain

```
CochSpaces (parent dir)
   ├── KerSizeUniversal
   └── KernelConstancyUniversal
         └── (BoolEnum, ListCount → List213)
               PathCoboundary
                 └── KEdgeCochain
               BettiOneUniversal
```

## Narrative

`theory/math/cohomology/bipartite.md` — "Universal kernel = constants"
and "Universal first Betti number" sections.
