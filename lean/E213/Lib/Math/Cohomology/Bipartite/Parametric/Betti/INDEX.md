# Bipartite/Parametric/Betti — universal δ⁰-kernel of K_{NS,NT}^{(c)}

The universal `b₀` (δ⁰-kernel = constants) of the complete-bipartite
coboundary, ∅-axiom for every connected deployment (NS ≥ 1, NT ≥ 1,
c ≥ 1).  Finite cardinalities are counted as `List.length` over
`Combinatorics.BoolEnum` enumerations — no `Fintype`, `funext`, or core
`Nat.div`.

## File map

| File | PURE | Content |
|---|---|---|
| `KernelConstancyUniversal.lean` | 20 | **b₀ product-indexed**: `delta0Tri` (edges `Fin NS × Fin NT × Fin c`, division-free) + `isKer_iff_const` / `isKer_const_false_or_true` / `isKer_root_determines` (dim ker = 1) + `Combinatorics.GraphConnectivity` instantiation (`bipAdj_connected`) |

## Dependency chain

```
CochSpaces (parent dir)
   └── KernelConstancyUniversal
         └── (BoolEnum, ListCount → List213)
```

## Consumers

`Math/Geometry/GeometrizationConjecture/KChartLensAbstract.lean` —
universal M2 chart-axes partition (`selfPointingAxes = 1` derived from
the 1-dimensional δ⁰-kernel for every connected K).
