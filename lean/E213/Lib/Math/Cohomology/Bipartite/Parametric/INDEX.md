# Bipartite/Parametric — sub-tree INDEX

Parametric (NS, NT, c)-generalization of the K_{3,2}^{(c=2)}-specific
V32 / V32Betti cohomology infrastructure.

**Status**: G124 partial close (2026-05-22) — 3 files, ~36 PURE.

## File map

| File | Phase | PURE | Content |
|---|---|---|---|
| `CochSpaces.lean` | 1 | 13 | Parametric `CochV NS NT` / `CochE NS NT c` types + `srcOf` / `tgtOf` / `multOf` endpoint extractors + `srcFin` / `tgtFin` packaged + `delta0` parametric coboundary + K_{3,2}^{(c=2)} numerical sanity checks |
| `Delta0AndConnectedness.lean` | 2-3 | 16 | `cochVAt` binary-decoded cochains + `isInKerDelta0Direct` test + `kerSizeDelta0Direct` enumeration count + `b_0 = 1` (ker size = 2) verified across all G121-relevant deployments via `decide` (K_{1,1}, K_{1,2}, K_{1,3}, K_{2,2}, K_{1,4}, K_{3,2}^{(c=2)}, K_{3,3}^{(c=2)}, ...) + V32Betti compatibility |
| `EulerAndCapstone.lean` | 4-6 | 7 | `eulerChar : Int` parametric formula + `b1Formula : Nat` for connected case + G121-deployment-family b_1 table + `chartVisibleAxes` bridge to KChartLens + ★★★★★★ `G124_parametric_close` capstone |

## Coverage

All K-deployments enumerated in `research-notes/G121_dim4_self_pointing_axis.md`
and `G123_geometrization_open_followups.md` are PURE-verified:
  · Trees: K_{1,1}, K_{1,2}, K_{2,1}, K_{1,3}, K_{3,1}, K_{1,4}, K_{4,1}
  · 4-cycle: K_{2,2}^{(c=1)}, K_{2,2}^{(c=2)}
  · Forced critical: K_{3,2}^{(c=2)}, K_{2,3}^{(c=2)} (S/T swap)
  · Higher chartBase: K_{3,3}^{(c=2)}

V32Betti compatibility theorem: parametric `kerSizeDelta0Direct 3 2 2`
matches `V32Betti.kerSizeDelta0` exactly.

## Open work (full universal parametric closure)

The fully universal `∀ (NS NT c : Nat), 1 ≤ NS → 1 ≤ NT → 1 ≤ c →
kerSizeDelta0 NS NT c = 2` requires either:
  · Induction over graph-walk connectedness for arbitrary (NS, NT, c)
  · A connectedness-lemma library not yet present in 213

This file's `decide`-based representative range covers all G121-relevant
deployments; full universal closure deferred to future sessions.

## Dependency chain

```
CochSpaces
   └── Delta0AndConnectedness (+ V32Betti import for compatibility)
         └── EulerAndCapstone
```

Linear chain.  All under namespace
`E213.Lib.Math.Cohomology.Bipartite.Parametric.*`.

## Cross-references

  · `research-notes/G124_v32betti_parametric_generalization.md` —
    pre-marathon research direction (6-phase plan)
  · `research-notes/G123_geometrization_open_followups.md` §4.5 —
    G124 entry in spin-off marathon table
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V32Betti.lean` —
    K_{3,2}^{(c=2)}-specific predecessor
  · `lean/E213/Lib/Math/GeometrizationConjecture/KChartLensAbstract.lean` —
    abstract axes-partition structure that this parametric machinery
    grounds at the deployment level
