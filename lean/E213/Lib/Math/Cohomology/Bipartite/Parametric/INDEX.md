# Bipartite/Parametric — sub-tree INDEX

Parametric (NS, NT, c)-generalization of the K_{3,2}^{(c=2)}-specific
V32 / V32Betti cohomology infrastructure (b_0 / b_1 / Euler) and the
K_{3,3}^{(c)}-specific V33EnrichedParametric enriched-2-complex
infrastructure (codim ≥ c via per-layer ψ-functionals).

**Status**: 6 files, ~152 PURE.  Direction A **CLOSED** via the
8-family master coverage (`min(NS, NT) ∈ {3, 4, 5, 6}`) +
`EnrichedKNSNTcMaster.master_Knn_c_counter_resolved` (K_{n,n} for
n ∈ {3, 4, 5, 6}, both parity regimes uniformly).

## File map

| File | Phase | PURE | Content |
|---|---|---|---|
| `CochSpaces.lean` | 1 | 13 | Parametric `CochV NS NT` / `CochE NS NT c` types + `srcOf` / `tgtOf` / `multOf` endpoint extractors + `srcFin` / `tgtFin` packaged + `delta0` parametric coboundary + K_{3,2}^{(c=2)} numerical sanity checks |
| `Delta0AndConnectedness.lean` | 2-3 | 16 | `cochVAt` binary-decoded cochains + `isInKerDelta0Direct` test + `kerSizeDelta0Direct` enumeration count + `b_0 = 1` (ker size = 2) verified across all G121-relevant deployments via `decide` (K_{1,1}, K_{1,2}, K_{1,3}, K_{2,2}, K_{1,4}, K_{3,2}^{(c=2)}, K_{3,3}^{(c=2)}, ...) + V32Betti compatibility |
| `EulerAndCapstone.lean` | 4-6 | 7 | `eulerChar : Int` parametric formula + `b1Formula : Nat` for connected case + chartBase-≤-5 deployment-family b_1 table + `chartVisibleAxes` bridge to KChartLens + ★★★★★★ `parametric_close_capstone` |
| `EnrichedKNSNTc.lean` | — | 63 | `(NS, NT, c)`-parametric enriched-2-complex framework + abstract Q-decomposition kill + concrete instances at every parity-OK pair.  Adds `qT_param_zero_NT5` (mirror of `qS_param_zero_NS5`) + `kills_delta1_KNS5` family + K_{4,5} and K_{5,5} closures. |
| `EnrichedKNSNTcEvenEven.lean` | — | 41 | Parity-failing closures via **vertex-excluding ψ** (both S- and T-side dual families).  Six families: `psi_excl_S0_NS{4,6}` for K_{4, NT} / K_{6, NT}; `psi_excl_T0_NT{4,6}` for K_{NS, 4} / K_{NS, 6}.  Plus concrete K_{4,4}, K_{6,4}, K_{4,6}, K_{6,6} capstones |
| `EnrichedKNSNTcMaster.lean` | — | 5 | **Master closure capstone** combining all eight closure families.  Six-route directory (§2 table: NS or NT ∈ {3, 4, 5, 6} ⇒ family selection).  `CClosure NS NT c pS pT` structure for uniform packaging.  `master_K33`, `master_K44`, `master_K55`, `master_K66` — K_{n,n} witnesses for n = 3, 4, 5, 6.  ★ `master_Knn_c_counter_resolved` — single statement bundling all four K_{n,n} signatures, spanning both parity-OK (n odd) and parity-failing (n even) regimes |

## Coverage

All K-deployments enumerated in `research-notes/G121_dim4_self_pointing_axis.md`
and `research-notes/archive/G128_geometrization_open_followups.md` are PURE-verified:
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

  · `theory/math/cohomology/bipartite.md` "Parametric V32Betti"
    section — chapter narrative for this sub-tree
  · `research-notes/archive/G129_v32betti_parametric_generalization.md`
    — 6-phase plan + partial-close summary (deep-dive)
  · `research-notes/archive/G128_geometrization_open_followups.md` §4.5 —
    V32Betti entry in spin-off marathon table
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V32Betti.lean` —
    K_{3,2}^{(c=2)}-specific predecessor
  · `lean/E213/Lib/Math/GeometrizationConjecture/KChartLensAbstract.lean` —
    abstract axes-partition structure that this parametric machinery
    grounds at the deployment level
