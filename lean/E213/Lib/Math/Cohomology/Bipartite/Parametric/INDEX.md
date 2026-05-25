# Bipartite/Parametric — sub-tree INDEX

Parametric (NS, NT, c)-generalization of the K_{3,2}^{(c=2)}-specific
V32 / V32Betti cohomology infrastructure (b_0 / b_1 / Euler) and the
K_{3,3}^{(c)}-specific V33EnrichedParametric enriched-2-complex
infrastructure (codim ≥ c via per-layer ψ-functionals).

**Status**: 5 files, ~106 PURE.

## File map

| File | Phase | PURE | Content |
|---|---|---|---|
| `CochSpaces.lean` | 1 | 13 | Parametric `CochV NS NT` / `CochE NS NT c` types + `srcOf` / `tgtOf` / `multOf` endpoint extractors + `srcFin` / `tgtFin` packaged + `delta0` parametric coboundary + K_{3,2}^{(c=2)} numerical sanity checks |
| `Delta0AndConnectedness.lean` | 2-3 | 16 | `cochVAt` binary-decoded cochains + `isInKerDelta0Direct` test + `kerSizeDelta0Direct` enumeration count + `b_0 = 1` (ker size = 2) verified across all G121-relevant deployments via `decide` (K_{1,1}, K_{1,2}, K_{1,3}, K_{2,2}, K_{1,4}, K_{3,2}^{(c=2)}, K_{3,3}^{(c=2)}, ...) + V32Betti compatibility |
| `EulerAndCapstone.lean` | 4-6 | 7 | `eulerChar : Int` parametric formula + `b1Formula : Nat` for connected case + chartBase-≤-5 deployment-family b_1 table + `chartVisibleAxes` bridge to KChartLens + ★★★★★★ `parametric_close_capstone` |
| `EnrichedKNSNTc.lean` | — | 63 | `(NS, NT, c)`-parametric enriched-2-complex framework + abstract Q-decomposition kill + concrete instances at every parity-OK pair.  Adds `qT_param_zero_NT5` (mirror of `qS_param_zero_NS5`) + `kills_delta1_KNS5` family + K_{4,5} and K_{5,5} closures. |
| `EnrichedKNSNTcEvenEven.lean` | — | 7 | Parity-failing closure via **vertex-excluding ψ**.  For both NS, NT even, the uniform `psi_layer_param` fails (each edge appears (NS-1)(NT-1) = odd times).  `ψ_excl_S0_K44 m v := ⊕_{s ∈ {3,4,5}} ⊕_t v s t m` restricts the s-fold to S-pairs NOT containing vertex 0; each remaining S-vertex now appears NS-2 = 2 (even) times.  Kill via existing `foldXor_t_face_eq_qT_decomposition` + 3-bool case-bash on `qT 1, qT 2, qT 3`.  Signature via repositioned `e_face_layer_K44` at `(s=3, t=0)` (pair {1,2} doesn't contain 0).  Capstone `K44_c_independent_h2_classes` |  **Framework core (25):** `foldXor` Fin-XOR fold + `PairEnum n` + `chooseTwo` (`abbrev`) + `EnrichedEdgeCoch` / `EnrichedFaceVal` + `face_boundary_param` / `delta1_enr_param` + `psi_layer_param` (double foldXor) + `e_face_layer_param` + `psi_layer_signature_param` (Kronecker δ) + `KillsDelta1` hypothesis + `parametric_c_independent_h2_classes_param` capstone + `pairEnum3` + K_{3,3} kill via 9-edge case-bash + `K33_c_independent_h2_classes_via_framework`. **Abstract Q-decomposition kill (15):** `foldXor_xor_distribute` (linearity) + `qT_param` (row Q) / `qS_param` (column Q) + `foldXor_swap` (fold commutativity) + `foldXor_t_face_eq_qT_decomposition` / `foldXor_s_face_eq_qS_decomposition` (per-face factoring) + `psi_layer_kill_of_qT_zero` / `psi_layer_kill_of_qS_zero` (abstract kill under Q ≡ 0) + concrete `qT_param_zero_NT3` (NT=3 ⇒ qT=0) / `qS_param_zero_NS3` (NS=3) / `qS_param_zero_NS5` (NS=5) + family kills `kills_delta1_KNS3` / `kills_delta1_K3NT` / `kills_delta1_K5NT`.  **Concrete instances (16):** `pairEnum4` (6 pairs lex order) + `pairEnum5` (10 pairs lex order) + `kills_delta1_K43` / `K43_c_independent_h2_classes_via_framework` + `kills_delta1_K53` / `K53_c_independent_h2_classes_via_framework` + `kills_delta1_K54` / `K54_c_independent_h2_classes_via_framework` + `kills_delta1_K34` / `K34_c_independent_h2_classes_via_framework` + `kills_delta1_K35` / `K35_c_independent_h2_classes_via_framework`.  Covers every (NS, NT) where NS ∈ {3, 5} or NT ∈ {3} (NS, NT ∈ {3, 4, 5} with at least one in {3, 5}) — the full original followup list (3,3), (4,3), (5,3), (5,4) plus bonus (3,4), (3,5) |

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
