# Session Handoff — 2026-06-10 (Ricci-flow frontier: discrete curvature → spectrum → smooth Perelman tensor calculus)

## Branch & build state
`claude/rich-flow-open-frontier-WIA6l` — `origin/main` merged in (the primitive-root /
full-Zolotarev marathon).  **Fresh `rm -rf .lake/build && lake build` ✓ clean.**  Kernel
regression 45/45 0-axiom; `audit_axioms.py` all ✓.  All session modules strict ∅-axiom PURE
(`tools/scan_axioms.py`): `OllivierRicci` 60/0, `BakryEmery` 42/0, `BakryEmeryBipartite` 16/0,
`DiscreteLichnerowicz` 11/0, `ConformalCurvature` 18/0, `TensorCalculus` 23/0,
`IntGridSum` 14/0, `OrderMul` 10/0.

## What was done (three math arcs + a closing skills marathon)

### Arc 1 — discrete curvature, parametric across all graph families
- **Complete graph `K_m`**: Bakry–Émery `CD((m+2)/2,∞)` sharp/optimal (`BakryEmery` §3);
  Ollivier `κ=(m−2)/(m−1)` (`OllivierRicci` §7).
- **Star `K_{1,b}`**: centre `CD((3−b)/2,∞)`, leaf `CD((5−b)/2,∞)` (`BakryEmery` §4–§5).
- **General bipartite `K_{a,b}`** (`BakryEmeryBipartite.lean`): `A`-vertex curvature
  `min(3a−b,b−a+4)/2`, split into the wide regime `b ≥ 2a−2` (`kab_cd_wide`, SOS only) and the
  narrow regime `b < 2a−2` (`kab_cd_narrow`, discrete Cauchy–Schwarz); DRLT core `K_{3,2} = CD(3/2)`.
- Honest cross-frame correction: `K_{3,2}` Forman `−1` vs Bakry–Émery `+3/2` — corrected the
  "frames cannot disagree" overclaim in `theory/essays/synthesis/curvature_as_lens_readout.md`.

### Arc 2 — curvature → spectrum (Lichnerowicz) (`DiscreteLichnerowicz.lean`)
- `km_rayleigh` (`Σ(Lf)² = m·E`), `km_eigenvalue` + eigenspaces ⟹ `K_m` Laplacian spectrum
  `{0¹, m^{m−1}}`; `km_green` (integration-by-parts trio explicit); `lichnerowicz_abstract`
  (`K ≤ λ`) via `OrderMul.le_of_mul_le_mul_right_pos` (Int positive cancellation).

### Arc 3 — the smooth Perelman wall, attacked along the reachable routes
- **Conformal (general `n`)** (`ConformalCurvature.lean` §S6–§S7): `confRNumN` (general-`n`
  conformally-flat **scalar** curvature, validated `= 4·confKNum` at `n=2`, `n=3` trichotomy);
  the conformally-flat **Ricci tensor** `confRic*` + trace consistency + Einstein-at-a-point.
- **General-metric algebraic tensor calculus** (`Geometry/TensorCalculus.lean`, dimension-free):
  Christoffel 1st kind (symmetry, metric compatibility) → 2nd kind + raising/lowering → Riemann
  tensor (+ **all four** symmetries via the metric 2-jet `riemLow`) → Ricci contraction + first
  Bianchi → scalar `R=g^{ij}Ric` + Einstein `R=λn`.  Promoted to
  `theory/math/geometry/riemannian_curvature_tensor.md`.
- **Panel consensus brick**: `perelman_rate_nonneg` (`TensorCalculus` §7),
  `0 ≤ Σ_{i,j}(Ric_{ij}+∇_i∇_j f)²` — the algebraic form of Perelman's `d/dt 𝓕 ≥ 0` (the SOS
  rate), reachable now that `Ric` exists.

### Closing skills marathon (process → promote → crossdomain → essay → org-audit → purity → merge)
- **/process**: sink-rule clean (no permanent tier cites a research-notes note-file).
- **Promotions**: `theory/math/geometry/riemannian_curvature_tensor.md` (the tensor calculus).
- **Cross-domain**: `research-notes/frontiers/curvature_spectrum_crossdomain.md` — the `K_p`
  Laplacian eigenbasis (additive characters of ℤ/p) dual to main's multiplicative Legendre
  character; one cyclic group, two character-faces, both eigen-data.
- **/essay**: `theory/essays/synthesis/the_character_is_the_groups_eigen_data.md`.
- **/org-audit**: relocated `gridSumZ` + its 14-lemma toolkit out of the `OllivierRicci` leaf
  into `Lib/Math/Combinatorics/IntGridSum` (domain-agnostic infra; 5 consumers repointed);
  relocated `le_of_mul_le_mul_right_pos` into `Meta/Int213/OrderMul` next to its forward form.
- **/purity-check + /ready-to-merge**: 0 sorry / 0 axiom / 0 native_decide / 0 Classical / 0
  Mathlib / 0 omega; layer audit 0 violations; flagship theorems `#print axioms` = "does not
  depend on any axioms".  **Verdict: READY TO MERGE.**

## Lean-tooling notes (recurring, for the next session)
- `ring_intZ` **cannot certify a zero-polynomial `= 0`** goal — use pure
  `sub_add_cancel_int`/`sub_self_zero`/`add_neg_cancel`/`zero_mul`/`mul_one`, or state the
  identity in moved-over (non-zero RHS) form (`riemLow_bianchi1`).
- `omega` is **barred** (leaks `propext`+`Quot.sound`).
- `rw [gridSumZ_* ]` often fails to key-match lambdas from `gridSumZ_congr` — use term-mode
  `Eq.trans (congr) (lemma)` + `exact`; keep `gridSumZ_mul_left` constants **on the left**.
- congr tactic blocks need a leading `dsimp only` to beta-reduce (omit if already reduced).
- The `gridSumZ` toolkit now lives at `E213.Lib.Math.Combinatorics.IntGridSum` — `import` + `open`
  it (not `OllivierRicci`) for any new finite-Int-sum work.

## Open Problems (priority order)
### 1. `Real213`-cut maximum principle (most surgical)
Promote the discrete `heatIter_range` to a `Real213` `cutLe` via the `RealCauchyWitness`
order-squeeze idiom (~40 lines, a solved pattern).  High-confidence frontier-closer.
Frontier note: `research-notes/frontiers/ricci_flow_smooth_core.md` (Panel exploration §, brick 2).

### 2. `expCauchySeq (x) : CauchyCutSeq` — retire the transcendental-metric stub
Package the already-PURE `exp`/`sin`/`cos` series rate certificates (`Real213/ExpLog/CutExpModulus`,
`CutTrigModulus`) into a `CauchyCutSeq` (template: `eulerCauchySeq`), retiring the
`Real213/Core/Functions.lean` `:= fun _ _ => true` stubs.  "Transcendental metrics" is a packaging
stub, not the century problem.
Frontier note: `research-notes/frontiers/ricci_flow_smooth_core.md` (brick 1).

### 3. Discrete χ²-entropy descent
`Ent(μ)=Σ μ(μ−1)` monotone under `lazyHeatStep` (same shape as `ricci_energy_monotone`) — the
synthetic discrete Perelman-entropy.
Frontier note: `research-notes/frontiers/ricci_flow_smooth_core.md` (brick 3).

### 4. The genuine un-reframable analysis wall
Weighted integration-by-parts (`∇𝓕 ↔ flow`), the `𝓦` Gaussian, Li–Yau Harnack (nonlinear, needs
`Real213` division), κ-solution/surgery classification + no-local-collapsing compactness.
Frontier notes: `research-notes/frontiers/ricci_flow_smooth_core.md` +
`research-notes/frontiers/a6_ricci_core/discrete_ricci_flow_ladder.md`.

## Unresolved from this session
None attempted-and-failed.  The smooth-Perelman **algebraic** core is ∅-axiom; what remains
(Open Problem 4) is pure analysis, recorded as frontiers, not dead ends.

## Next
After the merge to `main`: Open Problem 1 (`Real213`-cut maximum principle) — the most surgical
high-confidence brick, then the entropy descent (3).

## Three-tier state
- **Promotions this session**: `theory/math/geometry/riemannian_curvature_tensor.md` ← the
  Geometry/TensorCalculus closure.  Essay:
  `theory/essays/synthesis/the_character_is_the_groups_eigen_data.md`.
- **Promotion candidates**: the discrete-curvature `GeometrizationConjecture/` sub-tree
  (Ollivier/BakryEmery/Bipartite/Lichnerowicz) is PURE-closed; a consolidated `theory/` chapter
  mirroring it is a candidate (check `theory/PROMOTION_CRITERIA.md` H1–H4 + S1–S3).
- **Active scratchpad**: `research-notes/frontiers/ricci_flow_smooth_core.md`,
  `.../a6_ricci_core/discrete_ricci_flow_ladder.md`, `.../curvature_spectrum_crossdomain.md`.

## File map
```
lean/E213/Lib/Math/Combinatorics/IntGridSum.lean           ← NEW: gridSumZ + 14-lemma Int-sum toolkit (relocated infra)
lean/E213/Lib/Math/Geometry/TensorCalculus.lean            ← general-n tensor calculus + Perelman SOS
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/BakryEmeryBipartite.lean  ← K_{a,b} (wide/narrow split)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/DiscreteLichnerowicz.lean ← curvature→spectrum
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/{BakryEmery,OllivierRicci,ConformalCurvature}.lean ← extended
lean/E213/Meta/Int213/OrderMul.lean                        ← +le_of_mul_le_mul_right_pos (relocated Int order lemma)
theory/math/geometry/riemannian_curvature_tensor.md        ← NEW: tensor-calculus chapter (promotion)
theory/essays/synthesis/the_character_is_the_groups_eigen_data.md  ← NEW: character-as-eigen-data essay
research-notes/frontiers/curvature_spectrum_crossdomain.md ← NEW: additive/multiplicative character cross-domain
research-notes/frontiers/ricci_flow_smooth_core.md         ← smooth-core attack + panel findings
research-notes/frontiers/a6_ricci_core/discrete_ricci_flow_ladder.md  ← all rungs + spectral
theory/essays/synthesis/curvature_as_lens_readout.md       ← promoted + overclaim corrected
```
