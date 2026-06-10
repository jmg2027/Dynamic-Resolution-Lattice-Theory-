# Session Handoff — 2026-06-10 (Ricci-flow frontier: discrete curvature → spectrum → smooth Perelman tensor calculus)

## Branch & build state
`claude/rich-flow-open-frontier-WIA6l` — pushed, ~32 commits ahead of `origin/main`.
**Full `cd lean && lake build E213` ✓ clean (307/307)** — no downstream breakage.
All session modules strict ∅-axiom PURE (`tools/scan_axioms.py`): `OllivierRicci` 74/0,
`BakryEmery` 42/0, `BakryEmeryBipartite` 16/0, `DiscreteLichnerowicz` 12/0,
`ConformalCurvature` 18/0, `TensorCalculus` 23/0.

## What was done (a very long marathon — three arcs)

### Arc 1 — discrete curvature, parametric across all graph families
- **Complete graph `K_m`**: Bakry–Émery `CD((m+2)/2,∞)` sharp/optimal (`BakryEmery` §3);
  Ollivier `κ=(m−2)/(m−1)` (`OllivierRicci` §7).
- **Star `K_{1,b}`**: centre `CD((3−b)/2,∞)`, leaf `CD((5−b)/2,∞)` (`BakryEmery` §4–§5).
- **General bipartite `K_{a,b}`** (`BakryEmeryBipartite.lean`): 4-phase marathon →
  `A`-vertex curvature `min(3a−b,b−a+4)/2`; DRLT core `K_{3,2} = CD(3/2)`.
- Honest cross-frame correction: `K_{3,2}` Forman `−1` vs Bakry–Émery `+3/2` — corrected the
  "frames cannot disagree" overclaim in `theory/essays/synthesis/curvature_as_lens_readout.md`.

### Arc 2 — curvature → spectrum (Lichnerowicz) (`DiscreteLichnerowicz.lean`)
- `km_rayleigh` (`Σ(Lf)² = m·E`), `km_eigenvalue` + eigenspaces ⟹ `K_m` Laplacian spectrum
  `{0¹, m^{m−1}}`; `km_green` (integration-by-parts trio explicit); `lichnerowicz_abstract`
  (`K ≤ λ`) via the new `le_of_mul_le_mul_right_pos` (Int positive cancellation).

### Arc 3 — the smooth Perelman wall, attacked along the reachable routes
- **Conformal (general `n`)** (`ConformalCurvature.lean` §S6–§S7): `confRNumN` (general-`n`
  conformally-flat **scalar** curvature, validated `= 4·confKNum` at `n=2`, `n=3` trichotomy);
  the conformally-flat **Ricci tensor** `confRic*` + trace consistency + Einstein-at-a-point.
- **General-metric algebraic tensor calculus** (`Geometry/TensorCalculus.lean`, dimension-free):
  Christoffel 1st kind (symmetry, metric compatibility) → 2nd kind + raising/lowering (the
  inverse layer) → Riemann tensor (+ **all four** symmetries via the metric 2-jet `riemLow`) →
  Ricci contraction + first Bianchi → scalar `R=g^{ij}Ric` + Einstein `R=λn`.
- **Panel + consensus brick**: a 4-mathematician-agent panel explored the residual wall; built
  `perelman_rate_nonneg` (`TensorCalculus` §7): `0 ≤ Σ_{i,j}(Ric_{ij}+∇_i∇_j f)²` — the
  algebraic form of Perelman's `d/dt 𝓕 ≥ 0` (the SOS rate), reachable now because `Ric` exists.

## Architect's assessment & the org-debt (FLAG for an org-audit, not yet fixed)
The branch is internally coherent (full build PURE).  Deferred organizational debt:
1. **`gridSumZ` placement** — it lives in `OllivierRicci.lean` (a leaf) but is now imported by
   `BakryEmeryBipartite`, `DiscreteLichnerowicz`, `TensorCalculus` (shared-infra-in-leaf smell).
   A clean fix relocates `gridSumZ` + its `~15` lemmas to a shared infra module; risky refactor
   (touches `OllivierRicci`'s 74 theorems), so deferred to a focused `/org-audit`.
2. **`le_of_mul_le_mul_right_pos`** (`DiscreteLichnerowicz`) — a general `Int` fact, a
   `Int213.OrderMul` (Meta) relocation candidate; kept local to avoid a full rebuild.
3. **`kab_inner`** reused cross-file (`DiscreteLichnerowicz` imports `BakryEmeryBipartite`).
4. **`Real213/Core/Functions.lean`** still has `exp/sin/cosCut := fun _ _ => true` stubs while
   the real rate machinery is in `ExpLog/` — a packaging gap (see panel brick below).

## Lean-tooling notes (recurring, for the next session)
- `ring_intZ` **cannot certify a zero-polynomial `= 0`** goal — use pure
  `sub_add_cancel_int`/`sub_self_zero`/`add_neg_cancel`/`zero_mul`/`mul_one`, or state the
  identity in moved-over (non-zero RHS) form (`riemLow_bianchi1`).
- `omega` is **barred** (leaks `propext`+`Quot.sound`).
- `rw [gridSumZ_* ]` often fails to key-match lambdas from `gridSumZ_congr` — use term-mode
  `Eq.trans (congr) (lemma)` + `exact`; keep `gridSumZ_mul_left` constants **on the left**.
- congr tactic blocks need a leading `dsimp only` to beta-reduce (omit if already reduced).

## Open frontiers — the panel's reachable next bricks (all recorded in the notes)
The smooth-Perelman **algebraic** core is now ∅-axiom; the residual wall is pure **analysis**.
Per the 4-agent panel (`ricci_flow_smooth_core.md` "Panel exploration" section):
1. **`expCauchySeq (x) : CauchyCutSeq`** — package the (already-PURE) `exp`/`sin`/`cos` series
   rate certificates (`Real213/ExpLog/CutExpModulus`, `CutTrigModulus`) into a `CauchyCutSeq`
   (template: `eulerCauchySeq`), retiring the `Functions.lean` stubs.  "Transcendental metrics"
   is a packaging stub, NOT the century problem.
2. **`Real213`-cut maximum principle** — promote the discrete `heatIter_range` to a `Real213`
   `cutLe` via the `RealCauchyWitness` order-squeeze idiom (~40 lines, a solved pattern).
3. **Discrete χ²-entropy descent** — `Ent(μ)=Σ μ(μ−1)` monotone under `lazyHeatStep`
   (same shape as `ricci_energy_monotone`) — the synthetic discrete Perelman-entropy.
The GENUINE un-reframable wall: weighted integration-by-parts (`∇𝓕 ↔ flow`), the `𝓦` Gaussian,
Li–Yau Harnack (nonlinear, needs `Real213` division), κ-solution/surgery classification +
no-local-collapsing compactness.

## Recommendation (leading architect)
This branch is **merge-ready** (full PURE build, internally coherent, frontier notes + one
essay promotion + correction all in place).  Highest-value next moves, in order: (a) **merge to
`main`** so this large body of work is integrated and reviewable; (b) a **`/org-audit`** to pay
down the `gridSumZ`/Meta-candidate placement debt; (c) THEN the panel's reachable bricks
(2 — the `Real213`-cut maximum principle — is the most surgical, high-confidence frontier-closer).

## File map (new this session)
```
lean/E213/Lib/Math/Geometry/TensorCalculus.lean            ← general-n tensor calculus + Perelman SOS
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/BakryEmeryBipartite.lean  ← K_{a,b}
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/DiscreteLichnerowicz.lean ← curvature→spectrum
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/{BakryEmery,OllivierRicci,ConformalCurvature}.lean ← extended
research-notes/frontiers/ricci_flow_smooth_core.md         ← smooth-core attack + panel findings
research-notes/frontiers/a6_ricci_core/discrete_ricci_flow_ladder.md  ← all rungs + spectral
theory/essays/synthesis/curvature_as_lens_readout.md       ← promoted + overclaim corrected
```
