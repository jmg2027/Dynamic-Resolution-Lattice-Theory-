# Session Handoff — 2026-06-08 (Ricci-flow open frontier: discrete curvature → spectrum)

## Branch
`claude/rich-flow-open-frontier-WIA6l` — pushed, 19 commits ahead of `origin/main`.
`cd lean && lake build E213.Lib.Math.Geometry.GeometrizationConjecture` ✓ clean
(199/199).  All new theorems strict ∅-axiom PURE (`tools/scan_axioms.py`):
`BakryEmery` 38/0, `BakryEmeryBipartite` 16/0, `DiscreteLichnerowicz` 12/0,
`OllivierRicci` 74/0.

## What Was Done This Session (a long marathon)

The discrete Bakry–Émery / Ollivier curvature, closed **parametrically across whole
graph families**, then the **curvature → spectrum (Lichnerowicz)** bridge opened.

### 1. Complete graph `K_m` (`BakryEmery.lean` §3)
- Bakry–Émery `CD((m+2)/2, ∞)` (`bochner_complete`/`cd_complete_graph`), **sharp +
  optimal** (`cd_complete_graph_sharp` + `complete_graph_gammaC_witness` ⟹
  `lin_yau_curvature_complete`): `(m+2)/2` is the exact Lin–Yau curvature.
- Ollivier `κ = (m−2)/(m−1) > 0` (`OllivierRicci.lean` §7, `km_ollivier_optimal` +
  `km_plan_optimal`), parametric in `m` (not `decide`).  New δ-sum infra
  (`gridSumZ_delta`/`_zero`/`_weight`, `gridSumZ_const`/`_nonneg`).

### 2. Star `K_{1,b}` (`BakryEmery.lean` §4–§5)
- Centre `CD((3−b)/2, ∞)` (`cd_star`), negative for `b ≥ 4` (`star_negatively_curved`).
- Leaf `CD((5−b)/2, ∞)` (`cd_star_leaf`) — vertex-type-dependent (not vertex-transitive).

### 3. General bipartite `K_{a,b}` — the marathon (`BakryEmeryBipartite.lean`)
Four phases, centred coordinates (translation-invariance kills `c`):
`kab_bochner` (two-shell closed form) → `kab_shell_sos` (complete the square over the
free second shell) → `kab_cd_wide` (`b ≥ 2a−2`, pure SOS) + `kab_cd_narrow`
(`b ≤ 2a−2`, via the discrete `cauchy_schwarz_gridZ`).  `A`-vertex curvature
`min(3a−b, b−a+4)/2`; the DRLT core `K_{3,2}` is `CD(3/2, ∞)` (`kab_K32_pos`).  A
`B`-vertex = same theorems with `(na,nb) ↦ (b−1, a)`.

### 4. Honest cross-frame correction
`K_{3,2}`: Forman `4−3−2 = −1 < 0` (`forman_K32`) vs Bakry–Émery `CD(3/2) > 0` —
**opposite signs on the same graph**.  The earlier essay claim "the frames cannot
disagree" was an over-extension; corrected in
`theory/essays/synthesis/curvature_as_lens_readout.md` (promotion + correction):
the frames cohere on the qualitative `+/0/−` trichotomy, not pointwise.

### 5. Curvature → spectrum / Lichnerowicz (`DiscreteLichnerowicz.lean`, new file)
- `km_lap_sq_sum` (`Σ(Lf)²`), `km_f_lap_sum` (`Σf·Lf`), `km_green`
  (`Σ Γ = E = −Σf·Lf`) — the **integration-by-parts trio** for `K_m`, explicit.
- `km_rayleigh` (`Σ(Lf)² = m·E`, all `f`): the Rayleigh quotient is identically `m`,
  so the `K_m` Laplacian spectrum is `{0, m}`.
- `km_eigenvalue` (`λ ∈ {0,m}`) + `km_meanzero_eigen` + `km_const_eigen`: spectrum
  `{0¹, m^{m−1}}` fully realized (algebraic connectivity `m`).
- `lichnerowicz_abstract` (`K·(λN) ≤ λ·(λN)`, `λ,N>0` ⟹ `K ≤ λ`) via the new
  `le_of_mul_le_mul_right_pos` (Int positive cancellation — a Meta-layer relocation
  candidate, kept local).  The general mechanism; for `K_m` the chain is end-to-end.

## Lean-friction notes (for the next session)
- `rw [gridSumZ_delta/_const …]` often fails to key-match the lambda from
  `gridSumZ_congr`/lemma instantiation — use **term-mode** `Eq.trans (congr) (lemma)`
  + `exact` (defeq), `show` to align goals.
- `ring_intZ` fails when a side normalizes to the **bare zero polynomial** or has a
  leading `0 −` / trailing `+ 0` / `× 1` — use pure `zero_mul`/`add_neg_cancel`/
  `Int.add_zero`/`Order.zero_sub`/`Order.sub_self_zero`/`mul_one`/`PolyIntM.one_mulZ`.
- congr tactic blocks need a leading `dsimp only` to beta-reduce (but it errors on
  "no progress" — omit when the goal is already reduced).
- Keep `gridSumZ` linearity terms **constant-on-the-left** (`c * f x`, not `f x * c`)
  so `gridSumZ_mul_left` matches.

## Open Frontiers
1. **General-graph integration-by-parts** (`Σ Γ₂ = Σ(Lf)²`, `Σ Γ = E`) for an
   arbitrary finite graph — the one remaining input to feed `lichnerowicz_abstract`
   beyond `K_m`.  Needs an Int cyclic `gridSumZ` + shift-invariance (the `K_m` case is
   degenerate/easy; the cycle/star need the edge structure).  Note: the clean
   `Σ(Lf)²=λE` identity is special to `K_m`'s `{0,λ}` spectrum; other graphs give only
   the Lichnerowicz *inequality*.
2. **Relocate `le_of_mul_le_mul_right_pos` to `Int213.OrderMul`** (Meta) — genuinely
   reusable, deferred to avoid the full-repo rebuild.
3. Smooth general-`n` Perelman `𝓦` stays walled (`ricci_flow_smooth_core.md`).
4. **Promote** the bipartite/spectrum arc to a `theory/math/geometry/` chapter (the
   essay correction is done; a dedicated chapter for the parametric closures + the
   spectral bridge is the next tier-3 step).

## File Map
```
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/BakryEmery.lean          ← K_m + star (38 PURE)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/BakryEmeryBipartite.lean ← K_{a,b} marathon (16 PURE)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/DiscreteLichnerowicz.lean ← curvature→spectrum (12 PURE)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/OllivierRicci.lean        ← +K_m §7 + δ-sum infra
theory/essays/synthesis/curvature_as_lens_readout.md                          ← promoted + corrected
research-notes/frontiers/a6_ricci_core/discrete_ricci_flow_ladder.md           ← all rungs + spectral direction
```
