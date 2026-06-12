# Session Handoff — 2026-06-11 (closing-open-programs + weld structure)

## Branch
`claude/closing-open-programs-0qzj2c` — pushed, in sync with origin; **main
merged in** (33 commits: slot tower / number-systems-weaving). Full forced
`rm -rf .lake/build && lake build E213` clean (383/383); `layer_audit` 0
violations; `kernel_regress` 45/45 0-axiom; touched modules 0 DIRTY.
**READY TO MERGE** (full pre-merge audit passed). Merge to main is the next action.

## What Was Done This Session

### 1. Four "cheap brick" frontier closures (all PURE)
- **Pair-sum Lagrange identity** (`BakryEmeryBipartite` §5.5, 5 PURE): the
  depth-0 closed certificate `n·Σa² − (Σa)² = Σ_{i<j}(a_i−a_j)²`
  (`lagrange_pair_identity`), next to the folded `cauchy_schwarz_gridZ`; one A7
  POSITIVITY (`inequalities_positivity` brick 1).
- **Bracket = separation schedule** (`BracketModulus.bracket_is_sep_schedule`):
  exclusion-depth ⟹ `sep_cauchy`'s `hsep`, schedule `I k = B k + 2`
  (`weld_crossdomain` insight 3).
- **Zolotarev edge 2** (`CasoratianPermSign`, already in Lean): the cyclic-shift
  companion sign through `det_permMatrix` (note was stale; recorded closed).
- **Weld Casoratian flip criterion + ratio descent** — see §2.

### 2. The weld Casoratian: full structural development (`LambertOrder` §10, 64 PURE)
Lifted the subtraction-free ℕ `weld_casoratian` to a complete ℤ spine:
- `weld_casoratian_int`, `weld_flip_criterion`, `weldK_nonneg`,
  `weld_descent_step`, `weld_ratio_descent` (any anchor), `weld_positivity_persists`,
  `weldM_nonneg` — flip criterion + ratio descent (items 1+2).
- **det-floor resolves the margin's near-cancellation**: `weldM_devB`
  (`M_J·devB = s_J − q²Q·R_J`), `weld_cosh_RM` (`(2J+1)c_J = P·R_J + devA·M_J`) —
  the **unimodular transform** `(R,M) ↔ (s, (2J+1)c)` (det `−1` = det-one floor).
- **Three Wronskians** (`weld_rs_wronskian`, `weldM_wronskian`, `weldM_s_wronskian`),
  all `K_J`-proportional, collapsed to ONE master ring identity
  **`weld_bilinear_casoratian`** (every residual cross = `det(coeff)·K_J`);
  `weld_casoratian_bilinear` re-derives `weld_casoratian` with coupling `1`.
- **LowerBase localized** (`weld_lowerbase_reduction`, `..._rs` M-free,
  `weld_lowerbase_of_core`): the cross flips at exactly one step (`J=2i`), so
  LowerBase reduces theorem-backed to a single inequality / to {M-monotonicity, Core}.

### 3. Honest verdict on LowerBase — bridge-equivalent (multi-agent + numerical)
Both residuals (M-monotonicity, Core) bottom out in the **same `(4i+2)!!` flip
value** (`master_diagonal`) the existing `LambertBridge` already supplies:
- **Core** needs the `(4i+2)!!` counting (the flip value `R_{2i+1} ~ (4i+2)!!`).
- **M-monotonicity** ⟺ (via the M·sinh Wronskian) a `(s_{J+1}−s_J)M_J ≤ q²Q·K_J`
  that is *self-equivalent* to antitone — a genuine quantitative induction, not
  yet found (an agent's "provable now" was an over-claim, corrected).
Net: the Casoratian/Wronskian split is a clean M-free **second spine**, not a
counting-free re-closure. `LowerBase` stays closed in `LambertBridge` (proof of
record). (Also corrected an earlier over-claim that framed forward persistence
as a bridge-free certificate — it is vacuous at `R_0 ≤ 0`.)

### 4. Classical identification + 2 essays
- **Lambert/Padé/Bessel**: the convergent arrays `apF`/`bpF` ARE the reversed
  Bessel polynomials (essay `bessel_polynomials_are_the_lambert_convergents.md`);
  `(4i+2)!! = 2^{2i+1}(2i+1)!` is the Padé remainder leading coefficient;
  `minor_all` = Bessel total positivity.
- **The form is forced by two** (essay `the_form_forced_by_two.md`): rank-2
  (coth = ratio of two solutions of `y''=y`) forces the unique alternating form
  `K`, the bilinear collapse, the unimodular `±1`, the det-floor `+1` residue
  unit, and the double-factorial flip — no exterior dialer chooses the shape.

### 5. Merge + process + promotion + cross-domain
Merged main; `/process` (sink rule 0 violations); promoted the §10 development to
`lambert_weld.md` §9 + logged rows 70–72; wrote 4 cross-domain bridges (weld
bilinear Casoratian ↔ main's convolution / NoOrderModP / ζ(3)-Apéry / modular group).

## Current Precision Results (0 free parameters)
Unchanged this session (math-branch work — transcendental tower / weld structure).
See `catalogs/physics-constants.md`; headline rows (1/α_em ppb-class, m_p, m_μ/m_e)
as before.

## Open Problems (Priority Order)
1. **Weld LowerBase — bridge-free M-monotonicity induction**: the cleanest open
   residual. M-monotonicity `M_{2i} ≤ M_0` reduces to itself via the M·sinh
   Wronskian; a genuine quantitative ℤ-native induction would leave **Core** as
   the only bridge-dependent piece. Frontier note:
   `research-notes/frontiers/transcendentals/weld_casoratian_development.md`.
2. **General CF-weld bilinear instantiation** for `exp(2/q)` / `tan(1/q)`: the
   abstract `weld_bilinear_casoratian` applies with coupling = the CF determinant
   (coth `1`, exp(2/q) Möbius fold `2·a_n`); needs their normalized pairs built.
   Frontier note: same `weld_casoratian_development.md`.
3. **ζ(3) formalization** — two verified blueprints; the weld's subtraction-free
   weight-threading (`cfpos_moved`/`master_pair`) is the right tool for the Apéry
   integrality divisibility chains (cross-domain bridge 3). Frontier notes:
   `frontiers/zeta3_blueprint.md`, `zeta3_free_modulus.md`.
4. **exp(p/q), p ≥ 2, free modulus** — needs unconditional `hmeas`.
   `frontiers/modulus_degree_ladder.md`.
5. **inequalities = POSITIVITY ∘ LOOP** — brick 1 (Lagrange) closed; the general
   compilation theorem open. `frontiers/inequalities_positivity_fold_crossdomain.md`.
6. **Smooth Ricci core** — the standing wall (discrete side closed/promoted).
   `frontiers/ricci_flow_smooth_core.md`.

## Unresolved from This Session
- A bridge-free quantitative induction for M-monotonicity (and Core) was not
  found — multiple independent reductions (M-Casoratian, R-sinh Wronskian, scalar
  R-recursion) all terminate at the `(4i+2)!!` flip-timing (bridge-equivalent).
- Crude bounds on the LowerBase single inequality fail by 10⁹–10²⁵× (the margin
  `M_0 = P − q²Q` is a det-floor near-cancellation) — the delicate content is
  irreducible.

## Next
Either (1) attempt the M-monotonicity bridge-free induction (frontier 1), or
(2) start the ζ(3) Apéry-integrality marathon using the weld's weight-threading
technique (frontier 3 / cross-domain bridge), or (3) merge this branch to main
and pick a fresh frontier.

## Three-tier state
- **Promotions this session**: `theory/math/analysis/lambert_weld.md` §9 ←
  the closed `LambertOrder` §10 Casoratian development (log row 71); essays
  `bessel_polynomials_are_the_lambert_convergents.md` (row 70),
  `the_form_forced_by_two.md` (row 72).
- **Promotion candidates**: none flagged new — the weld chapter now reflects §10;
  the frontier stays open for the residuals.
- **Active scratchpad**: `frontiers/transcendentals/weld_casoratian_development.md`
  (the structural unification + the two open residuals);
  `frontiers/weld_crossdomain.md` (the 4-bridge addendum).

## File Map
```
lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/LambertOrder.lean  ← §10: full Casoratian spine (64 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/BracketModulus.lean       ← bracket_is_sep_schedule (PURE)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/BakryEmeryBipartite.lean ← §5.5 Lagrange identity (5 PURE)
theory/math/analysis/lambert_weld.md                               ← NEW §9 (Casoratian development promotion)
theory/essays/analysis/bessel_polynomials_are_the_lambert_convergents.md ← NEW essay
theory/essays/analysis/the_form_forced_by_two.md                   ← NEW essay
theory/essays/INDEX.md, research-notes/promotion_essay_log.md      ← registrations (essays 93; rows 70–72)
research-notes/frontiers/transcendentals/weld_casoratian_development.md ← structural unification + open residuals
research-notes/frontiers/weld_crossdomain.md                       ← 4 cross-domain bridges (merge addendum)
```
