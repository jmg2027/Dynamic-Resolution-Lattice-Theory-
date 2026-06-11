# Session Handoff — 2026-06-11 (closing-open-programs)

## Branch
`claude/closing-open-programs-0qzj2c` — cheap-brick sweep across the open
frontier board.  Full `lake build E213` green; touched modules 0 DIRTY.

## What Was Done This Session — four "cheap brick" frontier closures

### 1. Pair-sum Lagrange identity (`inequalities_positivity` #1) — CLOSED
`BakryEmeryBipartite` §5.5 (5 PURE): the depth-0 closed certificate of the
Cauchy–Schwarz gap, next to the folded `cauchy_schwarz_gridZ`.
- `lagrangePairSumZ` — triangular `Σ_{j<n}Σ_{i<j}(a_i−a_j)²`
- `lagrange_pair_identity` — `n·Σa² − (Σa)² = lagrangePairSumZ`
- `cauchy_schwarz_via_lagrange` (re-derive the bound), `lagrange_pair_two`
  (`n=2` collapse to `(a₀−a₁)²`, ties to `Foundations.Positivity.cauchy_schwarz_2d`)
The folded per-rung and depth-0 certificates proved equal — one A7 POSITIVITY.

### 2. Weld Casoratian flip criterion (`weld_casoratian_development` #1) — CLOSED
`LambertOrder` §10 (5 PURE): lift the subtraction-free ℕ `weld_casoratian`
to the named ℤ recurrence.
- `weldR/weldM/weldK` — lower cross `R_J`, upper margin `M_J`, constant `K_J`
  as signed ℤ quantities
- `weld_casoratian_int : R_{J+1}·M_J = R_J·M_{J+1} + K_J` — difference factors
  as `K_J·(detpair−detval)`; one det-one floor firing (`dev_cross_det` cast to
  ℤ) kills it
- `weld_flip_criterion : 0 < M_J → −(R_J·M_{J+1}) < K_J → 0 < R_{J+1}`
Added `import E213.Meta.Int213.OrderMul` (brings `ring_intZ` + order API).

### 3. Bracket engine = separation schedule (`weld_crossdomain` insight 3) — CLOSED
`BracketModulus.bracket_is_sep_schedule` (PURE): the two-sided exclusion-depth
hypotheses imply `AbCutSeq.sep_cauchy`'s one-sided `hsep` for the lower fold,
with schedule `I k = B k + 2`.  Forward (`below_fwd`) + backward (post-exit
constancy) regimes meet at `B k + 2`.  Ladder rung-2 bracket and weld
completion engine are one device.

### 4. Zolotarev "three readouts" edge 2 (`zolotarev_crossdomain`) — already in Lean
`CasoratianPermSign.{det_permMatrix_cycShift, companion_det_eq_permMatrix_det}`
(4 PURE) already route the cyclic-shift companion sign through `det_permMatrix`.
Frontier note was stale; recorded as closed (doc-only).

## Lean tactic intel (this session's pitfalls)
- **`ring_intZ` reads `↑(J+1)` and `↑J` as unrelated atoms** — a coefficient
  identity like `2(J+1)+1 = 2J+3` is invisible.  Bridge with
  `have hsucc : ((J+1:Nat):Int) = (J:Int)+1 := rfl; rw [hsucc]` before `ring_intZ`
  (one `rw` replaces all occurrences — `hsucc` has no metavariable).
- **`ring_intZ` does not normalize `·0` / `0+` forms** (same as `ring_nat`,
  per prior HANDOFF).  Route around: collapse `detval−detval` with
  `Order.sub_self_zero` + `PolyIntM.mul_zeroZ`, and rearrange `A−(B+C)=0 ⟹ A=B+C`
  with `int_eq_of_add_neg` + `Int.add_zero`, not `ring_intZ`.
- Cast a ℕ identity to ℤ via `congrArg Int.ofNat h` then `rw [Int.ofNat_mul,
  Int.ofNat_add, Int.ofNat_one]`; `Int.ofNat.inj` for the reverse.  For a ℕ
  *inequality* use `OrderMul.ofNat_le_of_le`; bridge `↑(2*J+c)` to `2*↑J+c`
  with a per-literal `have ... := by rw [Int.ofNat_add, Int.ofNat_mul]; rfl`.
- **`calc` with mixed `=`/`≤` steps pulls in `propext`** (its `Trans`
  instances) → the theorem scans DIRTY.  Replace with explicit
  `Order.le_trans` + goal `rw [show … from by ring_intZ]` + `le_refl` to stay
  ∅-axiom.  (`induction … with` and `ring_intZ` themselves are clean.)

## Open Problems (unchanged priority; footholds added)
1. **ζ(3) formalization** — two verified blueprints, formalization marathons.
   `frontiers/zeta3_blueprint.md`, `zeta3_free_modulus.md`.
2. **exp(p/q), p ≥ 2, free modulus** — needs unconditional `hmeas`.
   `frontiers/modulus_degree_ladder.md`.
3. **Weld Casoratian** — items 1+2 CLOSED; item 3 **reduced to one inequality +
   wall precisely located** (multi-agent + numerical probe).  Lemmas:
   `weld_casoratian_int`, `weld_flip_criterion`, `weldK_nonneg`, `weld_descent_step`,
   `weld_ratio_descent` [any anchor], `weld_positivity_persists`, `weldM_nonneg`,
   `weld_lowerbase_reduction`.  Discoveries: (i) the cross flips at **exactly one
   step** `J=2i→2i+1` (eval `i≤3`); (ii) so LowerBase reduces *theorem-backed,
   bridge-free* to the **single** inequality `(−R_0)·M_{2i}·M_{2i+1} ≤ K_{2i}·M_0`
   (`weld_lowerbase_reduction`), flip criterion now instantiated; (iii) but that
   inequality is **not crudely provable** — `M_0 = P − q²Q` is a small near-cancellation
   (det-floor `P·devB = q²devA·Q+1` the only gap; crude `M ≤ P·s` overshoots by
   10⁹–10²⁵×), so the residue *inherits* the bridge's delicate content (§5.4: no
   internal handle that avoids it — bridge-equivalence now evidenced, not asserted).
   Also: repo's `R_recursion` (`R_{J+1}=(2J+2)(2J+3)q²R_J+((2J+3)devB−devA)`, M-free)
   already gives the persistence — Casoratian persistence is a re-derivation; the new
   §10 content is the ℤ-Wronskian + flip + reduction (the M-margin second-certificate
   view).  (Corrects an earlier over-claim that framed persistence as a certificate.)
4. **inequalities = POSITIVITY ∘ LOOP** — first brick (Lagrange identity)
   CLOSED; the general compilation theorem over AM-GM/Jensen/power-mean open.
5. **Smooth Ricci core** — the standing wall (discrete side closed/promoted).

## Next
Either continue the cheap-brick sweep (curvature_spectrum bridge 1 `K_p`
Laplacian = additive character; selfref_matrix unimodularity note) or start
the ζ(3) Chebyshev-lcm marathon (Open Problem 1).

## File Map
```
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/BakryEmeryBipartite.lean  ← §5.5 Lagrange identity (5 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/BracketModulus.lean                   ← §3 bracket_is_sep_schedule (PURE)
lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/LambertOrder.lean              ← §10 named ℤ Casoratian + flip (5 PURE); +OrderMul import
research-notes/frontiers/inequalities_positivity_fold_crossdomain.md           ← brick 1 closed
research-notes/frontiers/weld_crossdomain.md                                   ← insight 3 closed
research-notes/frontiers/zolotarev_crossdomain.md                              ← edge 2 closed (was stale)
research-notes/frontiers/transcendentals/weld_casoratian_development.md        ← item 1 closed
research-notes/frontiers/INDEX.md                                              ← four closure records
```
