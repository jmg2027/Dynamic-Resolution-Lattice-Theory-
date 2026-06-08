# Session Handoff — 2026-06-08 (spiral-axis classification: A1/A3/A5 closed; merge marathon)

## Branch
`claude/spiral-axis-classification-ZvaNO` — `origin/main` merged in (87 commits: the CKM CP-phase
marathon, Zolotarev/Legendre, permutation-three-readouts, etc.).  Forced fresh `rm -rf .lake/build
&& lake build` ✓ clean; `layer_audit` 0 violations / 1876 files; `kernel_regress` 45/45 0-axiom;
purity 0 sorry/axiom/native_decide/Classical/Mathlib.  **READY TO MERGE → main** (pending the
session's final push + merge).

## What Was Done This Session

Theme: the **spiral-axis classification** cluster — closing the three ranked open conjectures
(A1/A3/A5 of `research-notes/frontiers/spiral_axis/G185`), then a full merge marathon (merge main →
`/process` → promote → cross-domain note → `/essay` → `/org-audit` → `/purity-check` →
`/ready-to-merge`).

### 1. Spiral-axis A3 — the all-orders Casoratian determinant law (15 PURE ✓)
`lean/E213/Lib/Math/Analysis/Cauchy/CasoratianDeterminant.lean`.  `casoratian_det_step`: for any
constant-coefficient order-`(K+1)` recurrence `s(m+K+1)=Σ_{l≤K} a l·s(m+l)`, the `(K+1)×(K+1)`
Hankel (Casoratian) determinant multiplies by the companion determinant `altSign K · a 0` each step
(`casoratian_det_closed` = the `qⁿ` form).  Structural proof — `H(n+1) = C·H(n)`
(`hankel_shift_eq_matMul`) + `DetMul.det_matMul` + `det_companion` — no `ring_intZ` expansion (the
order-4 normal form exceeds the kernel).  Subsumes order 2 (`CassiniUnimodular.det_step`) and order
3 (`SecondCasoratian.second_casoratian`); `second/third/fourth_order_multiplier` are the instances.
Supporting infra: `Linalg213/DetN.det_congr_lt` (det depends only on rows `< n`).

### 2. Spiral-axis A5 — CD-tower / axis non-coincidence (3 PURE ✓)
`Tower/SpiralAxisCrystallographic.cd_tower_axis_noncoincidence` + `not_pow_two_six`.  The CD
dimension tower `{1,2,4,8}=2ⁿ` is not the spiral axis `{2,4,6}` — they meet only on `{2,4}` and
diverge because `8=2³` is a power of two but not crystallographic (`φ 8 = 4 > 2`, axis ⊆
crystallographic) and `6` is crystallographic (`φ 6 = 2`) but no power of two.  Stated via the
structural reasons (not `List.Mem`, which leaks propext/Quot.sound under `decide`).

### 3. A1 was already closed
`Mat2CayleyHamilton.cayley_hamilton` + `Mat2TraceRecurrence.trace_recurrence` (the trace/Lucas
recurrence is Cayley–Hamilton iterated); `UTracePeriodic.elliptic_orders_four_and_six`.  G185 note
updated to reflect this.

### 4. Merge marathon (origin/main → branch)
`/process` (0 sink violations; frontiers well-recorded).  Promotions: A3 → `theory/math/analysis/
divergence_depth_characterization.md` §7.1; A5 → `theory/math/analysis/spiral_coordinate_
classification.md` (binary-cover §); log rows 33/34.  Cross-domain note + essay (below).
`/org-audit`: fixed stale INDEX counts (physics 18→19 for main's `cp_phase`, essays 69→71, total
~205), narrative-hygiene rephrasings.  `/purity-check` + `/ready-to-merge`: clean, READY.

### 5. Cross-domain insight + essay — the `i`-point of the spiral axis
`research-notes/frontiers/casoratian_axis_cp_crossdomain.md` + essay
`theory/essays/synthesis/the_i_point_of_the_spiral_axis.md` (log row 35).  **Proven shared object**:
the order-4 spiral-axis point `4 = |ℤ[i]^×|` IS the CKM CP phase's `C₄` — the *same* ring `ℤ[i]`,
read as the continued-fraction floor rotation (`gaussian_floor_rotation`, `μ=−i`) and as the Hodge
`⋆` on `H*(Δ⁴)` (`SignedStarC4`); the CP phase sits at the `i`-point (disc `−4`), selected over the
order-6 Eisenstein rung.  Also: the companion-det sign `altSign(k−1)` is the `psign` of the shift
cycle (a 4th instance of main's "permutation under three readouts").

## Current Precision Results (0 free parameters)
**No physics-constant changes** (pure mathematics / foundations).  The merged CKM CP-phase content
(`δ=90°` forced, golden modulus `R_u=1/φ²`) is from main; see `catalogs/physics-constants.md` +
`theory/physics/cp_phase.md` for the standing DRLT table (α_em 0.09 ppb, etc.).

## Open Problems (Priority Order)

### 1. `det_companion` ↔ `psign(cyclicShift)` Lean bridge
The companion-determinant sign `altSign(k−1)` equals the permutation sign of the `k`-cycle shift;
proving `altSign(k−1) = PermSign.psign (cyclicShift k)` puts the Casoratian multiplier sign on the
same inversion-sign readout as `det(permMatrix)`/Legendre/Zolotarev.  Med, genuine.
Frontier: `research-notes/frontiers/casoratian_axis_cp_crossdomain.md`.

### 2. floor-rotation ↔ Hodge-`⋆` morphism (the `i`-point bridge)
The CP-phase = order-4 axis point is a *shared-object* identification (`ℤ[i]^×=C₄`), not yet a Lean
morphism between the `gaussian_floor_rotation` `C₄`-action and the `SignedStarC4` `⋆`-action.
Frontier: `research-notes/frontiers/casoratian_axis_cp_crossdomain.md`.

### 3. π continued-fraction non-holonomicity (classical open)
The one open input to the spiral-coordinate classification — would turn "π is rate-free" into a
theorem.  Not closable ∅-axiom here.  Frontier: `research-notes/frontiers/pi_nonholonomicity/`.

## Unresolved from This Session
No dead ends.  Two diagnosed traps worth remembering:
- **`ring_intZ` does not fold `x·0`** (treats `PE.C 0` as opaque) and **overflows on the order-4
  determinant** (the `4×4` Hankel normal form exceeds the kernel's `isDefEq`) — the structural
  `det_matMul` route is the escape, and it generalises to all orders for free.
- **`Nat.lt_one_iff`, `Int.zero_mul`, and `List.Mem` `decide` all leak `propext`** (Quot.sound for
  `List.Mem`) — use hand-rolled `lt_one_eq_zero`, `E213.Meta.Int213.zero_mul`, and structural
  predicates (not list membership) for strict ∅-axiom.

## Next
Spiral-axis A1/A3/A5 are closed; the cluster's only open input (π non-holonomicity) is
classical-open.  Highest-value next: **(1)** the `det_companion ↔ psign` bridge (genuine, ties the
Casoratian sign to the permutation/Legendre readout), or **(2)** the floor-rotation↔`⋆` morphism
essay→Lean bridge, or a fresh field marathon (`blueprints/`).

## Three-tier state (per CLAUDE.md "Three-tier discipline")
- **Promotions this session**: `theory/math/analysis/divergence_depth_characterization.md` §7.1
  (A3 ladder), `theory/math/analysis/spiral_coordinate_classification.md` (A5 non-coincidence);
  essay `theory/essays/synthesis/the_i_point_of_the_spiral_axis.md`.  Log rows 33/34/35.
- **Promotion candidates**: none outstanding from this branch (A1/A3/A5 captured in theory).
- **Active scratchpad**: `research-notes/frontiers/casoratian_axis_cp_crossdomain.md` (2 buildable
  bridges), `spiral_axis/` (G185 all-closed), `pi_nonholonomicity/`.

## File Map
```
lean/E213/Lib/Math/Analysis/Cauchy/CasoratianDeterminant.lean   ← NEW: all-orders Casoratian law (15 PURE)
lean/E213/Lib/Math/Analysis/Cauchy/Cauchy.lean                  ← + CasoratianDeterminant import
lean/E213/Lib/Math/Analysis/Cauchy/SecondCasoratian.lean        ← docstring: forward ref to general law
lean/E213/Lib/Math/Analysis/Cauchy/INDEX.md                     ← + determinantal-ladder subsection
lean/E213/Lib/Math/Algebra/Linalg213/DetN.lean                  ← + det_congr_lt (rows < n)
lean/E213/Lib/Math/Algebra/CayleyDickson/Tower/SpiralAxisCrystallographic.lean ← + cd_tower_axis_noncoincidence (3 PURE)
theory/math/analysis/divergence_depth_characterization.md       ← + §7.1 (A3 ladder)
theory/math/analysis/spiral_coordinate_classification.md        ← + A5 non-coincidence (binary-cover §)
theory/essays/synthesis/the_i_point_of_the_spiral_axis.md       ← NEW essay (CP phase = order-4 axis C₄)
theory/essays/INDEX.md, theory/INDEX.md                         ← counts fixed (essays 71, physics 19)
research-notes/frontiers/casoratian_axis_cp_crossdomain.md      ← NEW cross-domain note (+INDEX)
research-notes/frontiers/spiral_axis/G185_*.md                  ← A1/A3/A5 marked closed
research-notes/promotion_essay_log.md                           ← rows 33/34/35
```
