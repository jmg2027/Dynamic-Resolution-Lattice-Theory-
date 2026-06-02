# G168 — Eisenstein (3-axis) completion: floor rotation + completion factors through the real norm

Built independently on `claude/goal-g166-A6MVE` (no merge from the CD-tower branch).
Module: `lean/E213/Lib/Math/CayleyDickson/Integer/EisensteinCompletion.lean` (9 PURE).
Sits on the existing `EisensteinCrossDet` (14 PURE, the floor) + `ContinuedFractionModulus`
(the real completion).

## Question

Parallel to the real continued-fraction completion (`cf_universal_total_modulus`, every
real ≥ 1 completes via its CF), build the **Eisenstein** (`ℤ[ω]`, 3-axis) analog and see
what is genuinely different.

## What was already closed (floor)

`EisensteinCrossDet.crossDet_on_units`: for a constant-coefficient `ℤ[ω]`-recurrence
`s_{n+2} = p·s_{n+1} + q·s_n` with `q`, `W_0` units, the cross-determinant `W_n` is one of
the **6 units** at every step.  (Over `ℤ` it is one of the 2 units `±1`.)

## New findings (this note)

### Numerics (the investigation that drove the build)

- ω-Fibonacci denominators `‖d_n‖²` (`q = ω`): `[1,0,1,1,1,3,4,7,13,21,37,64,109,189]` —
  a transient (`d_1 = 0`, **impossible on the real line** with `a_i ≥ 1`), then grows.
- Real-integer CF (`a_i ∈ ℤ`): `‖d_n‖² = [1,0,1,4,25,144,841,…]` = **perfect squares**
  `q_n²` (the real denominators squared).
- ω-Fibonacci cross-det values: `(1,0)→(0,−1)→(−1,−1)→(−1,0)→(0,1)→(1,1)→(1,0)` — the
  cross-determinant **rotates through all 6 units, period 6**, by the fixed multiplier
  `μ = ⟨0,−1⟩ = −ω` (a primitive 6th root).

### Theorems

1. `gap_scale_factors` — the gap `W_n/(q_n q_{n+1})` has unit numerator (`‖W_n‖² = 1`), so
   its scale is `‖q_n q_{n+1}‖² = ‖q_n‖²·‖q_{n+1}‖²` (`normSq_mul`): **3-axis convergence is
   governed by the integer norm product** — a 2-axis quantity.
2. `eisenstein_real_slice_completes` — real partial quotients embed (`dEis = ofInt cfQn`):
   `‖d_n‖² = (cfQn n)²` (`dEis_normSq`), and these diverge (`dEis_norm_diverges`, from
   `cfQn_ge_self`).  So every real's Eisenstein CF completes via its real completion — the
   **2-axis is the completing diagonal of the 3-axis**.
3. `eisenstein_floor_rotation` — the genuinely-complex content: cross-det rotates by
   `μ = −ω` (`omega_cross_step`), `μ⁶ = 1`, orbit returns at step 6, unit group order
   `6 = NS·NT`.  **Over `ℤ` rotation order 2; over `ℤ[ω]` order 6 = NS·NT.**

## The structural reading

The 3-axis is richer than the 2-axis in **exactly one** way: the floor's rotation order
(`6` vs `2`, = the unit-group order = `NS·NT` vs `NT`).  **Convergence itself is a 2-axis
phenomenon** — the integer norm sequence `N_n = ‖q_n‖²` must grow, and on the real slice it
grows as a perfect square.  The complex/hexagonal directions add rotation, not a new
convergence mechanism: the limit's *existence* still rides the real growth of the norm form.

Open (not formalised, both branches agree): the transcendental 3-axis value — the
equianharmonic Eisenstein period, a `Γ(1/3)` value (j=0 CM by `ℤ[ω]`).  To pin it as a
*theorem* (the way `e` is pinned on the 2-axis) would need its natural series/CF to carry a
norm-growth rate tied to the disc-`−3` structure.

Cross-branch note: `claude/category-d-trig-conj-mul-yZZ8U` reached `3-axis ↔ Eisenstein ω`
(`AxisSeedTrichotomy`) from the algebra/CD-tower side; this note reaches the same ω from the
analytic/completion side, and adds: the floor *rotates* with order `NS·NT`, and completion
factors through the real norm.
