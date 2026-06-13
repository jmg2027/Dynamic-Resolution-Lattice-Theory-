# G185 — spiral-axis cluster deep research: the two CM points, and the honest unifier

**Date**: 2026-06-02.  **Method**: 4-agent repo-wide deep research (deep survey + connection-hunt
+ conjecture-gen + adversarial audit) on the cluster *spiral axis {2,4,6}=2·{1,2,3} ↔ Cassini sign
↔ q=±1 ↔ 2-1-3 ↔ modular/Cayley-Dickson*.  **Trigger**: "궤도-클라임 방향이 몇 개?" → answer
**3** (the axis `{2,4,6}`, exhaustively, `imaginary_quadratic_unit_trichotomy`).

## The genuine through-line (the audit's verdict)

Everything *real* in this cluster flows from **two CM points**: **disc −4 (`i`)** and **disc −3
(`ω`)**.  They simultaneously give the unit-group orders `4, 6`, the modular elliptic fixed points
(`S` fixes `i`, `U` fixes `ω`), and the integral cyclotomic traces `{1,2,3,4,6}`.  The
`det_step`/Casorati multiplier ladder is a *separate* genuine result (about `q = det(shift)`,
generic — not about −3/−4).

## Proved this round — `CayleyDickson/Integer/UnitsToModular` (9 PURE)

**Bridge B (the Tier-1 gap both survey + connection agents flagged, done honestly):** the
*regular representation* unifies the spiral-axis units with the modular generators via a genuine
ring homomorphism (NOT glyph-reuse):
  - `repI : ℤ[i] → M₂(ℤ)`, `repI ⟨a,b⟩ = ⟨a,−b,b,a⟩`; **`repI_I : repI i = S` (literally)**, `repI_hom`
    (homomorphism).  `gaussian_unit_realizes_S`: `S` IS the regular-rep image of the Gaussian unit
    `i`, so `S⁴=I` is the image of `i⁴=1` under a real morphism.
  - `repO : ℤ[ω] → M₂(ℤ)`, `repO_hom`; `eisenstein_unit_realizes_U_class`: `repO(−ω)` has the same
    trace (1), det (1), order (6) as `U` — the same `SL₂` conjugacy class `λ²−λ+1` (up to
    conjugacy; the repo's `ℤ[ω]` basis differs from `U`'s by orientation).
  - `orders_four_six_from_two_cm_points`: the orders `4, 6` come from the two CM points via
    `repI, repO` — the honest unifier of `{2,4,6}=2·{1,2,3}` with the modular generators.

## Interlock (proved vs thematic) — from the connection + survey agents

  - **PROVED**: `{2,4,6}=2·{1,2,3}` (`spiral_axis_is_even_crystallographic`); the `q=±1` Cassini law
    (`det_step`, `second_casoratian`); the trichotomy `{2,4,6}` (`imaginary_quadratic_unit_trichotomy`);
    the generator orders `S⁴=I, U⁶=I`; and now **Bridge B** (units → `S,U`).
  - **THEMATIC GAPS (were docstring-glyph "−1" reuse, NOT theorems)**: "central −1 = Cassini sign"
    and "Cassini q=−1 = modular S²=−I".  Bridge B closes the *honest* part (units↔generators by a
    morphism); the remaining "one central −1 threads all" is per-type and only literal on the `Int`
    axis.

## Stereotype-matches identified and AVOIDED (the audit's guard rails)

  - **CD dimension tower `1,2,4,8` ↔ axis `{2,4,6}`** — EMPTY past `{2,4}` (diverge `6≠8`: no
    octonion at the axis, no Eisenstein-6 in the CD tower).  The real CD content flows through the
    *rings* `ℤ[i],ℤ[ω]` (Bridge B), NOT the dimension tower.  Conjecture A5 (prove the
    non-coincidence) is the correct defensive response.
  - **"Cassini sign IS the McKay/E₈ binary cover"** — `−1` shared by symbol, no cover map; narrative.
  - **`det q=−1` = modular `S²=−I`** — FORCIBLE: `S` has det `+1` (`q=+1`); its order-4 square `−I`
    is a *different* `−1` from a determinant-sign multiplier.  Do not formalize.
  - **`PSL₂(ℤ) ≅ ℤ/2*ℤ/3`** — cited classical, NOT formalized; `modular_generator_orders` witnesses
    only the generator orders.  Don't narrate the free product as proved.
  - **2-1-3 ↔ axis**: honest 2/3 (endpoints `2=NT`, `6=NS·NT`); the middle `4=|ℤ[i]^×|` has no clean
    NS/NT reading.

## Open / next (ranked, from the conjecture agent)

  - **A1** ✓ **CLOSED**: the modular generators `S,U` are trace-orbits — `trace(Mⁿ)` satisfies
    `t(n+2)=tr·t(n+1)−det·t(n)` (Cayley–Hamilton iterated).  `Real213/Mat2/Mat2CayleyHamilton.cayley_hamilton`
    + `Mat2TraceRecurrence.trace_recurrence`; the elliptic orders read off as trace periods 4/6
    (`UTracePeriodic.elliptic_orders_four_and_six`), the hyperbolic Lucas growth
    (`golden_trace_recurrence`).  The modular↔Cassini bridge is a theorem.
  - **A3** ✓ **CLOSED — and generalised past `k=4`.**  The determinantal ladder closed at **all**
    orders in one structural theorem (not just the requested order-4 `hankel4`):
    `Analysis/Cauchy/CasoratianDeterminant.casoratian_det_step` — for any constant-coefficient
    order-`(K+1)` recurrence the `(K+1)×(K+1)` Hankel/Casoratian determinant multiplies by the
    companion determinant `altSign K · a 0` each step.  Proof = `H(n+1) = C·H(n)`
    (`hankel_shift_eq_matMul`) + `DetMul.det_matMul` + `det_companion` (no `ring_intZ` expansion —
    the order-4 normal form exceeds the kernel; `second_order/third_order/fourth_order_multiplier`
    are the rung instances).  Subsumes `CassiniUnimodular.det_step` (order 2) and
    `SecondCasoratian.second_casoratian` (order 3).
  - **A5** ✓ **CLOSED**: the CD-tower / axis non-coincidence — `Tower/SpiralAxisCrystallographic`
    `cd_tower_axis_noncoincidence`.  The CD dimension tower `{1,2,4,8} = 2ⁿ` and the spiral axis
    `{2,4,6}` meet only on `{2,4}` and diverge for two independent reasons: `8 = 2³` is a power of
    two but not crystallographic (`φ 8 = 4 > 2`, the axis ⊆ crystallographic — *no octonion at the
    axis*); `6` is crystallographic (`φ 6 = 2`) but no power of two (`not_pow_two_six` — *no order-6
    CD rung*).  The `1,2,4,8 ↔ {2,4,6}` stereotype is ruled out; the axis's CD content flows
    through the rings `ℤ[i], ℤ[ω]` (unit orders `4,6`), not the dimension doubling.

**Status: all three ranked conjectures (A1, A3, A5) closed ∅-axiom.**
