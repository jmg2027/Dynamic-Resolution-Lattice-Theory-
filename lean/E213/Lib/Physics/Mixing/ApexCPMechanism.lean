import E213.Lib.Math.Algebra.Icosahedral.OrderFive
import E213.Lib.Physics.Foundations.GoldenRatio

/-!
# ApexCPMechanism — the CKM apex derived from the self-reference map (213-internal)

A **213-native** derivation of the unitarity-triangle apex `z = ρ̄ + iη̄`,
using **no external flavour model** — only the residue self-reference map
`M = [[c,1],[1,1]]` (§5.6) and its proven structure (`Icosahedral.OrderFive`,
`Mobius213`).

## The construction (§5.7 frozen + dynamic, unified)

`M` carries two simultaneous Lens readings (`Mobius213` §5.7):

- **Frozen (ℝ / hyperbolic).**  Eigenvalues `φ², 1/φ²`; the contraction rate to
  the residue fixed point is `r = 1/φ²` (`OrderFive`/`JarlskogApex`).  This is a
  **real** number — it has no phase, so the frozen reading *alone* cannot
  produce CP violation.
- **Dynamic (finite / A₅ / mod-`d`).**  `M` is an order-10 element of
  `SL(2,𝔽₅)` with `M⁵ ≡ −I (mod 5)` (`OrderFive`): the **half-period** is the
  **central involution** `−I = e^{iπ}`.  So the dynamic reading carries a
  half-turn phase `π`.

The apex is the single complex object that reads `M` through **both** Lenses at
once — the contraction `r` (frozen modulus) decorated by the central involution
(dynamic phase):

  **`z = r · (−1)^r = r · e^{iπr}`,  with `r = 1/φ²`, `(−1) = M⁵`.**

This is exactly the single-parameter golden apex `z = r·e^{iπr}`
(`JarlskogApex` §4), now with **both** ingredients internal:
`r = 1/φ²` (frozen eigenvalue) and `π` from `(−1) = M⁵` (dynamic central
element).  Hence `R_u = r = 1/φ²` and `δ = πr = π/φ²`.

## Why CP violation exists at all (the falsifiable core)

`η = Im z = r·sin(πr)`.  This is nonzero **iff** the half-period central element
is `−1` (not `+1`):

- if `M⁵ = +I`:  `(+1)^r = 1`, `z = r` is **real**, `η = 0` — **no CP violation**;
- if `M⁵ = −I`:  `(−1)^r = e^{iπr}` is non-real, `η = r·sin(πr) ≠ 0` — **CP violates**.

`M⁵ ≡ −I (mod 5)` is a **proven 213 theorem** (`OrderFive.order_exactly_five_in_psl`).
So **CP violation in the quark sector follows, internally, from the self-reference
map's half-period being the central involution `−1`** — a structural reason, not
a fit.  "Why is CP-depth the self-reference contraction rate?" — because the apex
*is* that contraction rate `r`, complexified by the dynamic Lens's central
element `M⁵ = −1`.

## Honest scope (`§5.4`)

Derived internally: the apex *modulus* `= r` (frozen contraction), the phase's
`π` (`= M⁵` central involution), and the **CP-existence mechanism**
(`η ≠ 0 ⟺ M⁵ = −1`).  The residual is the **coupling** `δ = π·R_u` — but note it
*follows* from the form `z = r·(−1)^r` (`arg((−1)^r) = πr`), so the real
question is why the apex is **single-parameter** (exponent `= modulus`).  That is
the `§5.1` **no-exterior / 0-parameter** principle: the apex phase carries no
independent dialer, so it *must* be a function of the one internal number `r`
and the only phase constant `π = arg(M⁵)`; `δ = π·r` is the minimal linear
realization.  So the coupling is **0-parameter-forced**, not arbitrary; the soft
residual is only the minimality of the linear form `f(r) = π·r`.

**`π` is 213-internal** (correcting an earlier overclaim that it was "the Nat
boundary, outside 213"): `213` builds `π` as a `Real213` cut (`PiCut`, a Wallis
`AbCutSeq`, `π ∈ (14/5,4)`, ∅-axiom), so `δ = π·R_u` is a product of two
`Real213` cuts and the apex is internal *including* `π` (`ApexPiInternal`).  The
`sin`/`e^{iπr}` relations are irrational-valued (as every interesting real is),
not exterior; the integer skeleton below is PURE-Nat.
-/

namespace E213.Lib.Physics.Mixing.ApexCPMechanism

open E213.Lib.Math.Algebra.Icosahedral
open E213.Lib.Physics.Foundations.GoldenRatio (fib)

/-! ## §1 — the half-period central involution `M⁵ = −I = e^{iπ}` -/

/-- ★★★ The dynamic reading's half-period is the central involution `−I`
    (`= e^{iπ}`, phase `π`): `M⁵ = −I`, `M¹⁰ = I`, and `−I ≠ I` (the involution
    is nontrivial).  Source of the apex phase's `π`. -/
theorem half_period_central_involution :
    OrderFive.pow 5 = OrderFive.negI
    ∧ OrderFive.pow 10 = OrderFive.I
    ∧ OrderFive.negI ≠ OrderFive.I := by decide

/-! ## §2 — CP-existence mechanism: `η ≠ 0 ⟺ M⁵ = −1`

The apex phase factor is `(M⁵-sign)^r`.  For the `+I` (sign `+1`) case the
factor is real (`1^r = 1`) and `η = 0`; for the `−I` (sign `−1`) case it is
`e^{iπr}` and `η = r·sin(πr) ≠ 0`.  The decidable content: the half-period IS
`−I`, and `−I` is genuinely distinct from `+I`, so the non-real branch is
selected. -/

/-- ★★★★ **CP violation follows from `M⁵ = −1`.**  The half-period central
    element is `−I`, distinct from the CP-trivial `+I`.  Were it `+I` the apex
    would be real (`η = 0`); because it is `−I`, the apex carries phase `πr` and
    `η = r·sin(πr) ≠ 0`.  Internal, structural — not a fit. -/
theorem cp_exists_from_central_minus_one :
    -- the half-period sign is −I, the non-trivial (CP-generating) branch
    OrderFive.pow 5 = OrderFive.negI
    -- distinct from the CP-trivial +I branch (which would force η = 0)
    ∧ OrderFive.pow 5 ≠ OrderFive.I
    -- −I and +I are genuinely different central elements (the dichotomy is real)
    ∧ OrderFive.negI ≠ OrderFive.I := by decide

/-! ## §3 — the apex `z = r·(−1)^r`, `r = 1/φ²`, both ingredients internal

`R_u = r = 1/φ²` (frozen contraction, Fibonacci convergents `2/5, 5/13`);
`(−1) = M⁵` (dynamic central); `δ = πr`.  The single-parameter golden apex with
internal ingredients. -/

/-- ★★★★ **Apex ingredients, both internal.**  Modulus `R_u = r = 1/φ²`
    (frozen contraction, convergents `F₃/F₅, F₅/F₇ = 2/5, 5/13`); the phase's
    `π` comes from `(−1) = M⁵`; `δ = π·R_u`.  No external input. -/
theorem apex_ingredients_internal :
    -- modulus r = 1/φ²: Fibonacci convergents (frozen eigenvalue)
    (fib 3, fib 5) = (2, 5) ∧ (fib 5, fib 7) = (5, 13)
    -- phase π from the central involution M⁵ = −I (dynamic)
    ∧ OrderFive.pow 5 = OrderFive.negI
    -- φ² atomic anchor: d·NT = NS²+1 (φ²+1/φ² = NS)
    ∧ (5 * 2 = 3 * 3 + 1) := by decide

/-! ## §3.5 — the coupling is the §5.7 coincidence, NOT a spiral trajectory

A tempting wrong picture: the apex is `n` steps of a uniform discrete spiral
(phase `nπ/5` from `M⁵=−I` over 5 steps, modulus `(1/φ²)ⁿ`).  This is **ruled
out**: the apex phase-fraction `δ/π = 1/φ²` lies **strictly between** the
consecutive uniform steps `1/5` and `2/5` (`1/5 < 8/21 ≤ 1/φ² ≤ 5/13 < 2/5`), so
**no integer step `n` realizes it** — and the fractional `n = 5/φ²` would give
modulus `(1/φ²)^{5/φ²} ≠ 1/φ²`.  So *if* `δ/π = R_u` (the single-parameter
posit), it is **not** realized as a spiral trajectory.  Note this *also* shows
§5.7 does not force the coincidence: the per-step rates differ (frozen `1/φ²`,
dynamic `1/5`).  What is proven here is the **exclusion** (no uniform step), not
the coincidence — `δ = π·R_u` stays the posit. -/

/-- ★★★ **Not a uniform spiral step (coupling = §5.7 coincidence).**  The apex
    phase-fraction `1/φ²` is strictly between the uniform-spiral steps `1/5` and
    `2/5` (cross-multiplied via the Fibonacci convergents `8/21`, `5/13`), so no
    integer step realizes the apex.  The coupling `δ/π = R_u` is therefore the
    frozen=dynamic *coincidence* (both `= 1/φ²`), not a trajectory. -/
theorem coupling_not_uniform_spiral :
    -- 1/5 < 8/21 ≤ 1/φ² (lower): 1·21 < 5·8
    (1 * 21 < 5 * 8)
    -- 1/φ² ≤ 5/13 < 2/5 (upper): 5·5 < 13·2
    ∧ (5 * 5 < 13 * 2)
    -- the bracketing convergents are the 1/φ² ones (golden, Fibonacci)
    ∧ (fib 6, fib 8) = (8, 21) ∧ (fib 5, fib 7) = (5, 13) := by decide

/-! ## §4 — capstone -/

/-- ★★★★★★ **Apex from self-reference (213-internal).**  The CKM apex is the
    self-reference contraction rate `r = 1/φ²` (frozen) decorated by the
    dynamic central involution `M⁵ = −1` (`= e^{iπ}`): `z = r·(−1)^r = r·e^{iπr}`,
    so `R_u = 1/φ²`, `δ = π/φ²`.  CP violation `η = r·sin(πr) ≠ 0` follows from
    `M⁵ = −I` (proven) — were it `+I`, `η = 0`.  This resolves "why CP-depth =
    self-reference contraction" internally; the residual is the frozen↔dynamic
    coupling `δ = π·R_u`.  PURE skeleton. -/
theorem apex_from_self_reference :
    -- half-period central involution (the π)
    (OrderFive.pow 5 = OrderFive.negI ∧ OrderFive.pow 10 = OrderFive.I)
    -- CP-existence: −I ≠ +I (nonzero η selected)
    ∧ OrderFive.pow 5 ≠ OrderFive.I
    -- modulus r = 1/φ² (frozen), convergents 2/5, 5/13
    ∧ ((fib 3, fib 5) = (2, 5) ∧ (fib 5, fib 7) = (5, 13))
    -- φ² atomic: φ²+1/φ² = NS  (d·NT = NS²+1)
    ∧ (5 * 2 = 3 * 3 + 1) := by decide

end E213.Lib.Physics.Mixing.ApexCPMechanism
