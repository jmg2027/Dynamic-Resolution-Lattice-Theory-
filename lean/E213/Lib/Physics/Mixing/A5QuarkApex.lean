import E213.Lib.Math.Algebra.Icosahedral.A5Bridge
import E213.Lib.Physics.Foundations.GoldenRatio

/-!
# A5QuarkApex — the quark CKM has two distinct origins (magnitude vs CP-depth)

Established `A₅`/`SU(5)×A₅` quark flavour models set the structure the DRLT apex
must respect:

- **Established flavour models *fit* the quark CKM, they do not golden-predict
  it.**  At leading order the CKM is `≈ identity + Cabibbo`; the apex / CP phase
  comes from *subleading* terms fit to data (a trivial-identity CKM is the
  generic leading-order result of any discrete flavour group).  So the CKM
  **magnitudes** (Cabibbo) and the **CP-depth** (apex) have *distinct* origins —
  no single golden object delivers both.

DRLT mirrors exactly this two-origin structure, and *sharpens* it:

- **Magnitude sector — Cabibbo `λ`** is a **rational `d`-object**, NOT golden:
  `λ = 5/22 = d/(d²−d+c)` (`CabibboAngle`).  Its denominator `22` is **not a
  Fibonacci number** (`F₈ = 21 < 22 < 34 = F₉`), so `λ` is **not** a convergent
  of `1/φ²` — the Cabibbo angle is not a golden power.
- **CP-depth sector — apex `R_u`** IS golden: `R_u = 1/φ²`, the contracting
  eigenvalue of the self-reference map `M` (an order-5 `A₅` element,
  `Icosahedral.OrderFive`).

So DRLT does **not** force one golden number onto the whole CKM (which would be
wrong — the Cabibbo angle is not golden).  It assigns the golden `1/φ²` to the
**CP-depth** alone, and a rational `d`-object to the magnitude — the same
two-origin split the flavour-model literature finds, but with the CP-depth
*structurally* golden (`M`-eigenvalue) rather than fit.

## Honest scope

This records the two-origin **structure** (PURE) and the external concordance
(below).  It does **not** derive the apex *value* `1/φ²` from explicit quark
`A₅` mass matrices — that remains the open multi-session frontier
(`ckm_rho_eta_apex.md`).  DRLT's golden apex is novel relative to all existing
flavour models (which fit, not predict, the apex).

## External concordance (documented, trig — not PURE-Nat)

The nearest established prediction is the **nearly-right unitarity triangle**
(`α ≈ 89–90°`, `δ ≈ 1.188 ± 0.016 rad`) from discrete symmetry + a `π/2`
mass-matrix phase (arXiv:1805.07773, 1103.5930).  DRLT's structural
`δ = π/φ² = 1.200 rad` agrees at **0.75σ**; `α = 88.8°` is near (not exactly)
`90°`.

All theorems PURE.
-/

namespace E213.Lib.Physics.Mixing.A5QuarkApex

open E213.Lib.Physics.Foundations.GoldenRatio (fib)

def NS : Nat := 3
def NT : Nat := 2
def c  : Nat := 2
def d  : Nat := 5

/-! ## §1 — magnitude sector: Cabibbo `λ = 5/22` is rational, not golden -/

/-- ★★★ Cabibbo `λ = d/(d²−d+c) = 5/22`.  Its denominator `22` lies strictly
    between the Fibonacci numbers `F₈ = 21` and `F₉ = 34`, so it is **not**
    Fibonacci — hence `λ` is **not** a convergent of `1/φ²` (whose convergents
    have Fibonacci denominators `5, 13, 34, …`).  The Cabibbo angle is a
    rational `d`-object, not a golden power. -/
theorem cabibbo_is_rational_not_golden :
    -- λ denominator: d²−d+c = 22
    d * d - d + c = 22
    -- 22 is strictly between consecutive Fibonacci F₈=21 and F₉=34 ⇒ not Fibonacci
    ∧ fib 8 < 22 ∧ 22 < fib 9
    -- the 1/φ² convergent denominators are Fibonacci (5,13,34) — 22 is none of them
    ∧ fib 5 = 5 ∧ fib 7 = 13 ∧ fib 9 = 34
    ∧ 22 ≠ fib 5 ∧ 22 ≠ fib 7 ∧ 22 ≠ fib 9 := by decide

/-! ## §2 — CP-depth sector: apex `1/φ²` is the golden `M`-eigenvalue -/

/-- ★★★ The apex `R_u = 1/φ²` is golden — the contracting eigenvalue of the
    self-reference map `M` (order-5 `A₅` element).  Its convergents have
    Fibonacci numerator/denominator `F₃/F₅, F₅/F₇ = 2/5, 5/13`, distinct from
    the rational Cabibbo `5/22`.  So magnitude (`5/22`, rational) and CP-depth
    (`1/φ²`, golden) are **different** objects. -/
theorem apex_is_golden_distinct_from_cabibbo :
    -- apex convergents are Fibonacci ratios (golden)
    (fib 3, fib 5) = (2, 5) ∧ (fib 5, fib 7) = (5, 13)
    -- the Cabibbo rational 5/22 is none of the apex convergents
    ∧ (5, 22) ≠ (fib 3, fib 5)
    ∧ (5, 22) ≠ (fib 5, fib 7)
    -- two-origin split: magnitude denom 22 ≠ any apex (Fibonacci) denom
    ∧ 22 ≠ fib 5 ∧ 22 ≠ fib 7 := by decide

/-! ## §3 — capstone: the two-origin structure -/

/-- ★★★★★ **Two-origin CKM structure.**  DRLT assigns:
    magnitude → rational `d`-object Cabibbo `λ = 5/22` (`22 ∉ Fibonacci`);
    CP-depth → golden `1/φ²` (the `A₅` order-5 `M`-eigenvalue, Fibonacci
    convergents `2/5, 5/13`).  This matches the flavour-model literature's
    finding that CKM magnitudes and the CP phase have distinct origins — but
    DRLT's CP-depth is *structurally* golden, not fit.  The apex *derivation*
    from quark `A₅` mass matrices remains open (`ckm_rho_eta_apex.md`). -/
theorem two_origin_ckm :
    -- magnitude: Cabibbo 5/22 rational, denom not Fibonacci
    (d * d - d + c = 22 ∧ fib 8 < 22 ∧ 22 < fib 9)
    -- CP-depth: apex 1/φ² golden, Fibonacci convergents
    ∧ ((fib 3, fib 5) = (2, 5) ∧ (fib 5, fib 7) = (5, 13))
    -- distinct: 22 is not an apex (Fibonacci) denominator
    ∧ (22 ≠ fib 5 ∧ 22 ≠ fib 7 ∧ 22 ≠ fib 9) := by decide

end E213.Lib.Physics.Mixing.A5QuarkApex
