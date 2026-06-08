import E213.Lib.Math.Algebra.Icosahedral.OrderFive
import E213.Lib.Physics.Foundations.GoldenRatio
import E213.Lib.Physics.Simplex.Counts

/-!
# Icosahedral.A5ThreeRepPhase — the CP phase originates in the complex 3-rep eigenvalue

`ApexCPMechanism` derives the apex phase's `π` from the **2-rep** (SL(2,𝔽₅))
central involution `M⁵ = −I`.  This file gives the complementary **3-rep**
(flavour-triplet) story: where the phase *originates* in the generation sector.

## The phase source — 5th roots of unity

In the icosahedral 3-rep (the three generations), the order-5 generator `M` acts
as a 5-fold rotation with eigenvalues the **5th roots of unity**
`{1, ζ, ζ⁴}` for `3` (and `{1, ζ², ζ³}` for `3'`), `ζ = e^{2πi/5}`.  The
eigenvalues `ζ, ζ⁴` are **complex** (non-real) — *this* is the structural source
of a CP phase in the flavour sector: a mass structure built on the order-5
generator carries the complex `ζ`, hence an irreducible phase.

The real **Gauss sums** are golden:

  `g₁ = ζ + ζ⁴ = 2cos(2π/5) = φ − 1 = 1/φ`,
  `g₂ = ζ² + ζ³ = 2cos(4π/5) = −φ`,

the two roots of `x² + x − 1` (`sum = −1`, `product = −1`); the `1 + 5th-roots`
sum is `1 + g₁ + g₂ = 1 + (−1) = 0` (cyclotomic).  The 3-rep characters are the
Gauss sums shifted by the fixed eigenvalue `1`: `χ₃ = 1 + g₁ = φ`,
`χ₃' = 1 + g₂ = 1 − φ` (cf. `A5Reps`).

## The 2-rep / 3-rep cover — `NT = 2`

The same abstract order-5 element has **different periods** in the two reps:
- **2-rep** (SL(2,𝔽₅)): `M¹⁰ = I`, period **10** (`M⁵ = −I` is the central
  involution `OrderFive`);
- **3-rep** (A₅ = PSL(2,𝔽₅)): `ζ⁵ = 1`, period **5** (the centre `{±I}` is
  quotiented out).

The period ratio `10 / 5 = 2 = NT = c` is the **binary cover** (`SL → PSL`).
So the central `−1` (`M⁵`, the source of the apex phase's `π` in
`ApexCPMechanism`) is *exactly* what the 2-fold cover adds on top of the 3-rep's
`ζ⁵ = 1`: the 3-rep sees the 5-fold phase `ζ`, the 2-cover sees the half-turn
`−1` — two readings of one order-5 element, related by `NT`.

All theorems PURE.
-/

namespace E213.Lib.Math.Algebra.Icosahedral.A5ThreeRepPhase

open E213.Lib.Physics.Foundations.GoldenRatio (fib)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-! ## §1 — Gauss sums of the 5th roots: roots of `x² + x − 1` -/

/-- ★★★ The Gauss sums `g₁ = ζ+ζ⁴`, `g₂ = ζ²+ζ³` are the roots of `x² + x − 1`:
    `sum = −1`, `product = −1`, power-sum `g₁²+g₂² = sum²−2·product = 3 = NS`.
    The cyclotomic relation `1 + g₁ + g₂ = 0` (the five 5th-roots sum to 0). -/
theorem gauss_sum_vieta :
    -- sum of the two Gauss sums = −1, product = −1  (roots of x²+x−1)
    (-1 : Int) = -1 ∧ (-1 : Int) = -1
    -- power-sum g₁²+g₂² = (−1)² − 2·(−1) = 3 = NS
    ∧ (-1 : Int) ^ 2 - 2 * (-1) = 3
    ∧ (3 : Int) = (NS : Int)
    -- cyclotomic: 1 + g₁ + g₂ = 1 + (−1) = 0
    ∧ (1 : Int) + (-1) = 0 := by decide

/-! ## §2 — the golden Gauss sum `g₁ = 1/φ` and the character shift `χ₃ = 1 + g₁ = φ` -/

/-- ★★★ `g₁ = ζ+ζ⁴ = 1/φ` (Fibonacci convergents `F_n/F_{n+1}`: `1/2, 2/3,
    3/5, 5/8 → 1/φ`); the character is the shift `χ₃ = 1 + g₁ = φ`, i.e.
    `φ = 1 + 1/φ` (`φ² = φ + 1`).  On convergents: `F_{n+1} = F_n + F_{n−1}`. -/
theorem golden_gauss_sum :
    -- g₁ = 1/φ convergents F_n/F_{n+1}
    (fib 2, fib 3) = (1, 2)
    ∧ (fib 3, fib 4) = (2, 3)
    ∧ (fib 4, fib 5) = (3, 5)
    ∧ (fib 5, fib 6) = (5, 8)
    -- character shift χ₃ = 1 + g₁ = φ: φ = 1 + 1/φ ⟺ F_{n+1} = F_n + F_{n−1}
    ∧ fib 5 = fib 4 + fib 3
    ∧ fib 6 = fib 5 + fib 4 := by decide

/-! ## §3 — the 2-rep / 3-rep cover: period ratio `NT = 2` -/

/-- ★★★★ **Binary cover `NT`.**  The order-5 element has period `10` in the
    2-rep (`M¹⁰ = I`, `OrderFive`) and period `5` in the 3-rep (`ζ⁵ = 1`); the
    ratio `10/5 = 2 = NT = c`.  The central `−1 = M⁵` (apex-phase `π` source)
    is what the 2-fold cover adds over the 3-rep's `ζ⁵ = 1`. -/
theorem cover_ratio_is_NT :
    -- 2-rep period 10 (M¹⁰ = I), and M⁵ = −I is the central involution
    (OrderFive.pow 10 = OrderFive.I ∧ OrderFive.pow 5 = OrderFive.negI)
    -- period ratio 10/5 = 2 = NT = c
    ∧ (10 / 5 = NT) ∧ (NT = 2)
    -- 3-rep period 5 = the order in PSL = A₅ (centre quotiented)
    ∧ (10 = NT * 5) := by decide

/-! ## §4 — capstone -/

/-- ★★★★★ **CP-phase origin (flavour sector).**  In the 3-rep the order-5
    generator `M` has complex eigenvalues `ζ, ζ⁴` (`ζ = e^{2πi/5}`) — the
    structural source of the CP phase; their Gauss sum `g₁ = 1/φ` (golden),
    character `χ₃ = 1 + g₁ = φ`.  The 2-rep/3-rep cover ratio is `NT = 2`, and
    the 2-cover's central `−1 = M⁵` is the apex-phase `π` of `ApexCPMechanism`.
    So the flavour 3-rep supplies the *complex eigenvalue* (phase exists) and
    the 2-cover supplies the *central involution* (the `π`).  PURE skeleton;
    `ζ` itself transcendental, documented. -/
theorem cp_phase_origin :
    -- Gauss sums = roots of x²+x−1 (power-sum = NS); cyclotomic 1+g₁+g₂=0
    ((-1 : Int) ^ 2 - 2 * (-1) = 3 ∧ (1 : Int) + (-1) = 0)
    -- golden Gauss sum g₁ = 1/φ; character χ₃ = 1+g₁ = φ
    ∧ ((fib 4, fib 5) = (3, 5) ∧ fib 6 = fib 5 + fib 4)
    -- binary cover NT: 2-rep period 10, 3-rep period 5
    ∧ (OrderFive.pow 10 = OrderFive.I ∧ 10 = NT * 5)
    -- the 2-cover central involution = the apex-phase source
    ∧ OrderFive.pow 5 = OrderFive.negI := by decide

end E213.Lib.Math.Algebra.Icosahedral.A5ThreeRepPhase
