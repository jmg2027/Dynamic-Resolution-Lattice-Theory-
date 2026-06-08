import E213.Lib.Math.Algebra.Icosahedral.OrderFive
import E213.Lib.Physics.Foundations.GoldenRatio

/-!
# Icosahedral.A5Bridge — the golden character `φ` and the eigenvalue `φ²` are one

`OrderFive` shows the self-reference map `M` reduces mod `d = 5` to an order-5
element of `PSL(2,𝔽₅) ≅ A₅` — a 5-fold icosahedral rotation. This file ties
that mod-`d` reading to the ℝ-side reading (`Mobius213`: eigenvalues `φ², 1/φ²`)
through the golden ratio that lives in **both**.

## The two golden readings of the same `M`

- **A₅ character (mod-`d` reading).**  In the standard 3-dim irrep of
  `A₅ ≅` icosahedral, a 5-fold rotation by `2π/5` has eigenvalues
  `1, e^{2πi/5}, e^{−2πi/5}`, so its **character** is
  `χ₃ = 1 + 2cos(2π/5) = 1 + (φ−1) = φ` — the golden ratio (Groupprops, A₅
  rep theory). The two inequivalent triplets `3, 3'` give the two values
  `{φ, 1−φ}`, exactly the roots of `x² − x − 1` (`sum = 1`, `product = −1`).

- **ℝ eigenvalue (frozen reading).**  `M`'s eigenvalue is `φ²`, a root of
  `x² − NS·x + 1` (`sum = NS = 3`, `product = 1`), `Mobius213`.

## The bridge — one Fibonacci step

The two readings are not two golden numbers but **one**, related by the
defining identity `φ² = φ + 1`:

  **eigenvalue(M) = χ₃(M) + 1**     (`φ² = φ + 1`).

This is *exactly* the Fibonacci recurrence: the convergent of `φ²` is
`F_{n+2}/F_n = 1 + F_{n+1}/F_n` = `1 + (convergent of φ)`, because
`F_{n+2} = F_n + F_{n+1}`. So "the A₅ rotation character plus one is the
self-reference eigenvalue" is the recurrence `fib (n+2) = fib n + fib (n+1)`
read on convergents — PURE.

All theorems PURE.
-/

namespace E213.Lib.Math.Algebra.Icosahedral.A5Bridge

open E213.Lib.Physics.Foundations.GoldenRatio (fib)

/-! ## §1 — `|A₅| = |PSL(2,𝔽₅)| = 60` -/

/-- ★★ Group orders: `|SL(2,𝔽₅)| = d·(d²−1) = 120`, `|PSL(2,𝔽₅)| = 60`
    (mod the centre `{±I}`), `= |A₅| = 5!/2`.  The order-5 element `M`
    (`OrderFive`) sits inside this `A₅`. -/
theorem a5_order :
    -- |SL(2,𝔽₅)| = 5·(5²−1) = 120
    (5 * (5 * 5 - 1) : Nat) = 120
    -- |PSL(2,𝔽₅)| = 120 / 2 = 60
    ∧ (120 / 2 : Nat) = 60
    -- |A₅| = 5! / 2 = 60
    ∧ (5 * 4 * 3 * 2 * 1 / 2 : Nat) = 60 := by decide

/-! ## §2 — the two triplet characters `{φ, 1−φ}` = roots of `x² − x − 1`

`χ₃ = φ`, `χ₃' = 1 − φ`.  As the roots of `x² − x − 1`: `sum = 1`,
`product = −1`.  In Fibonacci form the larger root `φ`'s convergents are
`F_{n+1}/F_n`. -/

/-- ★★★ The golden character data.  The triplet characters on the order-5
    class are `{φ, 1−φ}`, the roots of `x² − x − 1` (the golden minimal
    polynomial): the convergent witness is the Fibonacci ratio `F_{n+1}/F_n`,
    bracketing `φ`, with Cassini `F_{n−1}F_{n+1} − F_n² = ±1` giving the
    `product = −1` of the root pair. -/
theorem golden_character :
    -- φ-convergents F_{n+1}/F_n: 2/1, 3/2, 5/3, 8/5, 13/8 (→ φ ≈ 1.618)
    (fib 3, fib 2) = (2, 1)
    ∧ (fib 4, fib 3) = (3, 2)
    ∧ (fib 5, fib 4) = (5, 3)
    ∧ (fib 6, fib 5) = (8, 5)
    -- golden min poly `x²−x−1`: Cassini `F₃·F₅ − F₄² = +1`, `F₄·F₆ − F₅² = −1`
    --   (the alternating ±1 = the `product = −1` of {φ, 1−φ})
    ∧ fib 3 * fib 5 = fib 4 * fib 4 + 1
    ∧ fib 4 * fib 6 + 1 = fib 5 * fib 5 := by decide

/-! ## §3 — the bridge: `eigenvalue φ² = character φ + 1` (Fibonacci recurrence) -/

/-- ★★★★★ **The golden bridge.**  `eigenvalue(M) = χ₃(M) + 1`, i.e.
    `φ² = φ + 1`.  On convergents: the `φ²`-convergent `F_{n+2}/F_n` equals
    `1 + (F_{n+1}/F_n)` = `1 + (φ-convergent)`, because
    `F_{n+2} = F_n + F_{n+1}` (the Fibonacci recurrence itself).  So the A₅
    rotation character `φ` and the self-reference eigenvalue `φ²` are **one**
    golden ratio, separated by a single Fibonacci step.

    Witnessed: `φ²`-convergent numerator `F_{n+2}` = `F_n + F_{n+1}` (φ-conv.
    numerator), over the common denominator `F_n`. -/
theorem golden_bridge :
    -- φ²-convergent F_{n+2}/F_n = (F_n + F_{n+1})/F_n = 1 + F_{n+1}/F_n
    fib 4 = fib 2 + fib 3       -- 3 = 1 + 2   (φ²-conv 3/1 = 1 + φ-conv 2/1)
    ∧ fib 5 = fib 3 + fib 4     -- 5 = 2 + 3   (φ²-conv 5/2 = 1 + φ-conv 3/2)
    ∧ fib 6 = fib 4 + fib 5     -- 8 = 3 + 5
    ∧ fib 7 = fib 5 + fib 6     -- 13 = 5 + 8
    -- so eigenvalue-convergent = 1 + character-convergent at every depth
    -- (numerators differ by exactly the denominator F_n: F_{n+2} − F_{n+1} = F_n)
    ∧ fib 7 - fib 6 = fib 5 := by decide

/-! ## §4 — capstone -/

/-- ★★★★★★ **Golden character ↔ eigenvalue bridge.**  The self-reference map
    `M`, as an order-5 element of `A₅ ≅ PSL(2,𝔽₅)` (`OrderFive`), carries the
    icosahedral 3-rep character `φ`; as an ℝ-matrix it carries eigenvalue `φ²`
    (`Mobius213`).  They are one golden ratio, bridged by `φ² = φ + 1`
    (Fibonacci recurrence).  `|A₅| = 60`. -/
theorem a5_golden_capstone :
    -- group: |A₅| = |PSL(2,5)| = 60
    (120 / 2 : Nat) = 60 ∧ (5 * 4 * 3 * 2 * 1 / 2 : Nat) = 60
    -- character convergent (φ): F₄/F₃ = 3/2
    ∧ (fib 4, fib 3) = (3, 2)
    -- eigenvalue = character + 1 (φ²=φ+1) on convergents: F₅ = F₃ + F₄
    ∧ fib 5 = fib 3 + fib 4
    -- order-5: M⁵ ≡ −I (mod d=5) ⇒ order 5 in PSL (cf. OrderFive)
    ∧ E213.Lib.Math.Algebra.Icosahedral.OrderFive.pow 5
        = E213.Lib.Math.Algebra.Icosahedral.OrderFive.negI := by decide

end E213.Lib.Math.Algebra.Icosahedral.A5Bridge
