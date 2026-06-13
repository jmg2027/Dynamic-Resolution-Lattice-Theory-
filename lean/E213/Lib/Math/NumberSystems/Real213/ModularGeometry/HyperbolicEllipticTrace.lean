/-!
# Hyperbolic and elliptic — the φ and π faces as the sign of the discriminant

The φ↔π duality is the **hyperbolic↔elliptic** split of `SL(2, ℤ)`, and the bridge between them
is the Wick rotation `cos(iθ) = cosh θ` (`θ ↦ iθ` sends the elliptic trace `2cos θ ∈ (−2,2)` to
the hyperbolic trace `2cosh t > 2`).  A `2×2` integer matrix of determinant `1` is classified by
its **discriminant** `Δ = tr² − 4·det = tr² − 4`:

  * `Δ > 0` — **hyperbolic**: real eigenvalues `(tr ± √Δ)/2`, a *scaling* (the φ / Fibonacci
    direction, `2cosh`).  The golden matrix `G = [[2,1],[1,1]]` has `tr = 3`, `Δ = 5`,
    eigenvalues `φ², φ⁻²` — the residue's self-reference iterator (`Mobius213`).
  * `Δ < 0` — **elliptic**: complex eigenvalues on the unit circle, a *rotation* (the π /
    circle direction, `2cos`).  `S = [[0,−1],[1,0]]` (order 4) and `U = [[1,−1],[1,0]]`
    (order 6) are the elliptic generators (`ModularElliptic`: `PSL(2,ℤ) = ℤ₂ * ℤ₃`).

So the **sign of `Δ = tr² − 4`** is the φ(hyperbolic)/π(elliptic) split, and the Wick rotation
`θ ↦ iθ` is exactly the flip of that sign (`2cos θ` with `Δ = 4cos²θ − 4 ≤ 0` ↦ `2cosh t` with
`Δ = 4cosh²t − 4 ≥ 0`).  This file proves the trichotomy data ∅-axiom on the concrete
generators, unifying the repo's golden form (disc `5`, `GoldenFormMarkov`) and elliptic orders
(`{4,6}`, `ModularElliptic`) under one discriminant-sign reading.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace

/-- A `2×2` integer matrix `[[a,b],[c,d]]`. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq

namespace Mat2

/-- Matrix product. -/
def mul (m n : Mat2) : Mat2 :=
  ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d,
   m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d⟩

instance : Mul Mat2 := ⟨mul⟩

/-- Determinant `ad − bc`. -/
def det (m : Mat2) : Int := m.a * m.d - m.b * m.c
/-- Trace `a + d`. -/
def tr (m : Mat2) : Int := m.a + m.d
/-- Discriminant of the characteristic polynomial `x² − tr·x + det`: `tr² − 4·det`. -/
def disc (m : Mat2) : Int := tr m * tr m - 4 * det m

/-- Identity. -/
def I : Mat2 := ⟨1, 0, 0, 1⟩
/-- `−I` (the central Cassini element). -/
def negI : Mat2 := ⟨-1, 0, 0, -1⟩
/-- The golden / Fibonacci iterator `[[2,1],[1,1]]` (hyperbolic). -/
def G : Mat2 := ⟨2, 1, 1, 1⟩
/-- The order-4 elliptic generator `S = [[0,−1],[1,0]]`. -/
def S : Mat2 := ⟨0, -1, 1, 0⟩
/-- The order-6 elliptic generator `U = [[1,−1],[1,0]]`. -/
def U : Mat2 := ⟨1, -1, 1, 0⟩

end Mat2

open Mat2

/-! ## §1 — the golden matrix is hyperbolic (Δ = 5 > 0) -/

/-- ★★★ **The golden iterator is hyperbolic.**  `det G = 1`, `tr G = 3` (= `NS`, spatial
    atomicity), and the discriminant `Δ = tr² − 4 = 5` (= `NS + NT`) is **positive** — real
    eigenvalues `φ², φ⁻²`, a scaling.  The φ face of the residue (`Mobius213`). -/
theorem golden_hyperbolic : det G = 1 ∧ tr G = 3 ∧ disc G = 5 ∧ 0 < disc G := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2 — the elliptic generators (Δ < 0), orders 4 and 6 -/

/-- ★★★ **`S` is elliptic of order 4.**  `det S = 1`, `tr S = 0`, `Δ = −4 < 0` (no real
    eigenvalues — a rotation), `S² = −I`, `S⁴ = I`.  The order-4 (Gaussian) axis. -/
theorem S_elliptic_order4 :
    det S = 1 ∧ tr S = 0 ∧ disc S = -4 ∧ disc S < 0
    ∧ S * S = negI ∧ S * S * S * S = I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★ **`U` is elliptic of order 6.**  `det U = 1`, `tr U = 1`, `Δ = −3 < 0`, `U⁶ = I`,
    `U³ = −I` (the central Cassini element).  The order-6 (Eisenstein) axis. -/
theorem U_elliptic_order6 :
    det U = 1 ∧ tr U = 1 ∧ disc U = -3 ∧ disc U < 0
    ∧ U * U * U = negI ∧ U * U * U * U * U * U = I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §3 — the Wick split: the φ/π faces are the two signs of the discriminant -/

/-- ★★★ **The discriminant sign is the φ/π (hyperbolic/elliptic) split.**  The golden face has
    `Δ = +5 > 0` (hyperbolic, `2cosh`, scaling); the elliptic faces `S, U` have `Δ = −4, −3 < 0`
    (rotation, `2cos`).  The Wick rotation `θ ↦ iθ` (`cos(iθ) = cosh θ`) is exactly this flip of
    `Δ`'s sign — the single continuous bridge between the residue's φ and π faces. -/
theorem wick_discriminant_split :
    0 < disc G ∧ disc S < 0 ∧ disc U < 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The golden discriminant is `NS + NT = 5`; the golden trace is `NS = 3`.  The hyperbolic
    face carries the repo's spatial/temporal atomicity numerics (`GoldenFormMarkov` disc 5). -/
theorem golden_trace_disc_numerics : tr G = 3 ∧ disc G = 5 := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace
