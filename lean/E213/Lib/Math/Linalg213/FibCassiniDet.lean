import E213.Lib.Math.Cauchy.OrbitDimension
import E213.Lib.Math.Linalg213.DetN

/-!
# The orbit's conserved unit, as a determinant

The general `n×n` determinant (`Linalg213.DetN`) is built toward the C-finite **Hadamard
product** (whose monic annihilator is a resultant = a determinant).  This file closes the
loop at the base size `n = 2`: the determinant of the Fibonacci **Casoratian** (companion
power) matrix is exactly the orbit-dimension-2 witness's **Cassini cross-determinant**, the
conserved unit `(−1)ⁿ⁺¹`.

So the determinant program's `2×2` base *is* the orbit's conserved unit — the same
unimodular `det = ±1` the number-tower founding reads as `ℚ`'s lowest-terms / the shared
unit `det = NS − NT = 1` (`Mobius213.Px.PnFibonacciUniversal.det_pn_universal`,
`det Qⁿ = unit`).  The period-2 sign flip is the count-Lens binary axis (negation = the
`PairCompletion` swap).  "Monic = the preserved unit" made concrete: `det 2` on the orbit
returns the unit, on the difference axis.

All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.FibCassiniDet

open E213.Lib.Math.Cauchy.OrbitDimension (fibZ cassini_fibZ_zero cassini_fibZ_step)
open E213.Lib.Math.Linalg213.DetN (det det_two altSign)

/-- The Fibonacci **Casoratian** matrix at step `n`: `M i j = fibₙ₊ᵢ₊ⱼ`, i.e. the `2×2`
    window `[[fibₙ, fibₙ₊₁], [fibₙ₊₁, fibₙ₊₂]]` — the companion-matrix power `Qⁿ` read off
    the orbit. -/
def fibCas (n : Nat) : Nat → Nat → Int :=
  fun i j => fibZ (n + i + j)

/-- The Cassini cross-determinant in closed form: `fibₙ·fibₙ₊₂ − fibₙ₊₁² = (−1)ⁿ⁺¹ = altSign (n+1)`.
    The orbit's conserved unit, pinned for every `n` (base `cassini_fibZ_zero` + period-2 step). -/
theorem cassini_fibZ_eq_altSign (n : Nat) :
    fibZ n * fibZ (n + 2) - fibZ (n + 1) * fibZ (n + 1) = altSign (n + 1) := by
  induction n with
  | zero =>
    show fibZ 0 * fibZ 2 - fibZ 1 * fibZ 1 = altSign 1
    rw [cassini_fibZ_zero]
    rfl
  | succ k ih =>
    show fibZ (k + 1) * fibZ (k + 3) - fibZ (k + 2) * fibZ (k + 2) = altSign (k + 2)
    rw [cassini_fibZ_step k, ih]
    rfl

/-- ★ **The orbit's Casoratian determinant is the conserved unit.**  `det 2 (fibCas n) = (−1)ⁿ⁺¹`.
    The general determinant, at its `2×2` base, returns the C-finite orbit's shared unit. -/
theorem fibCas_det_eq_unit (n : Nat) : det 2 (fibCas n) = altSign (n + 1) := by
  rw [det_two]
  show fibZ n * fibZ (n + 2) - fibZ (n + 1) * fibZ (n + 1) = altSign (n + 1)
  exact cassini_fibZ_eq_altSign n

end E213.Lib.Math.Linalg213.FibCassiniDet
