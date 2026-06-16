import E213.Lib.Math.NumberTheory.Norm5
import E213.Lib.Math.NumberTheory.FibZIdentities

/-!
# Golden-norm bridge: the Lucas–Fibonacci pair realizes the `ℚ(√5)` norm (∅-axiom)

Ties the `D=5` norm form (`Norm5.isNorm5neg`, `a²−5b²`) to the Fibonacci/Lucas Cassini
identity (`FibZIdentities.lucasZ_sq`, `L_m² = 5F_m² + 4(−1)ᵐ`): the pair `(L_m, F_m)` is a
ℤ[√5]-norm representation of `4·(−1)ᵐ`, i.e. the golden field's norm evaluated along the
Fibonacci recurrence.
-/

namespace E213.Lib.Math.NumberTheory.GoldenNormBridge

open E213.Lib.Math.NumberTheory.Norm5 (isNorm5neg)
open E213.Lib.Math.NumberTheory.FibZIdentities (lucasZ lucasZ_sq)
open E213.Lib.Math.Analysis.Cauchy.OrbitDimension (fibZ)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign)
open E213.Meta.Int213.PolyIntM

/-- ★ **The Lucas–Fibonacci pair realizes the `D=5` norm**: `L_m² − 5F_m² = 4·(−1)ᵐ`, so
    `4·(−1)ᵐ` is a ℤ[√5]-norm value witnessed by `(L_m, F_m)` — the golden-field norm
    (`isNorm5neg`) evaluated on the Fibonacci recurrence (Cassini at the `√5` level). -/
theorem lucas_fib_isNorm5neg (m : Nat) : isNorm5neg (4 * altSign m) :=
  ⟨lucasZ m, fibZ m, by rw [lucasZ_sq]; ring_intZ⟩

end E213.Lib.Math.NumberTheory.GoldenNormBridge
