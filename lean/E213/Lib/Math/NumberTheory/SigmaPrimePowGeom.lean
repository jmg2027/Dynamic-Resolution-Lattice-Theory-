import E213.Lib.Math.NumberTheory.GeometricSeries

/-!
# The divisor-power-sum over a prime power: geometric closed form (∅-axiom)

`σ_m(p^k) = Σ_{i=0}^{k} (p^i)^m = Σ_{i=0}^{k} p^{mi}` is a geometric series with ratio `p^m`,
so it has the closed form `(p^m − 1)·σ_m(p^k) = p^{m(k+1)} − 1` (the `D=p^m` Brahmagupta /
geometric identity).  Built on `geom_sum` + the new `ipow_mul` exponent law.
-/

namespace E213.Lib.Math.NumberTheory.SigmaPrimePowGeom

open E213.Lib.Math.NumberTheory.GeometricSeries (sumZ sumZ_succ geom_sum)
open E213.Lib.Math.NumberTheory.DiffPowDvd (ipow ipow_mul)

/-- `sumZ` respects pointwise equality of the summand. -/
theorem sumZ_congr (n : Nat) (f g : Nat → Int) (h : ∀ i, f i = g i) :
    sumZ n f = sumZ n g := by
  induction n with
  | zero => rfl
  | succ k ih => rw [sumZ_succ, sumZ_succ, ih, h k]

/-- ★★ **Geometric closed form for the prime-power divisor-power-sum**:
    `(p^m − 1)·(Σ_{i=0}^{k} p^{m·i}) = p^{m·(k+1)} − 1`.  The sum `Σ_{i≤k} (p^i)^m = σ_m(p^k)`
    is geometric with ratio `p^m`; this is its cleared closed form (∅-axiom). -/
theorem sigma_prime_pow_geom (p : Int) (m k : Nat) :
    (ipow p m - 1) * sumZ (k + 1) (fun i => ipow p (m * i)) = ipow p (m * (k + 1)) - 1 := by
  rw [sumZ_congr (k + 1) (fun i => ipow p (m * i)) (fun i => ipow (ipow p m) i)
        (fun i => ipow_mul p m i),
      geom_sum (ipow p m) k, ← ipow_mul p m (k + 1)]

end E213.Lib.Math.NumberTheory.SigmaPrimePowGeom
