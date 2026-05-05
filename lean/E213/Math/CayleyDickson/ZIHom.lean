import E213.Math.CayleyDickson.ZI

/-!
# Research: `ZI.conj` is a ring homomorphism

Proves `ZI.conj (u * v) = ZI.conj u * ZI.conj v` for Gaussian
integers, plus `ZI.conj I = ZI.negI` (and conversely). These
three facts are the hypotheses needed to apply
`Raw.fold_swap_hom` to obtain R4 for `ziLens`.
-/

namespace E213.Math.CayleyDickson.ZI.ZI


/-- `conj` sends `I` to `-I`. -/
theorem conj_I : ZI.conj I = negI := by
  show (⟨0, -1⟩ : ZI) = ⟨0, -1⟩
  rfl

/-- `conj` sends `-I` to `I`. -/
theorem conj_negI : ZI.conj negI = I := by
  show (⟨0, -(-1)⟩ : ZI) = ⟨0, 1⟩
  apply ext <;> simp

/-- `conj` distributes over Gaussian multiplication. -/
theorem conj_mul (u v : ZI) : conj (u * v) = conj u * conj v := by
  apply ext
  · -- real part
    show u.re * v.re - u.im * v.im
       = u.re * v.re - (-u.im) * (-v.im)
    rw [Int.neg_mul_neg]
  · -- imag part
    show -(u.re * v.im + u.im * v.re)
       = u.re * (-v.im) + (-u.im) * v.re
    rw [Int.mul_neg, Int.neg_mul, ← Int.neg_add]

end E213.Math.CayleyDickson.ZI.ZI
