import E213.Lib.Math.CayleyDickson.Integer.ZI
import E213.Meta.Int213.Core

/-!
# `ZI.conj` is a ring homomorphism

Proves `ZI.conj (u * v) = ZI.conj u * ZI.conj v` for Gaussian
integers, plus `ZI.conj I = ZI.negI` (and conversely). These
three facts are the hypotheses needed to apply
`Raw.fold_swap_hom` to obtain R4 for `ziLens`.

∅-axiom — uses `Int213.{neg_mul, mul_neg, neg_add}` instead of
propext-bearing Lean-core counterparts.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZI.ZI


/-- `conj` sends `I` to `-I`. -/
theorem conj_I : ZI.conj I = negI := by
  show (⟨0, -1⟩ : ZI) = ⟨0, -1⟩
  rfl

/-- `conj` sends `-I` to `I`. -/
theorem conj_negI : ZI.conj negI = I := by
  apply ext
  · show (0 : Int) = 0; rfl
  · show -(-1 : Int) = 1; exact Int.neg_neg _

/-- `conj` distributes over Gaussian multiplication. -/
theorem conj_mul (u v : ZI) : conj (u * v) = conj u * conj v := by
  apply ext
  · -- real part
    show u.re * v.re - u.im * v.im
       = u.re * v.re - (-u.im) * (-v.im)
    have h : (-u.im) * (-v.im) = u.im * v.im := by
      rw [E213.Theory.Internal.Int213.neg_mul,
          E213.Theory.Internal.Int213.mul_neg, Int.neg_neg]
    rw [h]
  · -- imag part
    show -(u.re * v.im + u.im * v.re)
       = u.re * (-v.im) + (-u.im) * v.re
    rw [E213.Theory.Internal.Int213.mul_neg,
        E213.Theory.Internal.Int213.neg_mul,
        ← E213.Theory.Internal.Int213.neg_add]

end E213.Lib.Math.CayleyDickson.Integer.ZI.ZI
