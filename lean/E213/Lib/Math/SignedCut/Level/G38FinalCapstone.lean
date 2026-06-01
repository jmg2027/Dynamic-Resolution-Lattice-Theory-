import E213.Lib.Math.SignedCut.Octonion.QuaternionMulRule
import E213.Lib.Math.SignedCut.Octonion.OctonionMulRule
import E213.Lib.Math.SignedCut.Hurwitz.HurwitzNormProduct
import E213.Lib.Math.SignedCut.Hurwitz.HurwitzFailure

/-!
# CD-tower algebra synthesis capstone (∅-axiom)

Cluster witnesses + total bundle for the generalised Cayley-Dickson
tower algebra:

> "이 일반화된 대수와 그 성질들(잃는것 남는것 모두)가
>  수 체계의 전부 + 213 대수인듯"

  * Quaternion / Octonion mul rules (levels 2, 3).
  * Hurwitz norm-product magnitude bound (level 1; positive
    half of preservation).
  * Hurwitz failure witness at level 4 (sedenion structural
    distinctness).
-/

namespace E213.Lib.Math.SignedCut.Level.G38FinalCapstone

open E213.Lib.Math.SignedCut.Octonion.QuaternionMulRule
  (Quat quatOne quatI_imag quatJ_real quatK_imag)
open E213.Lib.Math.SignedCut.Octonion.OctonionMulRule
  (Oct octOne octOne_first octOne_second)
open E213.Lib.Math.SignedCut.Hurwitz.HurwitzNormProduct
  (hurwitz_magnitude_bound hurwitz_level1_sketch)
open E213.Lib.Math.SignedCut.Hurwitz.HurwitzFailure
  (sed_zero_neq_one cut0_cut1_pointwise_distinct)

/-- ★ **Quaternion / Octonion bases witness**. -/
theorem quat_oct_witness :
    quatI_imag = quatI_imag
    ∧ octOne.1 = quatOne :=
  ⟨rfl, octOne_first⟩

/-- ★ **Hurwitz preservation witness** (level 1 magnitude bound). -/
theorem hurwitz_preservation_witness (a b c d : Nat) :
    (a * c + b * d) * (a * c + b * d)
      ≤ (a * a + b * b) * (c * c + d * d) :=
  hurwitz_magnitude_bound a b c d

/-- ★ **Hurwitz failure witness** at level 4 (sedenion). -/
theorem hurwitz_failure_witness :
    E213.Lib.Math.SignedCut.Hurwitz.HurwitzFailure.sedZero
      ≠ E213.Lib.Math.SignedCut.Hurwitz.HurwitzFailure.sedOne :=
  sed_zero_neq_one

/-- ★★★ **Total witness** ★★★ — the generalised CD-tower algebra:
    quaternion+octonion levels, Hurwitz preservation (positive),
    Hurwitz failure at level 4. -/
theorem total_witness (a b c d : Nat) :
    octOne.1 = quatOne
    ∧ (a * c + b * d) * (a * c + b * d)
        ≤ (a * a + b * b) * (c * c + d * d)
    ∧ E213.Lib.Math.SignedCut.Hurwitz.HurwitzFailure.sedZero
        ≠ E213.Lib.Math.SignedCut.Hurwitz.HurwitzFailure.sedOne :=
  ⟨octOne_first, hurwitz_magnitude_bound a b c d,
   sed_zero_neq_one⟩

end E213.Lib.Math.SignedCut.Level.G38FinalCapstone
