import E213.Meta.SelfRecognising
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIHom
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2Domain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtDomain
import E213.Meta.Tactic.DeriveConjugationCodomain

/-!
# CayleyDickson.Integer.ConjugationInstances — `ConjugationCodomain`
witnesses for the integer rings ZI / Z2 / ZOmega / ZSqrt D

Four concrete `ConjugationCodomain` witnesses, demonstrating the
three-tier codomain spec (`CommBinaryCodomain` +
`NonVanishingCodomain` + `ConjugationCodomain`) admits multiple
non-isomorphic integer rings:

  - **ZI** = ℤ[i]     — Gaussian integers, diagonal norm a² + b²
  - **Z2** = ℤ[√-2]   — diagonal norm a² + 2b²
  - **ZOmega** = ℤ[ω] — Eisenstein integers, cross-term norm
                        a² − ab + b² (structurally distinct)
  - **ZSqrt D** = ℤ[√-D] — parametric family; one generic
                  `conjugation_of_pos` witness + one-line concrete
                  instances for `D = 3, 5, 7`

The `derive_conjugation_codomain` elab discovers the required
lemmas by naming convention and synthesises the 13-field instance.

 from four singleton files
(`ZIInstance`, `Z2Instance`, `ZOmegaInstance`, `ZSqrtInstance`).
-/

open E213.Tactic

namespace _ZIScope
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI
derive_conjugation_codomain ZI with_bases I negI
end _ZIScope

namespace _Z2Scope
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2.Z2
derive_conjugation_codomain Z2 with_bases I negI
end _Z2Scope

namespace _ZOmegaScope
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
derive_conjugation_codomain ZOmega with_bases Omega Omega2
end _ZOmegaScope

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt.ZSqrt
open E213.Meta.SelfRecognising

/-- Generic `ConjugationCodomain` witness for `ZSqrt D` when `D > 0`. -/
def conjugation_of_pos {D : Int} (hD : 0 < D) :
    ConjugationCodomain (ZSqrt D) where
  base_a          := ZSqrt.I
  base_b          := ZSqrt.negI
  combine         := ZSqrt.mul
  combine_comm    := ZSqrt.mul_comm
  base_a_ne_zero  := by intro h; cases h
  base_b_ne_zero  := by intro h; cases h
  no_zero_div     := ZSqrt.no_zero_div hD
  conj            := ZSqrt.conj
  conj_involution := ZSqrt.conj_conj
  conj_ne_id      := ZSqrt.conj_ne_id
  conj_dist       := ZSqrt.conj_mul
  conj_swap_a     := ZSqrt.conj_I
  conj_swap_b     := ZSqrt.conj_negI

/-- `ℤ[√-3]`. -/
instance : ConjugationCodomain (ZSqrt 3) := ZSqrt.conjugation_of_pos (by decide)

/-- `ℤ[√-5]`. -/
instance : ConjugationCodomain (ZSqrt 5) := ZSqrt.conjugation_of_pos (by decide)

/-- `ℤ[√-7]`. -/
instance : ConjugationCodomain (ZSqrt 7) := ZSqrt.conjugation_of_pos (by decide)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt
