import E213.Meta.SelfRecognising
import E213.Math.CayleyDickson.ZSqrt
import E213.Math.CayleyDickson.ZSqrtDomain

/-!
# Research: `ZSqrt D = ℤ[√-D]` `R4Codomain` instances

A single generic theorem `R4_of_pos hD` produces the
instance for any `D` with `0 < D`.  Concrete `D = 3, 5, 7`
follow as one-line declarations.

This is the **parametric** counterpart to the per-D
`derive_r4_codomain` macro path: instead of generating
separate types `Z3`, `Z5`, `Z7`, we instantiate the
`ZSqrt D` family with specific `D` values.
-/

namespace E213.Math.CayleyDickson.ZSqrtInstance

open E213.Meta

/-- Generic R4Codomain witness for `ZSqrt D` when `D > 0`. -/
def R4_of_pos {D : Int} (hD : 0 < D) : R4Codomain (ZSqrt D) where
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

end E213.Math.CayleyDickson.ZSqrtInstance

namespace E213.Research

open E213.Meta

/-- `ℤ[√-3]`: `R4Codomain` instance via `ZSqrt.R4_of_pos`. -/
instance : R4Codomain (ZSqrt 3) := ZSqrt.R4_of_pos (by decide)

/-- `ℤ[√-5]`. -/
instance : R4Codomain (ZSqrt 5) := ZSqrt.R4_of_pos (by decide)

/-- `ℤ[√-7]`. -/
instance : R4Codomain (ZSqrt 7) := ZSqrt.R4_of_pos (by decide)

end E213.Research
