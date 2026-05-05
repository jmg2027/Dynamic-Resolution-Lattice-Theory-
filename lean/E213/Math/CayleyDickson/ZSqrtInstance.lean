import E213.Meta.SelfRecognising
import E213.Math.CayleyDickson.ZSqrt
import E213.Math.CayleyDickson.ZSqrtDomain

/-!
# Research: `ZSqrt D = ℤ[√-D]` `ConjugationCodomain` instances

A single generic theorem `conjugation_of_pos hD` produces the
instance for any `D` with `0 < D`.  Concrete `D = 3, 5, 7`
follow as one-line declarations.

This is the **parametric** counterpart to the per-D
`derive_conjugation_codomain` macro path: instead of generating
separate types `Z3`, `Z5`, `Z7`, we instantiate the
`ZSqrt D` family with specific `D` values.

Naming history: previously named `R4_of_pos` referring to the
"R4 axiom" in the deprecated R1–R5 frame (`seed/AXIOM.md` §9);
renamed per AXIOM.md §9.1 audit pass.
-/

namespace E213.Math.CayleyDickson.ZSqrt


open E213.Math.CayleyDickson.ZSqrt
open E213.Math.CayleyDickson.ZSqrt.ZSqrt
open E213.Meta

/-- Generic ConjugationCodomain witness for `ZSqrt D` when `D > 0`. -/
def conjugation_of_pos {D : Int} (hD : 0 < D) : ConjugationCodomain (ZSqrt D) where
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

end E213.Math.CayleyDickson.ZSqrt

namespace E213.Research

open E213.Meta

/-- `ℤ[√-3]`: `ConjugationCodomain` instance via `ZSqrt.conjugation_of_pos`. -/
instance : ConjugationCodomain (ZSqrt 3) := ZSqrt.conjugation_of_pos (by decide)

/-- `ℤ[√-5]`. -/
instance : ConjugationCodomain (ZSqrt 5) := ZSqrt.conjugation_of_pos (by decide)

/-- `ℤ[√-7]`. -/
instance : ConjugationCodomain (ZSqrt 7) := ZSqrt.conjugation_of_pos (by decide)

end E213.Research
