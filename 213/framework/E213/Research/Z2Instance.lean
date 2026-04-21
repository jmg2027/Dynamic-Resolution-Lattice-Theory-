import E213.Meta.SelfRecognising
import E213.Research.ZSqrt2
import E213.Research.ZSqrt2Domain

/-!
# Research: `Z2 = ℤ[√-2]` as `R4Codomain` instance

Same pattern as `ZIInstance` — adding a new R1–R4 witness is
now a single `instance R4Codomain α` declaration.
-/

namespace E213.Research

open E213.Meta E213.Research.Z2

instance : R4Codomain Z2 where
  base_a := Z2.I
  base_b := Z2.negI
  combine := Z2.mul
  combine_comm := mul_comm
  base_a_ne_zero := by intro h; cases h
  base_b_ne_zero := by intro h; cases h
  no_zero_div := no_zero_div
  conj := Z2.conj
  conj_involution := conj_conj
  conj_ne_id := conj_ne_id
  conj_dist := conj_mul
  conj_swap_a := conj_I
  conj_swap_b := conj_negI

end E213.Research
