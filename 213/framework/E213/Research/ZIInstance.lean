import E213.Meta.SelfRecognising
import E213.Research.ZI
import E213.Research.ZIDomain
import E213.Research.ZIHom

/-!
# Research: `ZI` as `R4Codomain` instance

Provides the spec instance.  By the typeclass hierarchy
`R4Codomain extends R3Codomain extends R12Codomain`, this
single `instance` declaration gives ZI access to:
- `R12Codomain.specLens` (generic Lens)
- `R3Codomain.specLens_nonVanishing` (R3, generic)
- `R4Codomain.specLens_swapMatching` (R4, generic)
-/

namespace E213.Research

open E213.Meta E213.Research.ZI

instance : R4Codomain ZI where
  base_a := ZI.I
  base_b := ZI.negI
  combine := ZI.mul
  combine_comm := mul_comm
  base_a_ne_zero := by intro h; cases h
  base_b_ne_zero := by intro h; cases h
  no_zero_div := no_zero_div
  conj := ZI.conj
  conj_involution := conj_conj
  conj_ne_id := conj_ne_id
  conj_dist := conj_mul
  conj_swap_a := conj_I
  conj_swap_b := conj_negI

end E213.Research
