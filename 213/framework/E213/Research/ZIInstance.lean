import E213.Meta.SelfRecognising
import E213.Research.ZI
import E213.Research.ZIDomain
import E213.Research.ZIHom

/-!
# Research: `ZI` as `SelfRecognisingCodomain` instance

Provides the spec instance for `ZI = ℤ[i]`.  Once this builds,
the generic `Meta.SelfRecognisingCodomain.specLens (α := ZI)`
is available, plus the generic R3 (`specLens_nonVanishing`)
and R4 (`specLens_swapMatching`) theorems — no Lens-specific
boilerplate needed.
-/

namespace E213.Research

open E213.Meta E213.Research.ZI

instance : SelfRecognisingCodomain ZI where
  base_a := ZI.I
  base_b := ZI.negI
  combine := ZI.mul
  conj := ZI.conj
  base_a_ne_zero := by intro h; cases h
  base_b_ne_zero := by intro h; cases h
  combine_comm := mul_comm
  no_zero_div := no_zero_div
  conj_involution := conj_conj
  conj_ne_id := conj_ne_id
  conj_dist := conj_mul
  conj_swap_a := conj_I
  conj_swap_b := conj_negI

end E213.Research
