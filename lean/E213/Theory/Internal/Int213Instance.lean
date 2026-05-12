import E213.Theory.Internal.Int213
import E213.Theory.Internal.Algebra213

/-!
# `Int` as a `CommRing213` instance

Provides Int as the base instance for the `Ring213` / `CommRing213`
hierarchy.  All ring axioms are PURE projections of `Int213.*`.

This enables generic Ring213 lemmas (`add_4_swap_mid`, `add_left_comm`,
`zero_mul`, `neg_mul`, etc.) to be specialised to `Int` directly,
rather than requiring `Int213.*` qualification at every call site.
-/

namespace E213.Theory.Internal

open E213.Theory.Internal.Algebra213
open E213.Theory.Internal.Int213

instance : Ring213 Int where
  add_assoc    := Int213.add_assoc
  add_comm     := Int213.add_comm
  add_zero     := Int.add_zero
  add_left_neg := Int213.add_left_neg
  mul_assoc    := Int213.mul_assoc
  add_mul      := Int213.add_mul
  mul_add      := Int213.mul_add

instance : CommRing213 Int where
  mul_comm := Int213.mul_comm

end E213.Theory.Internal
