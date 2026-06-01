import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyInt2
import E213.Meta.Algebra213.Core

/-! Spec-as-code entry point for `E213.Meta.Int213`.

Ring-independent Int helpers (∅-axiom Int arithmetic) +
`Ring213 Int` / `CommRing213 Int` instances.  Promoted from
`Theory.Internal/`; namespace path-aligned
to `E213.Meta.Int213` Session G.

The instance is registered here (not in `Core`) to break the
import cycle: `Algebra213.Core` depends on `Int213.Core`, so the
`Ring213 Int` instance — which depends on both — must live
downstream.
-/

namespace E213.Meta

open E213.Meta.Algebra213
open E213.Meta.Int213

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

end E213.Meta
