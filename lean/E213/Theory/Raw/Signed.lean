import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold
import E213.Theory.Raw.Hom
import E213.Meta.Int213.Core

/-!
# Theory.Raw.Signed: fold_signed_swap — swap as negation

The signed Lens (base_a=1, base_b=-1, combine=+) realises swap
as integer negation.  Used by Lens / App layers.
-/

namespace E213.Theory.Internal

open E213.Meta.Int213 (neg_add add_comm)

theorem Tree.fold_signed_swap :
    ∀ t : Tree, t.canonical = true →
    Tree.fold (1 : Int) (-1) (· + ·) (Tree.swap t)
      = - Tree.fold (1 : Int) (-1) (· + ·) t :=
  Tree.fold_swap_hom (1 : Int) (-1) (· + ·) (fun n => -n)
    (by decide) (by decide)
    (fun u v => neg_add u v)
    (fun u v => add_comm u v)

end E213.Theory.Internal

namespace E213.Theory

open E213.Theory.Internal

theorem Raw.fold_signed_swap (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r :=
  Tree.fold_signed_swap r.val r.property

end E213.Theory
