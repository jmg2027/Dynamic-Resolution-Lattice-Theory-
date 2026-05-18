import E213.Term.Internal.Tree.Hom
import E213.Meta.Int213.Core

/-!
# Term.Internal.Tree.Signed — fold_signed_swap (Tree level)

Specialisation of `Tree.fold_swap_hom` for the signed-Lens instance:
`base_a = 1`, `base_b = -1`, `combine = (· + ·)`, `conj = (-·)`.
This is the "swap = integer negation" Tree-level identity.

Raw lift in `Theory/Raw/Signed.lean`.  ∅-axiom; Meta.Int213 is
ring-independent so Term can rely on it.
-/

namespace E213.Term.Internal

open E213.Meta.Int213 (neg_add add_comm)

theorem Tree.fold_signed_swap :
    ∀ t : Tree, t.canonical = true →
    Tree.fold (1 : Int) (-1) (· + ·) (Tree.swap t)
      = - Tree.fold (1 : Int) (-1) (· + ·) t :=
  Tree.fold_swap_hom (1 : Int) (-1) (· + ·) (fun n => -n)
    (by decide) (by decide)
    (fun u v => neg_add u v)
    (fun u v => add_comm u v)

end E213.Term.Internal
