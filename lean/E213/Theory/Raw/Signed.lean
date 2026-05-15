import E213.Term.Internal.Tree.Signed
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold

/-!
# Theory.Raw.Signed: Raw-level fold_signed_swap (swap as negation)

The signed Lens (base_a=1, base_b=-1, combine=+) realises swap as
integer negation.  Used by Lens / App layers.

Tree-level statement (`Tree.fold_signed_swap`) lives in
`Term/Internal/Tree/Signed.lean`.
-/

namespace E213.Theory

open E213.Term.Internal

protected theorem Raw.fold_signed_swap (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r :=
  Tree.fold_signed_swap r.val r.property

end E213.Theory
