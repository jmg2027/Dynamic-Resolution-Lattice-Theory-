import E213.Term.Tree
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold

/-!
# Theory.Raw.FoldSwap — fold's behaviour under Raw.swap

Two Raw-level lifts of Tree-level theorems for how `Raw.fold`
transforms under `Raw.swap`:

  * `Raw.fold_signed_swap` — for the signed lens (base 1 / -1,
    combine = +), swap acts as integer negation.  Tree-level
    statement: `Tree.fold_signed_swap`
    (`Term/Internal/Tree/Signed.lean`).
  * `Raw.fold_swap_hom` — generic: for any base-swapping
    homomorphism `conj` that distributes over a symmetric
    `combine`, `Raw.fold` on `Raw.swap` equals `conj` applied
    to `Raw.fold`.  Tree-level statement: `Tree.fold_swap_hom`
    (`Term/Internal/Tree/Hom.lean`).

 +
`Theory/Raw/Hom.lean`.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

protected theorem Raw.fold_signed_swap (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r :=
  Tree.fold_signed_swap r.val r.property

protected theorem Raw.fold_swap_hom {α : Type}
    (ba bb : α) (c : α → α → α) (conj : α → α)
    (h_ba : conj ba = bb) (h_bb : conj bb = ba)
    (h_dist : ∀ u v, conj (c u v) = c (conj u) (conj v))
    (h_comm : ∀ u v, c u v = c v u) (r : Raw) :
    Raw.fold ba bb c (Raw.swap r) = conj (Raw.fold ba bb c r) :=
  Tree.fold_swap_hom ba bb c conj h_ba h_bb h_dist h_comm r.val r.property

end E213.Theory
