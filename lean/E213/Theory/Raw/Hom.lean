import E213.Term.Tree
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold

/-!
# Theory.Raw.Hom: Raw-level fold_swap_hom

For any `conj : α → α` exchanging the base values and distributing
over a symmetric `combine`, `Raw.fold` on `Raw.swap` equals `conj`
applied to `Raw.fold`.  Tree-level theorem (`Tree.fold_swap_hom`)
lives in `Term/Internal/Tree/Hom.lean`.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

protected theorem Raw.fold_swap_hom {α : Type}
    (ba bb : α) (c : α → α → α) (conj : α → α)
    (h_ba : conj ba = bb) (h_bb : conj bb = ba)
    (h_dist : ∀ u v, conj (c u v) = c (conj u) (conj v))
    (h_comm : ∀ u v, c u v = c v u) (r : Raw) :
    Raw.fold ba bb c (Raw.swap r) = conj (Raw.fold ba bb c r) :=
  Tree.fold_swap_hom ba bb c conj h_ba h_bb h_dist h_comm r.val r.property

end E213.Theory
