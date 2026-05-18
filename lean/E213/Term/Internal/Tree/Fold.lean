import E213.Term.Internal.Tree

/-!
# Term.Internal.Tree.Fold — catamorphism on Tree (Tree level)

`Tree.fold` — generic structural recursion into `α` with base values
and a binary combiner.  Raw-level lift (`Raw.fold` + slash
compatibility) lives in `Theory/Raw/Fold.lean`.

**WARNING — axiom compliance (AXIOM.md §3)**: `Tree.fold` does not
require symmetry of `combine` at the type level.  Asymmetric combines
make the result depend on the canonical ordering of `Tree` (an
encoding artifact, not an axiom).  Every use should verify
symmetry; the Raw-level `fold_slash` documents this assumption.
-/

namespace E213.Term.Internal

def Tree.fold {α : Type}
    (fa fb : α) (fc : α → α → α) : Tree → α
  | .a         => fa
  | .b         => fb
  | .slash x y => fc (Tree.fold fa fb fc x) (Tree.fold fa fb fc y)

end E213.Term.Internal
