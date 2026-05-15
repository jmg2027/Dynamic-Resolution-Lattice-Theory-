import E213.Term.Tree
import E213.Theory.Raw.Core

/-!
# Theory.Raw.Swap: Raw-level swap automorphism

Tree-level `swap` (def + canonical/involutivity proofs) lives in
`Term/Internal/Tree/Swap.lean`.  This file lifts that machinery to
the canonical-form subtype `Raw`.

`Raw.swap_swap` is Theorem 3.2 of the paper.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

protected def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩

protected theorem Raw.swap_a : Raw.swap Raw.a = Raw.b := rfl
protected theorem Raw.swap_b : Raw.swap Raw.b = Raw.a := rfl

protected theorem Raw.swap_swap (r : Raw) : Raw.swap (Raw.swap r) = r := by
  apply Subtype.ext
  exact Tree.swap_swap r.val r.property

/-- Raw.swap is injective.  Follows directly from involutivity. -/
protected theorem Raw.swap_injective {x y : Raw} (h : Raw.swap x = Raw.swap y) : x = y := by
  have hswap : Raw.swap (Raw.swap x) = Raw.swap (Raw.swap y) :=
    congrArg Raw.swap h
  rw [Raw.swap_swap, Raw.swap_swap] at hswap
  exact hswap

end E213.Theory
