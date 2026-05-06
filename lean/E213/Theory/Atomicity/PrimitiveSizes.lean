import E213.Theory.Atomicity.NonDecomposable

/-!
# Primitive sizes: `{2, 3}` from the axiom

Remark 6.6(b) of PAPER.md: the atom set is read directly off the
axiom, which names exactly two sizes:

- `pairSize = 2`: the input pair (the axiom's "two objects").
- `closureSize = 3`: the first closure (pair + their relation).

Proposition 6.5 (`E213.Theory.Atomicity.NonDecomposable.non_decomposable_iff`)
confirms that these two sizes are exactly the non-decomposable
integers `≥ 2` under additive composition with parts `≥ 2`.

The two characterizations — primitive-structural (this file) and
arithmetic (NonDecomposable) — coincide on `{2, 3}`.
-/

namespace E213.Theory.Atomicity.PrimitiveSizes
open E213.Theory.Atomicity.NonDecomposable

/-- The input pair: two objects. Named by the axiom. -/
def pairSize : Nat := 2

/-- The first closure: the pair plus their relation. Named by the axiom. -/
def closureSize : Nat := 3

/-- The input pair size is non-decomposable. -/
theorem pairSize_nondecomposable : NonDecomposable pairSize :=
  (non_decomposable_iff 2).mpr (Or.inl rfl)

/-- The first closure size is non-decomposable. -/
theorem closureSize_nondecomposable : NonDecomposable closureSize :=
  (non_decomposable_iff 3).mpr (Or.inr rfl)

/-- **Coincidence of the two atom characterizations.**
    The sizes named by the primitive (`pairSize` and `closureSize`)
    are exactly the non-decomposable integers `≥ 2`. -/
theorem primitive_sizes_eq_nondecomposable (n : Nat) :
    (n = pairSize ∨ n = closureSize) ↔ NonDecomposable n :=
  (non_decomposable_iff n).symm

end E213.Theory.Atomicity.PrimitiveSizes