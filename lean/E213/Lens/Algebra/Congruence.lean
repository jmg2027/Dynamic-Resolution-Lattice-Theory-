import E213.LensCore

/-!
# KernelCongruence: Lens kernel is a slash-congruence

**Theorem**: `L.equiv` is a **slash-congruence** on Raw —
if x ~ x' and y ~ y' (when slash is defined) then slash(x, y)
~ slash(x', y').

This shows that the kernel of a Lens must be not merely an
equivalence relation but one that is compatible with slash.

Positive counterpart to the negative result in `NoDepthParity.lean`
(depth parity is not a slash-congruence).

## Significance

Since every Lens kernel is a congruence, the answer to "which
partitions can be realized by a Lens?" is "**slash-compatible
partitions**".

This theorem + `NoDepthParity` → the space of Lens kernels is a
**strict subset** of the space of equivalences (not every equivalence
is slash-compatible).
-/

namespace E213.Lens.Algebra.Congruence

open E213.Theory E213.Lens

/-- **Lens kernel congruence**: if x ~ x' and y ~ y' then
    the slash values are also equivalent.  `hsym` requires
    symmetry at the AXIOM level. -/
theorem Lens.equiv_slash_congruence {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x x' y y' : Raw) (hx : x ≠ y) (hx' : x' ≠ y')
    (hxx' : L.equiv x x') (hyy' : L.equiv y y') :
    L.equiv (Raw.slash x y hx) (Raw.slash x' y' hx') := by
  show L.view (Raw.slash x y hx) = L.view (Raw.slash x' y' hx')
  have hf1 : L.view (Raw.slash x y hx)
               = L.combine (L.view x) (L.view y) :=
    Raw.fold_slash _ _ _ hsym x y hx
  have hf2 : L.view (Raw.slash x' y' hx')
               = L.combine (L.view x') (L.view y') :=
    Raw.fold_slash _ _ _ hsym x' y' hx'
  rw [hf1, hf2]
  have hxx'' : L.view x = L.view x' := hxx'
  have hyy'' : L.view y = L.view y' := hyy'
  rw [hxx'', hyy'']

end E213.Lens.Algebra.Congruence
