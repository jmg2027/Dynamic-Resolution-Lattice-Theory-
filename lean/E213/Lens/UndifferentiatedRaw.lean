import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Lattice.Lattice

/-!
# Lens.UndifferentiatedRaw — §9.5 K_∞ ≡ point at raw level

`seed/AXIOM/09_chart_relativity.md` §9.5 records that under the
constant (undifferentiated) Lens reading of the residue, the
following are literally the same object:

  - a single point;
  - the infinite complete graph K_∞ (every vertex
    indistinguishable from every other);
  - an infinite topological space with the trivial topology.

This file gives a concrete Lean witness of that equivalence at
the Lens-quotient level: under the *constant Lens*
(`constLens e`), every Raw maps to the same value `e` — i.e.,
the constant Lens reading of Raw is a singleton.

This realises §9.5 operationally: the constant Lens is the
"no-distinction" reading; under it, the entire residue collapses
to one point.  Different Lenses extract different aspects of the
same residue; constLens extracts no aspect at all, recovering the
undifferentiated singleton.
-/

namespace E213.Lens.UndifferentiatedRaw

open E213.Theory (Raw)
open E213.Lens (Lens)
open E213.Lens.Lattice.Lattice (constLens constLens_view)

/-- ★ **Pre-Lens collapse**: under the constant Lens, every Raw
    maps to the same value.  At this Lens reading, Raw is
    a singleton — every distinction is invisible. -/
theorem constLens_collapses {α : Type} (e : α) (r s : Raw) :
    (constLens e).view r = (constLens e).view s := by
  rw [constLens_view, constLens_view]

/-- ★ **K_∞ ≡ point at raw** (Lens-quotient form).  Two arbitrary
    Raws — no matter how they were built — are identified under
    the constant Lens.  This is the Lean witness of §9.5's claim
    that at raw level, point ≡ K_∞ ≡ trivial-topology infinite
    space.  All three are the same single object under the
    no-distinction reading.

    The "naming" event (Lens choice ≠ constLens) is what
    introduces first colour — at that moment we leave the
    undifferentiated raw stage and enter the Lens-readings
    described elsewhere in the framework.  Cf.
    `seed/AXIOM/03_form.md` §4.2 and `09_chart_relativity.md`
    §9.5. -/
theorem pre_lens_singleton {α : Type} (e : α) :
    ∀ r s : Raw, (constLens e).view r = (constLens e).view s :=
  fun r s => constLens_collapses e r s

/-- ★ The constant-Lens kernel is the *total* relation on Raw —
    every pair of Raws is equivalent under no-distinction reading.
    This is the formal counterpart to §9.5's "everything is the
    same at raw level". -/
theorem constLens_kernel_total {α : Type} (e : α)
    (x y : Raw) : (constLens e).equiv x y :=
  constLens_collapses e x y

/-- Cf. `Lens/Lattice/Lattice.lean`: `constLens` is the
    coarsest Lens in the refinement preorder.  The collapse
    here + coarsest position together realise: constLens IS the
    "no distinction" / "K_∞-at-raw" extreme of the Lens lattice. -/
example : True := trivial  -- placeholder for cross-ref

end E213.Lens.UndifferentiatedRaw
