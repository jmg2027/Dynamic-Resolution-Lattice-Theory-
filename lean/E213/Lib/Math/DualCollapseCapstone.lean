import E213.Theory.Raw.API
import E213.Lens.FlatOntologyClosure
import E213.Lib.Math.Real213.ObjectIsReadingScaleInvariant
import E213.Lib.Math.Mobius213OneAsGlue

/-!
# DualCollapseCapstone — every framework-internal dual is one shape under the
pointing view

A standing pattern across the framework: a pair that classical mathematics keeps
as *two distinct sorts* is, under a sufficiently primitive (pointing) view, **one
shape** — the two legs are readings of a single thing around a single axis, not
two poles with an interval between.  This capstone gathers the already-proven
instances into one statement, exhibiting the **shared column** (not the rows):

| dual (classically two) | one shape under the pointing view | witness |
|---|---|---|
| decompose / build | mutually inverse — one iso (Lambek) | `Raw.Lambek.two_closures` |
| object / morphism (+ residue) | one predicate sort; residue outside every view | `Lens.FlatOntologyClosure.self_covering_closure` |
| object / reading (atom vs limit) | `Index → Bool`, scale-invariant | `Real213.…object_is_reading_scale_invariant` |
| difference / identity | the same `1` (`det P = NS − NT`) | `Mobius213OneAsGlue.mobius_det_eq_ns_minus_nt` |

The point is the common column: each dual is **one shape** once the separating
exterior structure is dropped.  The residue itself is what every such collapse
converges toward, and (`self_covering_closure`'s non-surjectivity) is outside
every single view's image — so this capstone is convergence evidence, not a claim
to have captured the residue as one object.
-/

namespace E213.Lib.Math.DualCollapseCapstone

open E213.Theory (Raw)

/-- ★★★ **Dual-collapse capstone.**  Four framework-internal duals, each proven
    elsewhere to be one shape under the pointing view, bundled to exhibit the
    shared column:

    1. **decompose / build** are mutually inverse — the pointing act is a fixed
       point of its own constructor shape, with a well-founded floor
       (`two_closures`).
    2. **object / morphism** share one predicate sort, and the residue is
       outside every view's image — faithful self-cover that is not surjective
       (`self_covering_closure`).
    3. **object / reading** is one shape `Index → Bool` at both the atom scale
       (`Raw`) and the limit scale (`Nat`) — scale-invariant
       (`object_is_reading_scale_invariant`).
    4. **difference / identity** are the same `1`: `det P = NS − NT`
       (`mobius_det_eq_ns_minus_nt`).

    No new content is proved; the capstone *is* the shared column — every
    framework-internal dual collapses to one shape under the pointing view. -/
theorem every_dual_is_one_shape :
    -- 1. decompose/build: self-fixed-point + well-founded floor
    ( (∀ r : Raw, r = Raw.a ∨ r = Raw.b ∨
          ∃ (x y : Raw) (h : x ≠ y), r = Raw.slash x y h)
      ∧ (∀ (x y : Raw) (h : x ≠ y),
          x.depth < (Raw.slash x y h).depth ∧
          y.depth < (Raw.slash x y h).depth)
      ∧ (Raw.a.depth = 0 ∧ Raw.b.depth = 0) )
    ∧ -- 2. object/morphism: faithful self-cover, not surjective (residue outside)
    ( Function.Injective E213.Lens.FlatOntology.Object1
      ∧ ¬ Function.Surjective E213.Lens.FlatOntology.Object1 )
    ∧ -- 3. object/reading: one shape Index→Bool, scale-invariant
    ( (∀ r : Raw,
          (E213.Lens.FlatOntology.Object1 r : Raw → Bool) r = true)
      ∧ (E213.Lib.Math.Real213.Core.AsLensOutput.RealAsLensOutput
          = (Nat → Nat → Bool)) )
    ∧ -- 4. difference/identity: the same 1
    ( (2 : Int) * 1 - 1 * 1
        = (E213.Lib.Physics.Simplex.Counts.NS : Int)
          - (E213.Lib.Physics.Simplex.Counts.NT : Int) ) :=
  ⟨ E213.Theory.Raw.Lambek.two_closures,
    E213.Lens.FlatOntologyClosure.self_covering_closure,
    E213.Lib.Math.Real213.ObjectIsReadingScaleInvariant.object_is_reading_scale_invariant,
    E213.Lib.Math.Mobius213OneAsGlue.mobius_det_eq_ns_minus_nt ⟩

end E213.Lib.Math.DualCollapseCapstone
