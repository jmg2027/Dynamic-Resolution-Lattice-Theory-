import E213.Lens.Bool213.SelfReferenceForms
import E213.Lens.ResidueReentry

/-!
# SelfReferenceThreeOutcomes — one Raw self-pointing, three co-present outcomes

`seed/AXIOM/05_no_exterior.md` §5.2 + §5.5: the residue's self-reference is one event read
several ways.  Three structurally distinct outcomes are now each closed ∅-axiom in their
*sharp* form, and this file bundles them as the co-presence theorem — not a single operator
(the three act on different objects: `not` on Raw values, the peel relation on Raw, the
re-pointing on predicates), but three readings of the *same* self-pointing:

  * **Oscillate** (Bool / liar, bounded loop).  On a Bool value, `not` has minimal period
    **exactly 2** (`SelfReferenceForms.bool_min_period_two`): never period 1 (no fixed
    point) yet closing at 2 (involution).  The turn loops without settling.

  * **Converge** (Nat / Lambek, terminating descent).  The peel relation is **well-founded**
    (`Lambek.isPart_wf`) and a Raw is peel-terminal **iff** it is an atom
    (`Lambek.terminal_iff_atom`): the descent settles at exactly the atomic floor.

  * **Escape** (residue / predicate, top-less ascent).  Re-pointing the encoded residue
    **never closes** the cover (`ResidueReentry.residue_reentry_never_closes`): the surplus
    re-enters as the next operand, forever.

All three move by the same count-Lens unit `1` (the convergence step and the escape surplus
are the identical `Nat` unit — `Cauchy.ReentryUnit.reentry_unit_across_scales`, one layer
up; the oscillation's period `2` is the two distinguishings of one toggle).  Which outcome
a turn takes is what the unit residue does next: loop (bounded), settle (floor), or open the
next rung (unbounded).

All zero-axiom.
-/

namespace E213.Lens.SelfReferenceThreeOutcomes

open E213.Theory (Raw)
open E213.Lens.Bool213.Raw (isBool not)
open E213.Lens.FlatOntology (Object1)
open E213.Lens.PredicateSelfEncoding (predicateToRaw)

/-- ★★★ **One self-pointing, three co-present outcomes.**  For the Raw substrate, all three
    readings of §5.2/§5.5 hold simultaneously, each in its sharp form:

    1. **oscillate** — every Bool value has `not`-orbit of minimal period exactly `2`
       (closes at `2`, never at `1`): the bounded liar loop;
    2. **converge** — the peel relation is well-founded and terminal exactly at the atoms:
       the descent settles at the floor;
    3. **escape** — re-pointing the encoded residue never closes the cover: the unbounded
       residue ascent.

    Three readings of one Raw self-pointing — co-present, none privileged, no operator
    forced across their different types. -/
theorem self_reference_three_outcomes (n : Nat) :
    -- OSCILLATE (bounded): minimal period exactly 2 on the Bool values
    (∀ r : Raw, isBool r = true →
      E213.Lens.Bool213.SelfReferenceForms.notIter 1 r ≠ r
      ∧ E213.Lens.Bool213.SelfReferenceForms.notIter 2 r = r)
    ∧ -- CONVERGE (terminating): well-founded peel, terminal iff atomic floor
    (WellFounded E213.Theory.Raw.Lambek.IsPart
      ∧ (∀ r : Raw, E213.Theory.Raw.Lambek.IsTerminal r ↔ E213.Theory.Raw.Lambek.IsAtom r))
    ∧ -- ESCAPE (unbounded): re-pointing never closes the cover
    ¬ Function.Surjective (fun P : Raw → Bool => Object1 (predicateToRaw n P)) :=
  ⟨fun r h => E213.Lens.Bool213.SelfReferenceForms.bool_min_period_two r h,
   ⟨E213.Theory.Raw.Lambek.isPart_wf, E213.Theory.Raw.Lambek.terminal_iff_atom⟩,
   E213.Lens.ResidueReentry.residue_reentry_never_closes n⟩

end E213.Lens.SelfReferenceThreeOutcomes
