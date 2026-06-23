import E213.Lens.Bool213.SelfReferenceForms
import E213.Lens.Foundations.ResidueReentry

/-!
# SelfReferenceThreeOutcomes — one Raw self-pointing, three co-present outcomes

`seed/AXIOM/05_no_exterior.md` §5.2 + §5.5 read the residue's self-reference as one event
seen several ways.  Three structurally distinct outcomes are now each closed ∅-axiom in
their *sharp* form, and this file bundles them.  The bundle is a conjunction of three
independent facts about three *different* objects (`not` on Raw values, the peel relation on
Raw, re-pointing on predicates) — the "same self-pointing read three ways" is the §5.2
reading, not part of the Lean (no operator unifies the three types, and none reduces to
another):

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
open E213.Lens.Foundations.FlatOntology (Object1)
open E213.Lens.Foundations.PredicateSelfEncoding (predicateToRaw)

/-- ★★ **Three sharp facts about Raw, none reducible to the others.**  For
    Raw, the three §5.2/§5.5 readings each hold in their sharp form:

    1. **oscillate** — every Bool value has `not`-orbit of minimal period exactly `2`
       (closes at `2`, never at `1`): a bounded loop on the Bool values;
    2. **converge** — the peel relation is well-founded and terminal exactly at the atoms:
       the descent settles at the floor;
    3. **escape** — re-pointing the encoded residue never closes the cover: the unbounded
       residue ascent.

    A conjunction of three independent sharp results about three *different* objects (`not`
    on Bool-valued Raws, the peel relation on Raw, re-pointing on predicates).  That they are
    "one self-pointing read three ways" is the §5.2 reading, not part of the Lean: no
    operator is forced across the three types, and none of the three reduces to another. -/
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
   E213.Lens.Foundations.ResidueReentry.residue_reentry_never_closes n⟩

end E213.Lens.SelfReferenceThreeOutcomes
