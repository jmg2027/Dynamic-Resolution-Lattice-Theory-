import E213.Lens.FlatOntologyClosure
import E213.Lens.PredicateSelfEncoding

/-!
# ResidueReentry — the residue re-enters as the next operand, and the cover never closes

The self-cover has two halves, both ∅-axiom:

  * `FlatOntologyClosure`: `Object1 : Raw → (Raw → Bool)` is faithful (`object1_injective`)
    but **not total** (`object1_not_surjective`) — pointing leaves a residue, the
    predicates outside its image (`cantor_raw_bool`);
  * `PredicateSelfEncoding`: a (finite-prefix) predicate encodes **back** to a Raw
    (`predicateToRaw`), so the residue — itself a predicate — re-enters the *domain* of
    pointing.

This file closes the loop: the residue is not an exterior surplus that sits there;
encoded back to a Raw and pointed at again, it produces a fresh predicate — and the
re-pointing **still** leaves a residue.  The composite `P ↦ Object1 (predicateToRaw n P)`
(encode the predicate, point at the encoding) is **not surjective**
(`residue_reentry_never_closes`): its image lies inside `Object1`'s image, which already
misses the residue.  So naming the residue never recovers it; the act produces a new
object, leaving a new residue.

The self-cover therefore never closes: each turn leaves the residue, the residue
re-enters as a Raw, the next turn leaves it again.  The residue is perpetually the *next
operand* of pointing — the same self-applying, gapless re-entry the resolution tower
shows at the diagonalisation scale (`Cauchy/DepthHeightDiagonal.diag_self_applies`), here
at the foundational pointing scale.  `residue_perpetually_reenters` bundles the three
facts.

All zero-axiom.
-/

namespace E213.Lens.ResidueReentry

open E213.Theory (Raw)
open E213.Lens.FlatOntology (Object1)
open E213.Lens.FlatOntologyClosure (object1_injective object1_not_surjective)
open E213.Lens.PredicateSelfEncoding (predicateToRaw)

/-! ## §1 — re-entering the residue never closes the cover -/

/-- ★★★ **The residue re-entry never closes the cover.**  Encode any predicate to a Raw
    (`predicateToRaw n`) and point at the encoding (`Object1`): the composite
    `P ↦ Object1 (predicateToRaw n P)` is **not surjective**.  Its image lies inside
    `Object1`'s image, which already misses the residue; so re-entering and re-pointing
    never produces the un-pointed predicates.  Naming the residue yields a fresh object,
    leaving a fresh residue — the cover never closes. -/
theorem residue_reentry_never_closes (n : Nat) :
    ¬ Function.Surjective (fun P : Raw → Bool => Object1 (predicateToRaw n P)) := by
  intro hsurj
  apply object1_not_surjective
  intro Q
  obtain ⟨P, hP⟩ := hsurj Q
  exact ⟨predicateToRaw n P, hP⟩

/-! ## §2 — the perpetual re-entry, bundled -/

/-- ★★★ **The residue is perpetually the next operand.**  Three facts of one loop:

    1. pointing is faithful but not total (`object1_injective` ∧ `object1_not_surjective`):
       every pointing leaves a residue;
    2. the residue re-enters the domain: every predicate `P` encodes to a Raw
       `predicateToRaw n P` (`predicate_self_encoding_closure`);
    3. re-entering and re-pointing never closes the cover
       (`residue_reentry_never_closes`).

    So the self-cover never closes: each turn leaves the residue, the residue re-enters
    as a Raw, the next turn leaves it again.  The residue is the perpetual next operand —
    the foundational instance of the gapless, self-applying re-entry. -/
theorem residue_perpetually_reenters (n : Nat) :
    (Function.Injective Object1 ∧ ¬ Function.Surjective Object1)
    ∧ (∀ P : Raw → Bool, ∃ r : Raw, r = predicateToRaw n P)
    ∧ ¬ Function.Surjective (fun P : Raw → Bool => Object1 (predicateToRaw n P)) :=
  ⟨⟨object1_injective, object1_not_surjective⟩,
   fun P => ⟨predicateToRaw n P, rfl⟩,
   residue_reentry_never_closes n⟩

end E213.Lens.ResidueReentry
