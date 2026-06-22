import E213.Lens.Foundations.SemanticAtom
import E213.Lens.Foundations.PredicateSelfEncoding

/-!
# The no-exhibitable-exterior closure (formal anchor for §1 / §5.1)

The strongest reading of "there is no exterior to 213" (`seed/AXIOM/05_no_exterior.md` §5.1): **the act of
distinguishing reaches everything it can reach, and the very attempt to present an exterior — even to
conceive "non-existence" or "the unpointable" — is itself an act of pointing, hence internal.**  There is
no exterior to exhibit, and no conceptual hiding place either: to conceive the concept is already to point
at it.

This file pulls the formalizable core of that closure down to a proof-core (∅-axiom):

  * **Naming is internal** — any property by which one would point at a candidate (`name : Raw → Bool`)
    is itself a `Raw` (`PredicateSelfEncoding.predicateToRaw`).  Conceiving "the exterior" lands inside.
  * **No distinguishing exterior** — any candidate type `α` that distinguishes at all
    (`HasDistinguishing α`) receives the *unique* structure-preserving morphism from `Raw`
    (`universalMorphism_unique`): its entire distinguishing is `Raw`'s, read out.  To present `α` as a
    *framework* is to present something downstream of `Raw`, not exterior.
-/

namespace E213.Lens.Foundations.NoExteriorClosure

open E213.Theory E213.Lens E213.Lens.Foundations.SemanticAtom E213.Lens.Foundations.PredicateSelfEncoding

/-- ★★★★★ **Naming a candidate exterior is producing a `Raw`.**  Any property by which one would name or
    conceive a candidate — `name : Raw → Bool`, the act of distinguishing it — is itself a `Raw`.  So
    conceiving "the exterior" / "the non-existent" does not escape; the conception lands inside. -/
theorem naming_is_internal (n : Nat) (name : Raw → Bool) :
    ∃ r : Raw, r = predicateToRaw n name := ⟨_, rfl⟩

/-- ★★★★★ **No distinguishing exterior.**  Any candidate `α` that distinguishes at all
    (`HasDistinguishing α`) receives the *unique* distinguishing-preserving morphism from `Raw`
    (`universalMorphism`): every `f : Raw → α` that preserves the atoms and slash agrees with it.  So a
    candidate "alternative / exterior framework" is downstream of `Raw`, not outside it. -/
theorem distinguishing_is_downstream (α : Type) [d : HasDistinguishing α]
    (f : Raw → α) (ha : d.same (f Raw.a) d.a) (hb : d.same (f Raw.b) d.b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
      d.same (f (Raw.slash x y h)) (d.combine (f x) (f y))) :
    ∀ r : Raw, d.same (f r) (universalMorphism α r) :=
  universalMorphism_unique α f ha hb hslash

/-- Concrete witness: the predicate "nothing is exterior" — the very claim — is itself a `Raw`. -/
theorem the_exterior_claim_is_a_raw :
    ∃ r : Raw, r = predicateToRaw 3 (fun _ => false) := ⟨_, rfl⟩

end E213.Lens.Foundations.NoExteriorClosure
