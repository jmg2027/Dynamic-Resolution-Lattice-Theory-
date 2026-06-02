import E213.Lens.SemanticAtom
import E213.Lens.FlatOntologyClosure
import E213.Lib.Math.Mobius213OneAsGlue
import E213.Theory.Atomicity

/-!
# ResidueForm — "no exterior" as source-without-enclosure (a naming capstone, NOT a capture)

This file gathers, into one ∅-axiom statement, the formal content of `05_no_exterior.md`
§5.1 ("there is no exterior to 213").  It is a **naming** capstone in the exact sense of
`DualCollapseCapstone`: it proves no new content and it is **not** a claim to have captured
the residue as one object — the residue is outside every view's image, and one of the
conjuncts below (`object1_not_surjective`) is itself that fact.

The synthesis it names: the residue is **source without enclosure**, with two directions and
a forced self-form name:

  * **(out — source)** every meaning-framework `α` receives a *unique* morphism out of Raw
    (`raw_initial`: `Raw.fold` is the unique `Raw → α`).  Everything readable is read OUT of
    the residue; there is no exterior *source* to supply a reading the fold does not.

  * **(no back — un-enclosed)** the canonical self-reading `Object1 : Raw → (Raw → Bool)` is
    faithful but **not** surjective (`object1_not_surjective`): no view's image encloses the
    residue.  There is no exterior *capture*; naming "everything pointable" always leaves the
    Cantor surplus (the residue).

  * **(name + forced shape)** the self-pointing's algebraic shadow carries the unit
    `1 = NS − NT = det P` (`mobius_det_eq_ns_minus_nt` — the off-diagonal glue/axis), and the
    shape is the unique atomic `5` (`atomic_iff_five`).

So "no exterior" is not a metaphysical boast: it is the conjunction *every reading is sourced
out (initiality) ∧ no reading encloses the source (non-surjectivity)*.  Crucially this is
**not** "the residue IS the source" promoted to identity — the form named here is the pair of
directions plus the unit-name; the residue itself stays outside every view (the second
conjunct).  No single operator unifies the directions (they live on different codomains: `α`,
`Raw → Bool`, `Int`); the honest unity is the *shared unit* `1` (proven byte-identical across
det/glue/unit elsewhere — `catalogs/cross-domain-identifications` CDI-9 — and across the
descent/overflow steps in `Cauchy/ReentryUnit`), not a forced common map.

All zero-axiom.
-/

namespace E213.Lib.Math.ResidueForm

open E213.Theory (Raw)
open E213.Lens.SemanticAtom (HasDistinguishing raw_initial)

/-- ★★★ **No exterior, named as source-without-enclosure.**  Four co-present facts, each
    proven elsewhere, bundled to exhibit the §5.1 "no exterior" content:

    1. **source (out)** — for every `HasDistinguishing α`, the distinguishing-preserving
       `Raw → α` *uniquely* exists (`raw_initial`): every reading is sourced out of Raw, no
       exterior source needed;
    2. **un-enclosed (no back)** — `Object1` is not surjective (`object1_not_surjective`): no
       view encloses the residue, no exterior capture possible;
    3. **the unit / glue / axis** — `(2·1 − 1·1) = NS − NT` (`mobius_det_eq_ns_minus_nt`): the
       self-form's off-diagonal `1`;
    4. **forced shape** — `Atomic n ↔ n = 5` (`atomic_iff_five`): the unique atomic shape.

    This **names** the two directions of no-exterior plus the forced self-form; it does **not**
    capture the residue as one object (conjunct 2 says the residue is outside every view).  No
    new content is proved — the capstone *is* the shared framing. -/
theorem no_exterior_source_without_enclosure :
    -- 1. source (out): Raw is initial — every meaning-framework reads out of it, uniquely
    (∀ (α : Type) [d : HasDistinguishing α], ∃ f : Raw → α,
        d.same (f Raw.a) d.a ∧ d.same (f Raw.b) d.b ∧
        (∀ (x y : Raw) (h : x ≠ y),
          d.same (f (Raw.slash x y h)) (d.combine (f x) (f y))) ∧
        (∀ g : Raw → α,
          d.same (g Raw.a) d.a → d.same (g Raw.b) d.b →
          (∀ (x y : Raw) (h : x ≠ y),
            d.same (g (Raw.slash x y h)) (d.combine (g x) (g y))) →
          ∀ r : Raw, d.same (g r) (f r)))
    ∧ -- 2. un-enclosed (no back): no view's image encloses the residue
    (¬ Function.Surjective E213.Lens.FlatOntology.Object1)
    ∧ -- 3. the unit / glue / axis: the self-form's off-diagonal 1 = NS − NT
    ((2 : Int) * 1 - 1 * 1
      = (E213.Lib.Physics.Simplex.Counts.NS : Int)
        - (E213.Lib.Physics.Simplex.Counts.NT : Int))
    ∧ -- 4. forced shape: the unique atomic 5
    (∀ n : Nat, E213.Theory.Atomicity.Five.Atomic n ↔ n = 5) :=
  ⟨fun α => raw_initial α,
   E213.Lens.FlatOntologyClosure.object1_not_surjective,
   E213.Lib.Math.Mobius213OneAsGlue.mobius_det_eq_ns_minus_nt,
   E213.Theory.Atomicity.Five.atomic_iff_five⟩

end E213.Lib.Math.ResidueForm
