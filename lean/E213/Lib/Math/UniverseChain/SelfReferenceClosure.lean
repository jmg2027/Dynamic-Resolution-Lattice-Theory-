import E213.Lib.Math.UniverseChain.Lawvere
import E213.Meta.UniversalLens.Core
import E213.Lib.Math.Infinity.Cantor

/-!
# Self-reference closure — Raw self-references safely (∅-axiom)

The conversational claim:

> Raw is self-referential (its meta is Raw itself, formalized via
> `idLens : Lens Raw` being universal), yet does **not** suffer
> Russell / Curry / Girard contradictions.

This file formalizes *why*.  The mechanism:

  * Russell, Curry, Girard, Cantor all instantiate the same
    Lawvere fixed-point theorem (`UniverseChain.Lawvere`).
  * The paradoxical fixed point requires a *surjection*
    `X → (X → A)` for some `A` admitting an endomorphism without
    fixed point (e.g. `!` on `Bool`).
  * On `Raw`, no such surjection exists (`Infinity.cantor_raw_bool`).
  * Hence the Lawvere fixed-point construction *cannot run* —
    the paradox premise is structurally absent.

What remains is *safe* self-reference: identity Lens on Raw, with
view injective (`Meta.UniversalLens.Core.idLens_is_universal`).

The two facts coexist by construction.
-/

namespace E213.Lib.Math.UniverseChain.SelfReferenceClosure

open E213.Theory
open E213.Lens.Instances.Identity (idLens)
open E213.Meta.UniversalLens.Core (IsUniversal idLens_is_universal refines_all)

/-- ★ **Safe self-reference exists.**  `idLens : Lens Raw` is a
    universal Lens — its `view` is injective on Raw.  Raw can
    describe itself via this Lens. -/
theorem raw_admits_universal_lens :
    ∃ L : E213.Lens.Lens Raw, IsUniversal L :=
  ⟨idLens, idLens_is_universal⟩

/-- ★ **Bool-paradox surjection on Raw is absent.**  No
    `f : Raw → (Raw → Bool)` is surjective. -/
theorem no_raw_bool_surjection :
    ¬ ∃ f : Raw → (Raw → Bool), Function.Surjective f :=
  E213.Infinity.cantor_raw_bool

/-- ★ **Lawvere blocked on Raw.**  Were there a Bool-surjection
    on Raw, every `g : Bool → Bool` would have a fixed point —
    contradicting `not_has_no_fixed_point`.  Since the conclusion
    fails, the hypothesis fails: no such surjection exists. -/
theorem lawvere_blocked_on_raw :
    ¬ ∃ f : Raw → Raw → Bool, ∀ φ : Raw → Bool, ∃ x : Raw, f x = φ :=
  E213.Lib.Math.UniverseChain.Lawvere.cantor_via_lawvere Raw

/-- ★★★ **Self-reference closure capstone.**

    Two ∅-axiom facts coexist:

    1. Raw admits a universal Lens (`idLens`) — *safe* self-reference.
    2. Raw admits no Bool-surjection — *paradoxical* self-reference
       (Russell / Curry / Girard / Cantor) is structurally blocked.

    Together: Raw self-describes (1) without exploding (2). -/
theorem self_reference_closure :
    (∃ L : E213.Lens.Lens Raw, IsUniversal L)
    ∧ (¬ ∃ f : Raw → (Raw → Bool), Function.Surjective f)
    ∧ (¬ ∃ f : Raw → Raw → Bool, ∀ φ : Raw → Bool, ∃ x : Raw, f x = φ) :=
  ⟨raw_admits_universal_lens,
   no_raw_bool_surjection,
   lawvere_blocked_on_raw⟩

end E213.Lib.Math.UniverseChain.SelfReferenceClosure
