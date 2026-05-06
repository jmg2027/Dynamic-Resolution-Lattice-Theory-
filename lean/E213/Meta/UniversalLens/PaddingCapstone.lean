import E213.Meta.UniversalLens.Padding
import E213.Meta.UniversalLens.Nat3
import E213.Meta.UniversalLens.Q213_3
import E213.Meta.UniversalLens.Nat4

/-!
# Universal Lens padding capstone — abstract + concrete bundle

Bundles the abstract padding lemma with its concrete applications:

  - Abstract: `view_inj_of_inj_proj` (any lens with injective
    projection through known universal map ⇒ universal)
  - Concrete: expSumLens3 (ℕ³), q213Lens3 (Q213³), expSumLens4 (ℕ⁴)

The padding theory closes HANDOFF Open Continuation #5 in *general*
form: future universal-lens constructions at any codomain become
trivial applications of the meta-theorem.
-/

namespace E213.Meta.UniversalLens.PaddingCapstone

open E213.Firmware E213.Lens
open E213.Meta.UniversalLens.Core (IsUniversal)
open E213.Meta.UniversalLens.Padding (view_inj_of_inj_proj)

/-- ★★★★★★★★ Padding theory capstone bundling abstract lemma + 3
    concrete applications (ℕ³, Q213³, ℕ⁴) all via a single
    meta-theorem.  All ≤ {propext, Quot.sound}. -/
theorem padding_capstone :
    -- Abstract padding lemma exists and is applicable
    (∀ {α γ : Type} (M : Lens α) (proj : α → γ) (f : Raw → γ),
        Function.Injective f →
        (∀ r, proj (M.view r) = f r) →
        IsUniversal M)
    -- Concrete: expSumLens3 universal
    ∧ IsUniversal E213.Meta.UniversalLens.Nat3.expSumLens3
    -- Concrete: q213Lens3 universal
    ∧ IsUniversal E213.Meta.UniversalLens.Q213_3.q213Lens3
    -- Concrete: expSumLens4 universal
    ∧ IsUniversal E213.Meta.UniversalLens.Nat4.expSumLens4 :=
  ⟨@view_inj_of_inj_proj,
   E213.Meta.UniversalLens.Nat3.expSumLens3_is_universal,
   E213.Meta.UniversalLens.Q213_3.q213Lens3_is_universal,
   E213.Meta.UniversalLens.Nat4.expSumLens4_is_universal⟩

end E213.Meta.UniversalLens.PaddingCapstone
