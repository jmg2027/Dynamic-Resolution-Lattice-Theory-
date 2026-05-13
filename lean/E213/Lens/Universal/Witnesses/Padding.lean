import E213.Lens.Universal.Witnesses.Core

/-!
# Universal Lens padding lemma (abstract codomain extension)

Generalises the projection trick used in `UniversalLensNat3` and
`UniversalLensQ213_3`:

  > A lens M is universal whenever its catamorphism projects
  > injectively through some known universal map (e.g., a
  > previously-proven universal lens or any injective function).

Concretely: if `f : α → γ` is injective and `(M.view r) =`
some pair whose first component agrees with `f (L.view r)` for a
universal `L : Lens γ`, then M is universal.

This is the META-padding lemma: ANY universal lens lifts to ANY
extension of its codomain that preserves the injective core.

Result: future universal-lens constructions at richer codomains
become a one-liner application of `view_inj_of_inj_proj`.
-/

namespace E213.Lens.Universal.Witnesses.Padding

open E213.Theory E213.Lens
open E213.Lens.Universal.Witnesses.Core

/-- ★★★★ Generic injectivity-via-projection lemma.

  If a lens M's view satisfies `proj (M.view r) = f r` for some
  injective `f : Raw → γ`, then M is universal.  Concrete `f`s
  used in 213's metatheory: `expSumNat`, `qNat`, `idLens.view`.

  This abstracts the proof pattern of `expSumLens3_view_inj`
  and `q213Lens3_view_inj`. -/
theorem view_inj_of_inj_proj {α γ : Type} (M : Lens α)
    (proj : α → γ) (f : Raw → γ)
    (hf : Function.Injective f)
    (hproj : ∀ r, proj (M.view r) = f r) :
    IsUniversal M := by
  intro r s hrs
  apply hf
  rw [← hproj r, ← hproj s, hrs]

/-- Specialisation to Lens(α × β): first-projection lifts. -/
theorem view_inj_of_fst_proj {α β γ : Type} (M : Lens (α × β))
    (proj1 : α → γ) (f : Raw → γ)
    (hf : Function.Injective f)
    (hproj : ∀ r, proj1 (M.view r).1 = f r) :
    IsUniversal M :=
  view_inj_of_inj_proj M (fun p => proj1 p.1) f hf hproj

/-- ★★★★★ Specialisation: any Lens(α × β) inherits universality
    when its first component IS a known universal lens.

  If `M.view r = (L.view r, ?)` for a universal `L : Lens α`,
  then M is universal.  Direct corollary of `view_inj_of_inj_proj`. -/
theorem view_inj_of_fst_eq_universal {α β : Type}
    (L : Lens α) (M : Lens (α × β))
    (hL : IsUniversal L)
    (hproj : ∀ r, (M.view r).1 = L.view r) :
    IsUniversal M :=
  view_inj_of_inj_proj M Prod.fst L.view hL hproj

/-- Triple-codomain specialisation: Lens(α × β × γ) inherits
    universality from a universal first-component lens. -/
theorem view_inj_of_fst_eq_universal_triple {α β γ : Type}
    (L : Lens α) (M : Lens (α × β × γ))
    (hL : IsUniversal L)
    (hproj : ∀ r, (M.view r).1 = L.view r) :
    IsUniversal M :=
  view_inj_of_inj_proj M Prod.fst L.view hL hproj

end E213.Lens.Universal.Witnesses.Padding
