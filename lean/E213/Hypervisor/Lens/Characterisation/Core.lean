import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Hypervisor.Lens.Characterisation.Catalog
import E213.Prelude

/-!
# LensCharacterisation: structural iff theorems

Consolidates the Lens-level theorems that were previously
sprinkled through `LensCatalog` and `SelfRecognising` into a
clean "necessary and sufficient" toolkit.

## Theorems

* `swap_invariant_of_base_eq_comm`
  (sufficient) base_a = base_b + commutative combine
  ⇒ view swap-invariant.

* `swap_invariant_iff_base_eq_of_comm`
  Under commutative combine, swap-invariance iff
  base_a = base_b.

* `R4_conj_agrees_on_image`
  Two R4-witnessing involutions agree on every view-image
  point; uniqueness of `conj` up to the image of the Lens.

* `R3_view_nonVanishing`
  Under NonVanishingCodomain-style assumptions lifted to the Lens
  level (no-zero-divisor combine + nonzero base values), every
  view(r) is nonzero — non-vanishing lifts from base-level to
  Raw-level by induction.
-/

namespace E213.Hypervisor.Lens.Characterisation.Core
open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Characterisation.Catalog

-- ═══ Characterisation 1: swap-invariance ═══

/-- **Sufficient condition for swap-blindness.**  If the Lens
    has equal base values and a commutative combine, its view
    is swap-invariant.  Proof: apply `Raw.fold_swap_hom` with
    `conj = id`; all three homomorphism clauses are trivial.
    -/
theorem swap_invariant_of_base_eq_comm
    {α : Type} (L : Hypervisor.Lens α)
    (hbase : L.base_a = L.base_b)
    (hcomm : ∀ u v : α, L.combine u v = L.combine v u)
    (r : Raw) : L.view (Raw.swap r) = L.view r := by
  show Raw.fold L.base_a L.base_b L.combine (Raw.swap r)
     = Raw.fold L.base_a L.base_b L.combine r
  have h := Raw.fold_swap_hom L.base_a L.base_b L.combine id
    (by simp [hbase]) (by simp [hbase])
    (fun _ _ => rfl) hcomm r
  exact h

end E213.Hypervisor.Lens.Characterisation.Core
namespace E213.Hypervisor.Lens.Characterisation.Core
open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Characterisation.Catalog

/-- **Full characterisation under commutative combine.**  The
    Lens is swap-invariant iff its base values coincide.  The
    forward direction uses `swap_invariant_base_eq` (no
    commutativity needed); the backward direction uses
    `swap_invariant_of_base_eq_comm`. -/
theorem swap_invariant_iff_base_eq_of_comm
    {α : Type} (L : Hypervisor.Lens α)
    (hcomm : ∀ u v : α, L.combine u v = L.combine v u) :
    (∀ r : Raw, L.view (Raw.swap r) = L.view r)
      ↔ L.base_a = L.base_b := by
  constructor
  · intro h
    exact swap_invariant_base_eq h
  · intro hbase r
    exact swap_invariant_of_base_eq_comm L hbase hcomm r

-- ═══ Characterisation 2: conj uniqueness on image ═══

/-- **R4 uniqueness on image.**  If two involutions both
    witness R4 for the same Lens, they coincide on every
    value in the view-image (not necessarily on all of α).
    Proof by rewriting both sides to `view (Raw.swap r)`. -/
theorem R4_conj_agrees_on_image
    {α : Type} {L : Hypervisor.Lens α} {conj1 conj2 : α → α}
    (h1 : SwapMatching L conj1) (h2 : SwapMatching L conj2)
    (r : Raw) : conj1 (L.view r) = conj2 (L.view r) := by
  have e1 := h1.2.2 r
  have e2 := h2.2.2 r
  rw [← e1, ← e2]

/-- **R4 uniqueness on surjective Lenses.**  If `view` is
    surjective and two involutions both witness R4, they are
    equal as functions. -/
theorem R4_conj_unique_of_surjective
    {α : Type} {L : Hypervisor.Lens α} {conj1 conj2 : α → α}
    (h1 : SwapMatching L conj1) (h2 : SwapMatching L conj2)
    (hsurj : Function.Surjective L.view) : conj1 = conj2 := by
  funext u
  obtain ⟨r, hr⟩ := hsurj u
  have := R4_conj_agrees_on_image h1 h2 r
  rw [hr] at this
  exact this

end E213.Hypervisor.Lens.Characterisation.Core
namespace E213.Hypervisor.Lens.Characterisation.Core
open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Characterisation.Catalog

-- ═══ Characterisation 3: R3 lifts from base to Raw ═══

/-- **R3 lifts to every Raw term.**  If `combine` has no zero
    divisors and both base values are nonzero, then `view r`
    is nonzero for every `r : Raw` — the point-wise R3
    property upgrades to a Raw-level non-vanishing statement.

    Proof by `Raw.rec`: base cases are the hypotheses on
    `base_a`, `base_b`; at `slash`, no-zero-divisor means
    `combine ≠ 0` so long as both children's views are
    nonzero (inductive hypotheses). -/
theorem R3_view_nonVanishing
    {α : Type} [Zero α] (L : Hypervisor.Lens α)
    (hba : L.base_a ≠ 0) (hbb : L.base_b ≠ 0)
    (hcomm : ∀ u v : α, L.combine u v = L.combine v u)
    (hnz : ∀ u v : α, L.combine u v = 0 → u = 0 ∨ v = 0)
    (r : Raw) : L.view r ≠ 0 := by
  induction r using Raw.rec with
  | a => show L.base_a ≠ 0; exact hba
  | b => show L.base_b ≠ 0; exact hbb
  | slash x y h ihx ihy =>
      show L.view (Raw.slash x y h) ≠ 0
      have hstep : L.view (Raw.slash x y h)
                     = L.combine (L.view x) (L.view y) := by
        show Raw.fold L.base_a L.base_b L.combine (Raw.slash x y h)
           = L.combine (Raw.fold L.base_a L.base_b L.combine x)
                        (Raw.fold L.base_a L.base_b L.combine y)
        exact Raw.fold_slash L.base_a L.base_b L.combine hcomm x y h
      rw [hstep]
      intro heq
      rcases hnz _ _ heq with hx0 | hy0
      · exact ihx hx0
      · exact ihy hy0

end E213.Hypervisor.Lens.Characterisation.Core