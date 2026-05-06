import E213.Firmware.Raw
import E213.LensCore
import E213.Lens.Characterisation.Catalog
import E213.Math.CayleyDickson.CDDouble
import E213.Prelude

/-!
# Lipschitz-valued Lens

A Lens with codomain `Lipschitz` (the integer quaternions).
This is a **non-commutative R4-like Lens**: the involution
`Lipschitz.conj` is non-trivial, but the combine (quaternion
multiplication) is not commutative, so R2 fails.

**Purpose**: extends the Lens catalogue beyond commutative
codomains, connecting the Lens framework to CD tower layer 1.
-/

namespace E213.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Math.CayleyDickson.CDDouble
open E213.Math.CayleyDickson.CDDouble.Lipschitz


open E213.Math.CayleyDickson.ZI
open E213.Math.CayleyDickson.ZI.ZI
open E213.Firmware E213.Lens E213.Meta Lipschitz

/-- Lens with codomain `Lipschitz`.  `a ↦ i`, `b ↦ j`,
    combine = quaternion multiplication. -/
def lipLens : Hypervisor.Lens Lipschitz where
  base_a  := Lipschitz.I'
  base_b  := Lipschitz.J
  combine := fun u v => u * v

/-- `lipLens.combine` (= quaternion mul) is NOT commutative.
    Concrete witness: `I' * J = ⟨0, i⟩` vs `J * I' = ⟨0, -i⟩`. -/
theorem lipLens_combine_not_commutative :
    ¬ ∀ u v : Lipschitz, lipLens.combine u v = lipLens.combine v u := by
  intro h
  have := h I' J
  rw [show lipLens.combine I' J = I' * J from rfl,
      show lipLens.combine J I' = J * I' from rfl,
      I_mul_J, J_mul_I] at this
  have hr : (⟨0, ZI.I⟩ : Lipschitz).im = (⟨0, ZI.negI⟩ : Lipschitz).im := by
    rw [this]
  have : ZI.I = ZI.negI := hr
  have : (1 : Int) = -1 := (ZI.mk.injEq ..).mp this |>.2
  exact absurd this (by decide)

open E213.Firmware E213.Lens E213.Meta Lipschitz

-- ═══ Direct view values ═══

example : lipLens.view Raw.a = I'  := rfl
example : lipLens.view Raw.b = J   := rfl

theorem lipLens_view_slash_ab :
    lipLens.view (Raw.slash Raw.a Raw.b (by decide))
      = I' * J := by
  show Raw.fold I' J (fun u v => u * v)
         (Raw.slash Raw.a Raw.b (by decide)) = I' * J
  unfold Raw.fold
  rfl

/-- `lipLens.view` on the `a/b` term equals `k = I'*J`. -/
theorem lipLens_view_slash_ab_eq_K :
    lipLens.view (Raw.slash Raw.a Raw.b (by decide))
      = ⟨0, ZI.I⟩ := by
  rw [lipLens_view_slash_ab, I_mul_J]

/-- **lipLens image contains `{i, j, k, ...}`** — three
    distinct quaternion basis generators. -/
theorem lipLens_image_has_ijk :
    lipLens.view Raw.a ≠ lipLens.view Raw.b ∧
    lipLens.view Raw.a ≠ lipLens.view (Raw.slash Raw.a Raw.b (by decide)) ∧
    lipLens.view Raw.b ≠ lipLens.view (Raw.slash Raw.a Raw.b (by decide)) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · rw [lipLens_view_slash_ab_eq_K]; decide
  · rw [lipLens_view_slash_ab_eq_K]; decide

end E213.Math.CayleyDickson.CDDouble.Lipschitz
