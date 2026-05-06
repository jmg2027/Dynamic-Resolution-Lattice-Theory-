import E213.Math.Real213.CutSum
import E213.Math.Real213.CutMaxMin

/-!
# CutPoset: cut-level partial order

cutLe cx cy := "x ≤ y" via "every rational ≥ y is ≥ x".
cutEq cx cy := pointwise Bool equality.

## Significance

Native order on RealCut in 213.  Cut form of Bishop's ≤.
-/

namespace E213.Math.Real213.CutPoset

open E213.Firmware E213.Lens
open E213.Math.Real213.CutMaxMin (cutMax cutMin)

/-- **cutEq**: pointwise Bool equality of cuts. -/
def cutEq (cx cy : Nat → Nat → Bool) : Prop := ∀ m k, cx m k = cy m k

/-- **cutLe**: x ≤ y as cuts.  Direction: cy implies cx. -/
def cutLe (cx cy : Nat → Nat → Bool) : Prop :=
  ∀ m k, cy m k = true → cx m k = true

/-- cutEq reflexivity. -/
theorem cutEq_refl (c : Nat → Nat → Bool) : cutEq c c := fun _ _ => rfl

/-- cutEq symmetry. -/
theorem cutEq_symm (cx cy : Nat → Nat → Bool) :
    cutEq cx cy → cutEq cy cx := fun h m k => (h m k).symm

/-- cutEq transitivity. -/
theorem cutEq_trans (cx cy cz : Nat → Nat → Bool) :
    cutEq cx cy → cutEq cy cz → cutEq cx cz :=
  fun hxy hyz m k => (hxy m k).trans (hyz m k)

/-- cutLe reflexivity. -/
theorem cutLe_refl (c : Nat → Nat → Bool) : cutLe c c :=
  fun _ _ h => h

/-- cutLe transitivity. -/
theorem cutLe_trans (cx cy cz : Nat → Nat → Bool) :
    cutLe cx cy → cutLe cy cz → cutLe cx cz :=
  fun hxy hyz m k hcz => hxy m k (hyz m k hcz)

/-- cutEq → cutLe (both directions). -/
theorem cutLe_of_cutEq (cx cy : Nat → Nat → Bool) :
    cutEq cx cy → cutLe cx cy := fun h m k hy => (h m k).symm ▸ hy

/-- **Antisymmetry**: cutLe both directions → cutEq. -/
theorem cutEq_of_cutLe_both (cx cy : Nat → Nat → Bool) :
    cutLe cx cy → cutLe cy cx → cutEq cx cy := by
  intro h1 h2 m k
  cases hcx : cx m k with
  | true =>
    have := h2 m k hcx
    rw [this]
  | false =>
    cases hcy : cy m k with
    | true =>
      have hcx_true := h1 m k hcy
      rw [hcx_true] at hcx
      exact Bool.noConfusion hcx
    | false => rfl

open E213.Firmware E213.Lens
open E213.Math.Real213.CutMaxMin (cutMax cutMin)

/-- **x ≤ max(x, y)**: cutLe cx (cutMax cx cy). -/
theorem cutLe_cutMax_left (cx cy : Nat → Nat → Bool) : cutLe cx (cutMax cx cy) := by
  intro m k h
  show cx m k = true
  have : (cx m k && cy m k) = true := h
  cases hcx : cx m k with
  | true => rfl
  | false =>
    rw [hcx] at this
    cases this

/-- **y ≤ max(x, y)**. -/
theorem cutLe_cutMax_right (cx cy : Nat → Nat → Bool) : cutLe cy (cutMax cx cy) := by
  intro m k h
  show cy m k = true
  have : (cx m k && cy m k) = true := h
  cases hcy : cy m k with
  | true => rfl
  | false =>
    cases hcx : cx m k <;> rw [hcx, hcy] at this <;> cases this

/-- **min(x, y) ≤ x**: cutLe (cutMin cx cy) cx. -/
theorem cutLe_cutMin_left (cx cy : Nat → Nat → Bool) : cutLe (cutMin cx cy) cx := by
  intro m k h
  show (cx m k || cy m k) = true
  rw [h]; rfl

/-- **min(x, y) ≤ y**. -/
theorem cutLe_cutMin_right (cx cy : Nat → Nat → Bool) : cutLe (cutMin cx cy) cy := by
  intro m k h
  show (cx m k || cy m k) = true
  rw [h]
  cases cx m k <;> rfl

/-- **least-upper-bound property of cutMax**: x, y ≤ z → max(x, y) ≤ z. -/
theorem cutMax_lub (cx cy cz : Nat → Nat → Bool)
    (hxz : cutLe cx cz) (hyz : cutLe cy cz) :
    cutLe (cutMax cx cy) cz := by
  intro m k hcz
  show (cx m k && cy m k) = true
  rw [hxz m k hcz, hyz m k hcz]
  rfl

/-- **greatest-lower-bound property of cutMin**: z ≤ x, z ≤ y → z ≤ min(x, y). -/
theorem cutMin_glb (cx cy cz : Nat → Nat → Bool)
    (hzx : cutLe cz cx) (hzy : cutLe cz cy) :
    cutLe cz (cutMin cx cy) := by
  intro m k hmin
  show cz m k = true
  have hor : (cx m k || cy m k) = true := hmin
  cases hcx : cx m k with
  | true => exact hzx m k hcx
  | false =>
    cases hcy : cy m k with
    | true => exact hzy m k hcy
    | false => rw [hcx, hcy] at hor; cases hor

end E213.Math.Real213.CutPoset
