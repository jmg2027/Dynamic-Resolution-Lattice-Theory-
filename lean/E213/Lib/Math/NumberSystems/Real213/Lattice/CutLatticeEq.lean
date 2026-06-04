import E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset

import E213.Lib.Math.NumberSystems.Real213.Core.Core
/-!
# CutLatticeEq: cutMax/cutMin preserve cutEq + cutLe

Compatibility of lattice ops with the cut order/equiv structure.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Lattice.CutLatticeEq

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutLe cutEq cutEq_trans cutLe_trans)
open E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin (cutMax cutMin)
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)

/-- cutMax preserves cutEq on left arg. -/
theorem cutMax_cutEq_left (cx cx' cy : Nat → Nat → Bool)
    (h : cutEq cx cx') :
    cutEq (cutMax cx cy) (cutMax cx' cy) := fun m k => by
  show (cx m k && cy m k) = (cx' m k && cy m k)
  rw [h m k]

/-- cutMax preserves cutEq on right arg. -/
theorem cutMax_cutEq_right (cx cy cy' : Nat → Nat → Bool)
    (h : cutEq cy cy') :
    cutEq (cutMax cx cy) (cutMax cx cy') := fun m k => by
  show (cx m k && cy m k) = (cx m k && cy' m k)
  rw [h m k]

/-- cutMin preserves cutEq on left arg. -/
theorem cutMin_cutEq_left (cx cx' cy : Nat → Nat → Bool)
    (h : cutEq cx cx') :
    cutEq (cutMin cx cy) (cutMin cx' cy) := fun m k => by
  show (cx m k || cy m k) = (cx' m k || cy m k)
  rw [h m k]

/-- cutMin preserves cutEq on right arg. -/
theorem cutMin_cutEq_right (cx cy cy' : Nat → Nat → Bool)
    (h : cutEq cy cy') :
    cutEq (cutMin cx cy) (cutMin cx cy') := fun m k => by
  show (cx m k || cy m k) = (cx m k || cy' m k)
  rw [h m k]

/-- 보조: `(a && b) = true → a = true`.  PURE — propext 없음. -/
private theorem and_left_of_eq_true {a b : Bool} (h : (a && b) = true) : a = true :=
  match a, h with
  | true, _ => rfl
  | false, h => Bool.noConfusion h

/-- 보조: `(a && b) = true → b = true`.  PURE. -/
private theorem and_right_of_eq_true {a b : Bool} (h : (a && b) = true) : b = true :=
  match a, h with
  | true, h => h
  | false, h => Bool.noConfusion h

/-- 보조: `a = true → b = true → (a && b) = true`. -/
private theorem and_intro_eq_true {a b : Bool}
    (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

/-- cutMax preserves cutLe on left arg. -/
theorem cutMax_cutLe_left (cx1 cx2 cy : Nat → Nat → Bool)
    (h : cutLe cx1 cx2) :
    cutLe (cutMax cx1 cy) (cutMax cx2 cy) := fun m k h_max => by
  show (cx1 m k && cy m k) = true
  have h_max' : (cx2 m k && cy m k) = true := h_max
  exact and_intro_eq_true (h m k (and_left_of_eq_true h_max'))
                          (and_right_of_eq_true h_max')

/-- cutMax preserves cutLe on right arg. -/
theorem cutMax_cutLe_right (cx cy1 cy2 : Nat → Nat → Bool)
    (h : cutLe cy1 cy2) :
    cutLe (cutMax cx cy1) (cutMax cx cy2) := fun m k h_max => by
  show (cx m k && cy1 m k) = true
  have h_max' : (cx m k && cy2 m k) = true := h_max
  exact and_intro_eq_true (and_left_of_eq_true h_max')
                          (h m k (and_right_of_eq_true h_max'))

/-- 보조: `(a || b) = true → a = true ∨ b = true`.  PURE. -/
private theorem or_cases_eq_true {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true :=
  match a, h with
  | true, _ => Or.inl rfl
  | false, h => Or.inr h

/-- 보조: `a = true → (a || b) = true`. -/
private theorem or_intro_left {a b : Bool} (h : a = true) : (a || b) = true := by
  rw [h]; rfl

/-- 보조: `b = true → (a || b) = true`. -/
private theorem or_intro_right {a b : Bool} (h : b = true) : (a || b) = true := by
  rw [h]; cases a <;> rfl

/-- cutMin preserves cutLe on left arg. -/
theorem cutMin_cutLe_left (cx1 cx2 cy : Nat → Nat → Bool)
    (h : cutLe cx1 cx2) :
    cutLe (cutMin cx1 cy) (cutMin cx2 cy) := fun m k h_min => by
  show (cx1 m k || cy m k) = true
  have h_min' : (cx2 m k || cy m k) = true := h_min
  rcases or_cases_eq_true h_min' with h1 | h2
  · exact or_intro_left (h m k h1)
  · exact or_intro_right h2

/-- cutMin preserves cutLe on right arg. -/
theorem cutMin_cutLe_right (cx cy1 cy2 : Nat → Nat → Bool)
    (h : cutLe cy1 cy2) :
    cutLe (cutMin cx cy1) (cutMin cx cy2) := fun m k h_min => by
  show (cx m k || cy1 m k) = true
  have h_min' : (cx m k || cy2 m k) = true := h_min
  rcases or_cases_eq_true h_min' with h1 | h2
  · exact or_intro_left h1
  · exact or_intro_right (h m k h2)

/-- cutMax preserves cutEq on both args. -/
theorem cutMax_cutEq_both (cx cx' cy cy' : Nat → Nat → Bool)
    (hx : cutEq cx cx') (hy : cutEq cy cy') :
    cutEq (cutMax cx cy) (cutMax cx' cy') :=
  cutEq_trans _ _ _ (cutMax_cutEq_left cx cx' cy hx)
                    (cutMax_cutEq_right cx' cy cy' hy)

/-- cutMin preserves cutEq on both args. -/
theorem cutMin_cutEq_both (cx cx' cy cy' : Nat → Nat → Bool)
    (hx : cutEq cx cx') (hy : cutEq cy cy') :
    cutEq (cutMin cx cy) (cutMin cx' cy') :=
  cutEq_trans _ _ _ (cutMin_cutEq_left cx cx' cy hx)
                    (cutMin_cutEq_right cx' cy cy' hy)

/-- cutMax preserves cutLe on both args. -/
theorem cutMax_cutLe_both (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : cutLe cx1 cx2) (hy : cutLe cy1 cy2) :
    cutLe (cutMax cx1 cy1) (cutMax cx2 cy2) :=
  cutLe_trans _ _ _ (cutMax_cutLe_left cx1 cx2 cy1 hx)
                    (cutMax_cutLe_right cx2 cy1 cy2 hy)

/-- cutMin preserves cutLe on both args. -/
theorem cutMin_cutLe_both (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : cutLe cx1 cx2) (hy : cutLe cy1 cy2) :
    cutLe (cutMin cx1 cy1) (cutMin cx2 cy2) :=
  cutLe_trans _ _ _ (cutMin_cutLe_left cx1 cx2 cy1 hx)
                    (cutMin_cutLe_right cx2 cy1 cy2 hy)

end E213.Lib.Math.NumberSystems.Real213.Lattice.CutLatticeEq
