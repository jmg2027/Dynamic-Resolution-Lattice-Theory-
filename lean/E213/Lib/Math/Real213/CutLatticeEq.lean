import E213.Lib.Math.Real213.CutMaxMin
import E213.Lib.Math.Real213.CutPoset

import E213.Lib.Math.Real213.Core
/-!
# CutLatticeEq: cutMax/cutMin preserve cutEq + cutLe

Compatibility of lattice ops with the cut order/equiv structure.
-/

namespace E213.Lib.Math.Real213.CutLatticeEq

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.CutPoset (cutLe cutEq cutEq_trans cutLe_trans)
open E213.Lib.Math.Real213.CutMaxMin (cutMax cutMin)
open E213.Lib.Math.Real213.Core (Real213)

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

/-- cutMax preserves cutLe on left arg. -/
theorem cutMax_cutLe_left (cx1 cx2 cy : Nat → Nat → Bool)
    (h : cutLe cx1 cx2) :
    cutLe (cutMax cx1 cy) (cutMax cx2 cy) := fun m k h_max => by
  show (cx1 m k && cy m k) = true
  have h_max' : (cx2 m k && cy m k) = true := h_max
  rw [Bool.and_eq_true] at h_max'
  rw [Bool.and_eq_true]
  exact ⟨h m k h_max'.1, h_max'.2⟩

/-- cutMax preserves cutLe on right arg. -/
theorem cutMax_cutLe_right (cx cy1 cy2 : Nat → Nat → Bool)
    (h : cutLe cy1 cy2) :
    cutLe (cutMax cx cy1) (cutMax cx cy2) := fun m k h_max => by
  show (cx m k && cy1 m k) = true
  have h_max' : (cx m k && cy2 m k) = true := h_max
  rw [Bool.and_eq_true] at h_max'
  rw [Bool.and_eq_true]
  exact ⟨h_max'.1, h m k h_max'.2⟩

/-- cutMin preserves cutLe on left arg. -/
theorem cutMin_cutLe_left (cx1 cx2 cy : Nat → Nat → Bool)
    (h : cutLe cx1 cx2) :
    cutLe (cutMin cx1 cy) (cutMin cx2 cy) := fun m k h_min => by
  show (cx1 m k || cy m k) = true
  have h_min' : (cx2 m k || cy m k) = true := h_min
  rw [Bool.or_eq_true] at h_min'
  rw [Bool.or_eq_true]
  rcases h_min' with h1 | h2
  · exact Or.inl (h m k h1)
  · exact Or.inr h2

/-- cutMin preserves cutLe on right arg. -/
theorem cutMin_cutLe_right (cx cy1 cy2 : Nat → Nat → Bool)
    (h : cutLe cy1 cy2) :
    cutLe (cutMin cx cy1) (cutMin cx cy2) := fun m k h_min => by
  show (cx m k || cy1 m k) = true
  have h_min' : (cx m k || cy2 m k) = true := h_min
  rw [Bool.or_eq_true] at h_min'
  rw [Bool.or_eq_true]
  rcases h_min' with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (h m k h2)

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

end E213.Lib.Math.Real213.CutLatticeEq
