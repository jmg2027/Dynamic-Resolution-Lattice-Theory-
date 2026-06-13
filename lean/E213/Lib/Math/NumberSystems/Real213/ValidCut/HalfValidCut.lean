import E213.Lib.Math.NumberSystems.Real213.ValidCut.IntValidCut
/-!
# HalfValidCut — bundled half-integer cut closing cutSum_assoc at b = 2

Extends `IntValidCut` (integer cuts, b = 1) to **dyadic cuts**
(b = 2) using `cutSum_half_general`.

  `HalfValidCut := { cut, num : Nat, is_half : cutEq cut
  (constCut num 2) }`

cutSum closes the class: cutSum of two half-cuts equals
`constCut (num₁ + num₂) 2`, by `cutSum_half_general`.  Both
parenthesizations reduce to `constCut ((a+b)+c) 2`; `Nat.add_assoc`
finishes.

This **closes b = 2** for the cutSum_assoc frontier.  Together
with `IntValidCut` (b = 1), the dyadic class
(b ∈ {1, 2}) has full cutSum associativity.  At b ≥ 3, the
forward-only `cutSum_same_denom_forward` blocks the backward
direction; full closure there genuinely requires the search-index
reorganization theorem (open).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.HalfValidCut

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq cutEq_refl)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumOne (cutSum_half_general)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumEq
  (cutSum_cutEq_left cutSum_cutEq_right)

/-! ## §1 — HalfValidCut structure -/

/-- A **bundled half-integer cut**: a cut function with a witness
    that it's cutEq to some `constCut · 2`. -/
structure HalfValidCut where
  cut : Nat → Nat → Bool
  /-- The numerator (denominator is fixed at 2). -/
  num : Nat
  /-- The witness: cut is cutEq to `constCut num 2`. -/
  is_half : cutEq cut (constCut num 2)

/-! ## §2 — Constructors -/

/-- The canonical half-integer cut at numerator `a` (= `a/2`). -/
def ofHalf (a : Nat) : HalfValidCut where
  cut := constCut a 2
  num := a
  is_half := cutEq_refl _

/-- Zero (= 0/2). -/
def zero : HalfValidCut := ofHalf 0

/-- One half (= 1/2). -/
def half : HalfValidCut := ofHalf 1

theorem ofHalf_cut (a : Nat) : (ofHalf a).cut = constCut a 2 := rfl

theorem ofHalf_num (a : Nat) : (ofHalf a).num = a := rfl

/-! ## §3 — Bundled cutSum -/

/-- Add two HalfValidCuts; the result represents the numerator sum. -/
def add (vx vy : HalfValidCut) : HalfValidCut where
  cut := cutSum vx.cut vy.cut
  num := vx.num + vy.num
  is_half := by
    intro m k
    rw [cutSum_cutEq_left vx.cut (constCut vx.num 2) vy.cut
          vx.is_half m k]
    rw [cutSum_cutEq_right (constCut vx.num 2) vy.cut
          (constCut vy.num 2) vy.is_half m k]
    exact cutSum_half_general vx.num vy.num m k

theorem add_num (vx vy : HalfValidCut) :
    (add vx vy).num = vx.num + vy.num := rfl

theorem add_cut (vx vy : HalfValidCut) :
    (add vx vy).cut = cutSum vx.cut vy.cut := rfl

/-! ## §4 — Full associativity at b = 2 -/

/-- ★★★★★ **Full cutSum associativity on HalfValidCut**.

    Both parenthesizations reduce to `constCut ((a+b)+c) 2`
    via `cutSum_half_general` + `is_half` witnesses; `Nat.add_assoc`
    finishes. -/
theorem cutSum_assoc_halfValidCut (vx vy vz : HalfValidCut) :
    cutEq (cutSum (cutSum vx.cut vy.cut) vz.cut)
          (cutSum vx.cut (cutSum vy.cut vz.cut)) := by
  intro m k
  have lhs_eq : cutSum (cutSum vx.cut vy.cut) vz.cut m k
              = constCut ((vx.num + vy.num) + vz.num) 2 m k := by
    show (add (add vx vy) vz).cut m k
       = constCut ((vx.num + vy.num) + vz.num) 2 m k
    exact (add (add vx vy) vz).is_half m k
  have rhs_eq : cutSum vx.cut (cutSum vy.cut vz.cut) m k
              = constCut (vx.num + (vy.num + vz.num)) 2 m k := by
    show (add vx (add vy vz)).cut m k
       = constCut (vx.num + (vy.num + vz.num)) 2 m k
    exact (add vx (add vy vz)).is_half m k
  rw [lhs_eq, rhs_eq]
  rw [Nat.add_assoc]

/-! ## §5 — Commutativity bonus -/

/-- ★ **Commutativity** on HalfValidCut via Nat.add_comm. -/
theorem cutSum_comm_halfValidCut (vx vy : HalfValidCut) :
    cutEq (cutSum vx.cut vy.cut) (cutSum vy.cut vx.cut) := by
  intro m k
  have lhs_eq : cutSum vx.cut vy.cut m k
              = constCut (vx.num + vy.num) 2 m k :=
    (add vx vy).is_half m k
  have rhs_eq : cutSum vy.cut vx.cut m k
              = constCut (vy.num + vx.num) 2 m k :=
    (add vy vx).is_half m k
  rw [lhs_eq, rhs_eq]
  rw [Nat.add_comm]

/-! ## §6 — Capstone -/

/-- ★★★★★ **Full cutSum_assoc closure at b = 2 via HalfValidCut**.

    Bundles: (a) HalfValidCut structure with cut + num + is_half
    witness, (b) ofHalf / zero / half / add constructors,
    (c) full associativity at b = 2 (via cutSum_half_general),
    (d) commutativity bonus, (e) add_num / add_cut computation.

    Reading: the bundled-subtype pattern extends naturally from
    b = 1 (IntValidCut) to b = 2 (HalfValidCut).  Both
    parenthesizations reduce to the same constCut via the b-fixed
    cutSum identity (`cutSum_int_int` at b=1, `cutSum_half_general`
    at b=2); `Nat.add_assoc` finishes.

    At b ≥ 3, the forward-only `cutSum_same_denom_forward` blocks
    backward closure; full closure there requires search-index
    reorganization (open frontier). -/
theorem halfvalidcut_full_assoc_capstone (vx vy vz : HalfValidCut) :
    -- (a) Add preserves the half class
    (add vx vy).num = vx.num + vy.num
    -- (b) Full associativity at b = 2
    ∧ cutEq (cutSum (cutSum vx.cut vy.cut) vz.cut)
            (cutSum vx.cut (cutSum vy.cut vz.cut))
    -- (c) Commutativity
    ∧ cutEq (cutSum vx.cut vy.cut) (cutSum vy.cut vx.cut)
    -- (d) Canonical values
    ∧ zero.num = 0
    ∧ half.num = 1 := by
  refine ⟨rfl, ?_, ?_, rfl, rfl⟩
  · exact cutSum_assoc_halfValidCut vx vy vz
  · exact cutSum_comm_halfValidCut vx vy

end E213.Lib.Math.NumberSystems.Real213.HalfValidCut
