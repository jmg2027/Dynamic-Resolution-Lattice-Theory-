import E213.Meta.UniversalLens.Core.Q213
import E213.Meta.UniversalLens.Core.Q213Inj

/-!
# Universal Lens at Q213³ — triple Q213 codomain universality

Extends `q213Lens : Lens (Q213 × Q213)` to `q213Lens3 : Lens (Q213³)`
adding a third Q213 component (leaves catamorphism via Q213.ofNat).

Triple Q213-codomain demonstrates: **adding components to a
universal Q213-codomain lens preserves universality** in the
213-native rational arithmetic.

Closes part of HANDOFF Open Continuation #5.
-/

namespace E213.Meta.UniversalLensQ213_3

open E213.Firmware E213.Hypervisor E213.Kernel
open E213.Meta.UniversalLensNat2 E213.Meta.UniversalLensQ213

/-- Lens at Q213³ = Q213 × (Q213 × Q213).  Three independent
    encodings (mirrors expSumLens3 at Q213 codomain). -/
def q213Lens3 : Lens (Q213 × Q213 × Q213) where
  base_a := (Q213.ofNat 1, Q213.ofNat 0, Q213.ofNat 1)
  base_b := (Q213.ofNat 2, Q213.ofNat 0, Q213.ofNat 1)
  combine x y :=
    let n1 := x.1.1.eval; let m1 := y.1.1.eval
    let n2 := x.2.1.1.eval; let m2 := y.2.1.1.eval
    let n3 := x.2.2.1.eval; let m3 := y.2.2.1.eval
    (Q213.ofNat (2 ^ n1 + 2 ^ m1),
     Q213.ofNat (n2 + m2 + 1),
     Q213.ofNat (n3 + m3))

/-- Combine is symmetric. -/
theorem q213Lens3_symmetric :
    ∀ u v : Q213 × Q213 × Q213,
      q213Lens3.combine u v = q213Lens3.combine v u := by
  intro u v
  show (Q213.ofNat (2^u.1.1.eval + 2^v.1.1.eval),
        Q213.ofNat (u.2.1.1.eval + v.2.1.1.eval + 1),
        Q213.ofNat (u.2.2.1.eval + v.2.2.1.eval))
      = (Q213.ofNat (2^v.1.1.eval + 2^u.1.1.eval),
         Q213.ofNat (v.2.1.1.eval + u.2.1.1.eval + 1),
         Q213.ofNat (v.2.2.1.eval + u.2.2.1.eval))
  congr 1
  · congr 1; exact Nat.add_comm _ _
  congr 1
  · congr 1; omega
  · congr 1; omega

/-- Concrete view: a maps to (1, 0, 1) all in Q213. -/
theorem q213Lens3_view_a :
    q213Lens3.view Raw.a
      = (Q213.ofNat 1, Q213.ofNat 0, Q213.ofNat 1) := rfl

/-- Concrete view: b maps to (2, 0, 1) all in Q213. -/
theorem q213Lens3_view_b :
    q213Lens3.view Raw.b
      = (Q213.ofNat 2, Q213.ofNat 0, Q213.ofNat 1) := rfl

/-- Nat encoding extracted from q213Lens3 view (1st component). -/
def qNat3 (r : Raw) : Nat := (q213Lens3.view r).1.1.eval

/-- ★★★ qNat3 agrees with expSumNat at base + slash recursion. -/
theorem qNat3_eq_expSumNat (r : Raw) : qNat3 r = expSumNat r := by
  induction r using Raw.rec with
  | a =>
    show (q213Lens3.view Raw.a).1.1.eval = expSumNat Raw.a
    rw [q213Lens3_view_a, expSumNat_a]
    exact Q213_ofNat_eval 1
  | b =>
    show (q213Lens3.view Raw.b).1.1.eval = expSumNat Raw.b
    rw [q213Lens3_view_b, expSumNat_b]
    exact Q213_ofNat_eval 2
  | slash x y h ihx ihy =>
    have hview : q213Lens3.view (Raw.slash x y h)
                  = q213Lens3.combine
                      (q213Lens3.view x) (q213Lens3.view y) :=
      Raw.fold_slash _ _ _ q213Lens3_symmetric x y h
    show (q213Lens3.view (Raw.slash x y h)).1.1.eval = _
    rw [hview]
    show (Q213.ofNat (2 ^ qNat3 x + 2 ^ qNat3 y)).1.eval
        = expSumNat (Raw.slash x y h)
    rw [Q213_ofNat_eval, expSumNat_slash, ihx, ihy]

/-- ★★★★★★★★ qNat3 is injective. -/
theorem qNat3_inj : Function.Injective qNat3 := by
  intro r s hrs
  apply expSumNat_inj
  rw [← qNat3_eq_expSumNat, ← qNat3_eq_expSumNat]
  exact hrs

/-- ★★★★★★★★★ q213Lens3.view is INJECTIVE — full universality
    at the 213-native ℚ × ℚ × ℚ codomain. -/
theorem q213Lens3_view_inj : Function.Injective q213Lens3.view := by
  intro r s hrs
  apply qNat3_inj
  show (q213Lens3.view r).1.1.eval = (q213Lens3.view s).1.1.eval
  rw [hrs]

/-- ★★★★★★★★★★ q213Lens3 IS a Universal Lens at Q213³. -/
theorem q213Lens3_is_universal :
    E213.Meta.UniversalLens.IsUniversal q213Lens3 :=
  q213Lens3_view_inj

end E213.Meta.UniversalLensQ213_3
