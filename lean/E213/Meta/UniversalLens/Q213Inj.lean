import E213.Meta.UniversalLens.Q213
import E213.Meta.UniversalLens.Nat2Inj

/-!
# q213Lens.view full injectivity (Open Problem #6 ℚ²-discrete CLOSED)

Strategy: define `qNat r := (q213Lens.view r).1.1.eval` and show
this equals `expSumNat r`.  Then injectivity follows from
`expSumNat_inj`.

Key bridge lemma: `(Q213.ofNat n).1.eval = n` (round-trip).
-/

namespace E213.Meta.UniversalLens.Q213Inj

open E213.Theory E213.Lens E213.Term
open E213.Meta.UniversalLens.Q213 (Q213 q213Lens q213Lens_symmetric q213Lens_view_a q213Lens_view_b)
open E213.Meta.UniversalLens.Nat2Inj (expSumNat expSumNat_a expSumNat_b expSumNat_inj)

/-- Round-trip: encoding then evaluating recovers the Nat. -/
theorem Q213_ofNat_eval (n : Nat) : (Q213.ofNat n).1.eval = n := by
  show (Q213.ofNat.build n).eval = n
  induction n with
  | zero => rfl
  | succ k ih =>
    show (Term.succ (Q213.ofNat.build k)).eval = k + 1
    show Nat.succ (Q213.ofNat.build k).eval = k + 1
    rw [ih]

/-- Nat encoding extracted from q213Lens view. -/
def qNat (r : Raw) : Nat := (q213Lens.view r).1.1.eval

/-- ★★★ qNat agrees with expSumNat at base values and slash recursion. -/
theorem qNat_eq_expSumNat (r : Raw) : qNat r = expSumNat r := by
  induction r using Raw.rec with
  | a =>
    show (q213Lens.view Raw.a).1.1.eval = expSumNat Raw.a
    rw [q213Lens_view_a, expSumNat_a]
    exact Q213_ofNat_eval 1
  | b =>
    show (q213Lens.view Raw.b).1.1.eval = expSumNat Raw.b
    rw [q213Lens_view_b, expSumNat_b]
    exact Q213_ofNat_eval 2
  | slash x y h ihx ihy =>
    have hview : q213Lens.view (Raw.slash x y h)
                  = q213Lens.combine (q213Lens.view x) (q213Lens.view y) :=
      Raw.fold_slash _ _ _ q213Lens_symmetric x y h
    show (q213Lens.view (Raw.slash x y h)).1.1.eval = _
    rw [hview]
    show (Q213.ofNat (2 ^ qNat x + 2 ^ qNat y)).1.eval
        = expSumNat (Raw.slash x y h)
    rw [Q213_ofNat_eval,
        E213.Meta.UniversalLens.Nat2Inj.expSumNat_slash _ _ h, ihx, ihy]

/-- ★★★★★★★★ qNat is injective (via correspondence with expSumNat). -/
theorem qNat_inj : Function.Injective qNat := by
  intro r s hrs
  apply expSumNat_inj
  rw [← qNat_eq_expSumNat, ← qNat_eq_expSumNat]
  exact hrs

/-- ★★★★★★★★★ q213Lens.view is INJECTIVE — full universality
    at the 213-native ℚ × ℚ codomain. -/
theorem q213Lens_view_inj : Function.Injective q213Lens.view := by
  intro r s hrs
  apply qNat_inj
  show (q213Lens.view r).1.1.eval = (q213Lens.view s).1.1.eval
  rw [hrs]

/-- ★★★★★★★★★★ q213Lens IS a Universal Lens in the
    `IsUniversal` metatheory sense.  Open Problem #6 ℚ²-discrete
    refinement: STRUCTURALLY CLOSED. -/
theorem q213Lens_is_universal :
    E213.Meta.UniversalLens.Core.IsUniversal q213Lens :=
  q213Lens_view_inj

end E213.Meta.UniversalLens.Q213Inj
