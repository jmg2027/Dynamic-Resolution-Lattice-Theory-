import E213.Lib.Math.NumberSystems.SignedCut.Core.Core

/-!
# SignedCut — algebraic identities (∅-axiom)

Group structure on `SignedCut` via the pair representation.

Atomic content:
  * `signedNeg` is involutive (rfl): `−(−s) = s`.
  * `signedSub s s = (a + b, b + a)` — sub-self gives a balanced pair.
  * Identity element behaviors of `zero`, `one`, `negOne`.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Core.Algebra

open E213.Lib.Math.NumberSystems.SignedCut.Core.Core
  (SignedCut zero one negOne ofPos ofNeg pos neg
   signedNeg signedAdd signedSub signedMul)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- ★ **Negation is involutive** (rfl).  Consumed by `Core/Capstone`. -/
theorem signedNeg_involutive (s : SignedCut) :
    signedNeg (signedNeg s) = s := rfl

/-- ★ **`−one = negOne`** (rfl).  Consumed by `Core/Capstone`. -/
theorem signedNeg_one : signedNeg one = negOne := rfl

/-- ★ **`signedSub s s = (s.1 + s.2, s.2 + s.1)`** (sub-self gives a
    balanced pair that structurally reads as 0 (difference-Lens
    readout) modulo cutSum commutativity).  Consumed by `Core/Capstone`. -/
theorem signedSub_self (s : SignedCut) :
    signedSub s s
      = (E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum s.1 s.2,
         E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum s.2 s.1) := rfl

/-- ★ **`signedAdd s zero = (s.1 + 0, s.2 + 0)`** (rfl).
    Consumed by `Core/Capstone`. -/
theorem signedAdd_zero_right (s : SignedCut) :
    signedAdd s zero
      = (E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum s.1 (constCut 0 1),
         E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum s.2 (constCut 0 1)) := rfl

/-- ★ SignedCut algebraic identities master — additional rfl facts
    that the externally-consumed theorems above do not cover.
    Bundles `−zero = zero`, `−negOne = one`, per-element pos/neg
    component values for {zero, one, negOne}, and ofPos/ofNeg
    component identities. -/
theorem signedCut_algebra_master :
    -- Negation identity on extremal elements
    signedNeg zero = zero
    ∧ signedNeg negOne = one
    -- Per-element component values
    ∧ (pos zero = constCut 0 1 ∧ neg zero = constCut 0 1)
    ∧ (pos one = constCut 1 1 ∧ neg one = constCut 0 1)
    ∧ (pos negOne = constCut 0 1 ∧ neg negOne = constCut 1 1)
    -- ofPos / ofNeg components
    ∧ (∀ c : Nat → Nat → Bool,
        pos (ofPos c) = c
        ∧ neg (ofPos c) = constCut 0 1
        ∧ pos (ofNeg c) = constCut 0 1
        ∧ neg (ofNeg c) = c) := by
  refine ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  intro _; exact ⟨rfl, rfl, rfl, rfl⟩

end E213.Lib.Math.NumberSystems.SignedCut.Core.Algebra
