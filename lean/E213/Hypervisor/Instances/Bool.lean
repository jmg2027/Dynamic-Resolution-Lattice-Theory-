import E213.Firmware.Raw
import E213.HypervisorCore
import E213.Hypervisor.Characterisation.Catalog

/-!
# Bool-valued Lenses — swap-blind vs swap-visible

Three natural Bool Lenses illustrate the spectrum:

- **AND Lens**: `a ↦ true`, `b ↦ true`, `combine = and` — swap-blind.
- **OR Lens**:  `a ↦ true`, `b ↦ true`, `combine = or`  — swap-blind.
- **XOR Lens**: `a ↦ true`, `b ↦ false`, `combine = xor` — swap-visible.

The XOR Lens is swap-visible (swap flips the Bool) but FAILS the
`ConjugationCodomain` typeclass: the involution candidate
`conj = not` does not satisfy the distributivity requirement
(conj does not distribute over xor).

Formally establishing this rules out the XOR Lens as a
self-recognising Lens.  By contrast, the `signedLens` on `Int`
(in `Hypervisor/Lens/Characterisation/Catalog.lean`) DOES
satisfy `ConjugationCodomain`, verifying that the conjugation
clause is a strong restriction.
-/

namespace E213.Hypervisor.Instances.Bool
open E213.Firmware E213.Hypervisor

-- ═══ Swap-blind Bool lenses ═══

def boolAndLens : Hypervisor.Lens Bool where
  base_a  := true
  base_b  := true
  combine := (· && ·)

def boolOrLens : Hypervisor.Lens Bool where
  base_a  := true
  base_b  := true
  combine := (· || ·)

-- Swap-blindness is immediate from `base_a = base_b` + the
-- `swap_invariant_base_eq` converse.  View is constantly `true`.

theorem boolAndLens_view_const (r : Raw) : boolAndLens.view r = true := by
  show Raw.fold true true (· && ·) r = true
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      rw [Raw.fold_slash _ _ _ (fun u v => by cases u <;> cases v <;> rfl) x y h,
          ihx, ihy]
      decide

theorem boolOrLens_view_const (r : Raw) : boolOrLens.view r = true := by
  show Raw.fold true true (· || ·) r = true
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      rw [Raw.fold_slash _ _ _ (fun u v => by cases u <;> cases v <;> rfl) x y h,
          ihx, ihy]
      decide

end E213.Hypervisor.Instances.Bool
namespace E213.Hypervisor.Instances.Bool
open E213.Firmware E213.Hypervisor

-- ═══ Swap-visible Bool lens: XOR ═══

/-- XOR lens: `a ↦ true`, `b ↦ false`, combine = `xor`.
    Base values differ; swap flips the image.  But this Lens
    FAILS R4: the natural involution candidate `conj = not`
    does not satisfy the homomorphism condition (conj does not
    distribute over xor in the right way). -/
def boolXorLens : Hypervisor.Lens Bool where
  base_a  := true
  base_b  := false
  combine := xor

/-- `not` is an involution on Bool. -/
theorem bool_not_involutive : ∀ u : Bool, !(!u) = u := by decide

/-- `not` on Bool is NOT the identity. -/
theorem bool_not_ne_id : (!·) ≠ (id : Bool → Bool) := by
  intro h
  have : (!true) = id true := congrFun h true
  exact absurd this (by decide)

/-- **R4 fails for `boolXorLens`.**  The homomorphism clause
    (Lens.combine distributing over `not`) is what fails:
    explicitly, `!(true xor false) = false` but
    `(!true) xor (!false) = false xor true = true`. -/
theorem boolXorLens_not_homomorphism :
    ¬ (∀ u v : Bool, !(xor u v) = xor (!u) (!v)) := by
  intro h
  have := h true false
  -- `!(true xor false) = xor (!true) (!false) = xor false true`
  -- LHS = !true = false; RHS = xor false true = true
  revert this; decide

end E213.Hypervisor.Instances.Bool