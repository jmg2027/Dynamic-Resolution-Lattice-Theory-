import E213.Math.Real213.FluxCut

/-!
# Research.Real213FluxCochain

Phase AV-2: **1-cochain construction** on dyadic brackets.

For f : Cut → Cut and a dyadic bracket db, the flux of f along db
is the 1-cochain value at that oriented edge:

  fluxAlong f db := { forward = f(db.rightCut), backward = f(db.leftCut) }

## Cohomology theorems

  fluxAlong_const   : flux of constant function is balanced (∂c = 0)
  fluxAlong_id      : identity's flux gives bracket endpoints
  fluxAlong_compose : flux respects function composition
-/

namespace E213.Math.Real213.FluxCochain

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)

namespace FluxCut

/-- 1-cochain: f's flux along a dyadic bracket edge. -/
def fluxAlong (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) : FluxCut :=
  { forward := f db.rightCut, backward := f db.leftCut }

/-- **Constant function flux is balanced**: ∂c = 0 (cohomology
    vanishing for 0-cochain that's constant). -/
theorem fluxAlong_const (c : Nat → Nat → Bool) (db : DyadicBracket)
    (m k : Nat) :
    (fluxAlong (constCutFn c) db).forward m k
      = (fluxAlong (constCutFn c) db).backward m k := rfl

/-- **Identity flux** = bracket endpoint pair. -/
theorem fluxAlong_id (db : DyadicBracket) :
    fluxAlong id db = { forward := db.rightCut, backward := db.leftCut } :=
  rfl

/-- **Function composition respects flux**: flux of (g ∘ f) is g
    applied componentwise to flux of f. -/
theorem fluxAlong_compose (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) :
    fluxAlong (g ∘ f) db
      = { forward := g ((fluxAlong f db).forward),
          backward := g ((fluxAlong f db).backward) } := rfl

/-- The forward component of fluxAlong is f at the right endpoint. -/
theorem fluxAlong_forward
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) :
    (fluxAlong f db).forward = f db.rightCut := rfl

/-- The backward component of fluxAlong is f at the left endpoint. -/
theorem fluxAlong_backward
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) :
    (fluxAlong f db).backward = f db.leftCut := rfl

/-- **Balanced flux gives zero coboundary**: when forward = backward
    pointwise, the flux is cohomologically zero. -/
def isBalanced (a : FluxCut) : Prop :=
  ∀ m k, a.forward m k = a.backward m k

/-- Constant flux is always balanced (cohomology of 0-cochain). -/
theorem fluxAlong_const_isBalanced (c : Nat → Nat → Bool)
    (db : DyadicBracket) :
    isBalanced (fluxAlong (constCutFn c) db) :=
  fun m k => fluxAlong_const c db m k

end FluxCut

end E213.Math.Real213.FluxCochain
