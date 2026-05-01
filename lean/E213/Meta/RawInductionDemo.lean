import E213.Firmware.Raw
import E213.Hypervisor.Lens

/-!
# Demo: `Raw.rec` as native `induction` target

With `@[eliminator] def Raw.rec` registered in
`Firmware/Raw.lean`, the standard `induction r` tactic
decomposes a `Raw` term through three cases
(`a`, `b`, `slash x y h ihx ihy`) without any Tree-level
access.

This module re-proves `Raw.fold_signed_swap` using the new
eliminator as a sanity-check that the Phase C3 refactor
actually works.  The `a` / `b` cases exercise `Raw.rec`
directly; the `slash` case delegates to `Raw.fold_swap_hom`
as a black-box (public API only, no Tree internals).
-/

namespace E213.Meta.RawInductionDemo

open E213.Firmware E213.Hypervisor

/-- Demo: swap realises negation on the signed Lens,
    re-proved via `Raw.rec` (no Tree access).  Base cases
    exercise `induction … using Raw.rec`; slash case
    delegates to the homomorphism theorem. -/
theorem raw_fold_signed_swap_demo (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r := by
  induction r using Raw.rec with
  | a =>
      show Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap Raw.a)
         = - Raw.fold (1 : Int) (-1) (· + ·) Raw.a
      rw [Raw.swap_a, Raw.fold_a, Raw.fold_b]
  | b =>
      show Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap Raw.b)
         = - Raw.fold (1 : Int) (-1) (· + ·) Raw.b
      rw [Raw.swap_b, Raw.fold_a, Raw.fold_b]; decide
  | slash x y h _ihx _ihy =>
      exact Raw.fold_swap_hom (1 : Int) (-1) (· + ·) (fun n => -n)
        (by decide) (by decide)
        (fun u v => by show -(u + v) = -u + -v; omega)
        (fun u v => by show u + v = v + u; omega)
        (Raw.slash x y h)

end E213.Meta.RawInductionDemo
