import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Meta.Lens.Catalog
import E213.Prelude

/-!
# Meta.ZMod6Lens: R3 (no zero divisors) fail witness

`zmod6Lens : Lens Nat` with `base_a = 2`, `base_b = 3`,
`combine u v = (u * v) % 6`.

**Purpose.**  Supplies the R3-failure side of the catalogue:
the combine has a **zero divisor**, because the modulus `6`
is composite.  `combine 2 3 = (2 * 3) % 6 = 0` even though
`2 ≠ 0` and `3 ≠ 0`.

Combined with `boolXorLens` / `parityLens` / `maxLens`
(R4-fail, three distinct mechanisms) and `parityLens` /
`maxLens` (R5-fail), this rounds out the catalogue with a
clean witness for **each** R3/R4/R5 predicate being strict
— no one of them is redundant.

The ℤ/6 arithmetic is reproduced on `Nat` rather than
`ZMod 6` to avoid Mathlib — core Lean supplies `Nat.mul`
and `Nat.mod`, which is all we need.
-/

namespace E213.Meta.Lens.ZMod6

open E213.Firmware E213.Hypervisor

/-- **ZMod-6 multiplicative lens.**  `a ↦ 2`, `b ↦ 3`,
    `combine u v = (u * v) mod 6`. -/
def zmod6Lens : Hypervisor.Lens Nat where
  base_a  := 2
  base_b  := 3
  combine := fun u v => (u * v) % 6

-- Direct view values on base + first composite.

example : zmod6Lens.view Raw.a = 2 := rfl
example : zmod6Lens.view Raw.b = 3 := rfl
example : zmod6Lens.view (Raw.slash Raw.a Raw.b (by decide)) = 0 := rfl

-- ═══ R3 fails ═══

/-- **R3 (NonVanishing) fails for `zmod6Lens`.**  Explicit
    witness `u = 2, v = 3`: neither is `0`, yet
    `combine 2 3 = (6 % 6) = 0`. -/
theorem zmod6Lens_R3_fails : ¬ NonVanishing zmod6Lens := by
  intro h
  have hne : zmod6Lens.combine 2 3 ≠ 0 :=
    h 2 3 (by decide) (by decide)
  have : zmod6Lens.combine 2 3 = 0 := by decide
  exact hne this

end E213.Meta.Lens.ZMod6

namespace E213.Meta.Lens.ZMod6

open E213.Firmware E213.Hypervisor

/-- **Commutative combine.**  `zmod6Lens.combine` is commutative
    (inherits from `Nat` multiplication) — so R2 is OK.  The
    failure is purely at R3. -/
theorem zmod6Lens_combine_comm :
    ∀ u v : Nat, zmod6Lens.combine u v = zmod6Lens.combine v u := by
  intro u v
  show (u * v) % 6 = (v * u) % 6
  rw [Nat.mul_comm]

/-- Every Raw `r ≠ Raw.a` whose construction passes through
    `Raw.slash a b` inherits view `0`: the R3-failure zero
    absorbs.  Concrete two-witness case:
    `slash a (slash a b)` and `slash b (slash a b)` both
    have view `0`, giving a second R5-injectivity failure. -/
example :
    zmod6Lens.view (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide))
        (by decide))
      = zmod6Lens.view (Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide))
        (by decide)) := by decide

end E213.Meta.Lens.ZMod6
