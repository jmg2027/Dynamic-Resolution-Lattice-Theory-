import E213.Lib.Math.NumberSystems.Real213.FoldReflections

/-!
# The two elliptic generators as cyclic fixtures — ℤ₂ from the folds, ℤ₃ from Eisenstein

`FoldReflections` showed the two folds' product is `S` (`N · R = S`), the order-4 elliptic generator
with `S² = −I` — **projective order 2**, acting on the four-point fixture as the 영무한대 swap.  The
modular group has a *second* elliptic generator `U = [[0, −1], [1, 1]]` (order 6, `U³ = −I` —
**projective order 3**, the Eisenstein/order-6 axis).  Its Möbius action `z ↦ −1/(z+1)` is a
fixed-point-free **3-cycle** on the small fixture `{∞, 0, −1}`:

  `∞ ↦ 0 ↦ −1 ↦ ∞`.

So the two elliptic generators of `PSL(2,ℤ)` realize the two cyclic fixtures whose projective orders
are `2` and `3` — exactly the free factors `PSL(2,ℤ) = ℤ₂ * ℤ₃` (`ModularElliptic`).  The `ℤ₂` factor
is the folds' product `S` (the 영무한대 swap, `FoldReflections`); the `ℤ₃` factor is `U`'s
Eisenstein 3-cycle.  The matrix orders `4` and `6` halve/third to the projective orders `2` and `3`
because the central `−I` (the Cassini sign) acts trivially on the projective line — the same
order-reduction the fold fixture sees.
-/

namespace E213.Lib.Math.NumberSystems.Real213.EllipticCycleFixtures

open E213.Lib.Math.NumberSystems.Real213.ModularElliptic (Mat2 mul I2 negI2 S U)

/-- The order-3 fixture `{∞, 0, −1}` — the support of `U`'s Möbius 3-cycle `z ↦ −1/(z+1)`. -/
inductive T3 where
  | inf
  | zero
  | negOne
  deriving DecidableEq

/-- `U`'s action `z ↦ −1/(z+1)` on the fixture: the 3-cycle `∞ ↦ 0 ↦ −1 ↦ ∞`. -/
def uCyc : T3 → T3
  | .inf => .zero
  | .zero => .negOne
  | .negOne => .inf

/-! ## `uCyc` is a fixed-point-free order-3 cycle -/

/-- `uCyc³ = id` — order 3. -/
theorem uCyc_cube : ∀ x, uCyc (uCyc (uCyc x)) = x := by intro x; cases x <;> rfl

/-- `uCyc` fixes nothing (a genuine 3-cycle, not the identity on any point). -/
theorem uCyc_no_fixed : ∀ x, uCyc x ≠ x := by intro x; cases x <;> decide

/-- `uCyc²` also fixes nothing — the order is exactly 3, not 1. -/
theorem uCyc_sq_no_fixed : ∀ x, uCyc (uCyc x) ≠ x := by intro x; cases x <;> decide

/-! ## Matrix side: the projective orders are 2 and 3 -/

/-- `S` has matrix order 4, projective order 2 (`S² = −I`, `S⁴ = I`) — the folds' product. -/
theorem S_proj_order_2 : mul S S = negI2 ∧ mul (mul (mul S S) S) S = I2 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `U` has matrix order 6, projective order 3 (`U³ = −I`, `U⁶ = I`) — the Eisenstein generator. -/
theorem U_proj_order_3 :
    mul (mul U U) U = negI2 ∧ mul (mul (mul (mul (mul U U) U) U) U) U = I2 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ★★★★ **The two elliptic generators are the ℤ₂ and ℤ₃ of `PSL(2,ℤ) = ℤ₂ * ℤ₃`.**  `S`
    (projective order 2, `S² = −I`) is the folds' product — the 영무한대 swap of `FoldReflections`;
    `U` (projective order 3, `U³ = −I`) is a fixed-point-free 3-cycle on the Eisenstein fixture
    `{∞, 0, −1}`.  Their projective orders `2, 3` are the free factors of the modular group; the
    matrix orders `4, 6` reduce to them through the central `−I`. -/
theorem elliptic_generators_are_two_and_three :
    (mul S S = negI2)
    ∧ (mul (mul U U) U = negI2)
    ∧ (∀ x, uCyc (uCyc (uCyc x)) = x)
    ∧ (∀ x, uCyc x ≠ x)
    ∧ (∀ x, uCyc (uCyc x) ≠ x) :=
  ⟨by decide, by decide, uCyc_cube, uCyc_no_fixed, uCyc_sq_no_fixed⟩

end E213.Lib.Math.NumberSystems.Real213.EllipticCycleFixtures
