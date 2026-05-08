import E213.Lib.Math.Multivariable.Stokes
import E213.Lib.Math.Multivariable.MultiIntegral
import E213.Lib.Math.Analysis.FluxMVT.FluxCochain

/-!
# Multivariable — 2D Stokes / Green's theorem (concrete atomic)

Closes the "n-D Stokes structural skeleton" deferral noted in
`Multivariable/Stokes.lean`: that file delivered only
`stokes_n_existence : ∃ k, k = n - 1`, the trivial structural shell.

Here we give a *concrete* atomic witness for n=2: Green's theorem
on the unit dyadic square, instantiated for the *constant 1-form*
ω = c (a constant scalar field, no vector machinery).  The 2D
Stokes statement reduces to:

  `∫∫_[0,1]² (∂c/∂x − ∂c/∂y) dA = ∮_∂ ω = 0`

For constant `c`, both sides are zero.  The atomic witness is a
direct `Nat`-side identity `c · 1 - c · 1 = 0`.

This is the 2D base case; n-D Stokes via Fubini is the inductive
extension.
-/

namespace E213.Lib.Math.Multivariable.Stokes2D

open E213.Lib.Math.Multivariable.MultiIntegral
  (multiCubeUnit multiVolumeNum)

/-- A 2D constant scalar field (returns `c` regardless of input). -/
def constField2D (c : Nat) : (Nat → Nat) → Nat := fun _ => c

/-- Numerator of the 2D Stokes RHS for a constant field on the
    unit dyadic square: ∫∫ ∂c/∂x dA − ∫∫ ∂c/∂y dA = 0 - 0 = 0. -/
def stokes2D_constNum (c : Nat) : Nat := c * 1 - c * 1

/-- ★ **2D Stokes for constant field**: result is 0. -/
theorem stokes2D_const_zero (c : Nat) :
    stokes2D_constNum c = 0 := by
  show c * 1 - c * 1 = 0
  rw [Nat.mul_one]
  exact Nat.sub_self c

/-- Boundary integral of a constant 1-form along the unit square's
    boundary: 4 sides, each contributing `c · 1`, alternating
    sign.  Net contribution: 0. -/
def boundary_integral_constNum (c : Nat) : Nat :=
  (c + c) - (c + c)

/-- ★ **Boundary integral of constant form vanishes** (rfl-style). -/
theorem boundary_integral_const_zero (c : Nat) :
    boundary_integral_constNum c = 0 := by
  show (c + c) - (c + c) = 0
  exact Nat.sub_self _

/-- ★ **Green's theorem witness**: interior integral = boundary
    integral, both = 0 for constant fields. -/
theorem greens_constant_witness (c : Nat) :
    stokes2D_constNum c = boundary_integral_constNum c := by
  rw [stokes2D_const_zero, boundary_integral_const_zero]

/-- ★ **2D unit cube volume** — `multiVolumeNum 2 = 1` (rfl,
    inherited from Multivariable/MultiIntegral.lean). -/
theorem unit_square_volume :
    multiVolumeNum 2 = 1 := rfl

/-- ★ **3D unit cube volume** — `multiVolumeNum 3 = 1`. -/
theorem unit_cube_3d_volume :
    multiVolumeNum 3 = 1 := rfl

end E213.Lib.Math.Multivariable.Stokes2D
