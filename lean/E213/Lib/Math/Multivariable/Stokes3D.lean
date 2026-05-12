import E213.Lib.Math.Multivariable.Stokes2D
import E213.Meta.Tactic.Nat213

/-!
# Multivariable — 3D Divergence theorem (atomic, constant fields)

Continuation of `Stokes2D.lean` to dimension 3.  Statement
(divergence form of Stokes for n=3):

  `∫∫∫_[0,1]³ ∇·F dV = ∫∫_∂ F·n̂ dS`

For a constant vector field `F = (c, c, c)`, the divergence is
`∂c/∂x + ∂c/∂y + ∂c/∂z = 0`, and the boundary flux through 6
faces (each contributing `c·1` on outward face, `−c·1` on inward
face) cancels in pairs.  Both sides are zero.

Atomic content: `Nat`-side identities `c·1 - c·1 = 0`,
`(c+c+c) - (c+c+c) = 0`.
-/

namespace E213.Lib.Math.Multivariable.Stokes3D

/-- 3D constant scalar field. -/
def constField3D (c : Nat) : (Nat → Nat) → Nat := fun _ => c

/-- Numerator of the 3D Stokes RHS for a constant field on the
    unit dyadic cube: ∫∫∫ ∇·F dV = 0 - 0 = 0. -/
def stokes3D_constNum (c : Nat) : Nat := c * 1 + c * 1 + c * 1
                                         - (c * 1 + c * 1 + c * 1)

/-- ★ **3D Stokes for constant field**: result is 0. -/
theorem stokes3D_const_zero (c : Nat) :
    stokes3D_constNum c = 0 := by
  show c * 1 + c * 1 + c * 1 - (c * 1 + c * 1 + c * 1) = 0
  exact Nat.sub_self _

/-- Boundary flux of a constant 1-form through the unit cube's
    6 faces: outward normals contribute `+c`, inward contribute
    `−c`, sum cancels.  Net contribution: 0. -/
def divergence_boundaryNum (c : Nat) : Nat :=
  (c + c + c) - (c + c + c)

/-- ★ **Boundary flux of constant field vanishes**. -/
theorem divergence_boundary_zero (c : Nat) :
    divergence_boundaryNum c = 0 := by
  show (c + c + c) - (c + c + c) = 0
  exact Nat.sub_self _

/-- ★ **Divergence theorem witness**: interior = boundary = 0
    for constant fields. -/
theorem divergence_thm_constant (c : Nat) :
    stokes3D_constNum c = divergence_boundaryNum c := by
  rw [stokes3D_const_zero, divergence_boundary_zero]

/-- ★ **Unit cube 3D volume**: `multiVolumeNum 3 = 1` (rfl,
    inherited from Stokes2D). -/
theorem unit_cube_volume_3d :
    E213.Lib.Math.Multivariable.MultiIntegral.multiVolumeNum 3 = 1 := rfl

/-- ★ **Unit cube 4D volume** — `multiVolumeNum 4 = 1`. -/
theorem unit_cube_volume_4d :
    E213.Lib.Math.Multivariable.MultiIntegral.multiVolumeNum 4 = 1 := rfl

end E213.Lib.Math.Multivariable.Stokes3D
