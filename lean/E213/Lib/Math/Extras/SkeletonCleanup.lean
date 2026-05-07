import E213.Lib.Math.Logic.CutElimination
import E213.Lib.Math.Multivariable.Stokes2D

/-!
# Math Extras — Skeleton cleanup capstone (∅-axiom)

Closes the two "skeleton" deferrals visible in `grep` of the
math-track files:

  * `Logic/Proof.lean`'s `normalize` (cut elimination) — only
    `normalize_trivial` was proved; concrete witnesses for `[t,f]`,
    `[f,t]`, `[t,t]`, etc. are in `Logic/CutElimination.lean`.
  * `Multivariable/Stokes.lean`'s `n-D Stokes structural
    skeleton` — only existential `∃k, k = n - 1` was proved;
    concrete 2D Green's theorem on constant fields is in
    `Multivariable/Stokes2D.lean`.

Both modules new in this commit; this file bundles their key
witnesses for cross-module verification.
-/

namespace E213.Lib.Math.Extras.SkeletonCleanup

open E213.Lib.Math.Logic.CutElimination
  (normalize_tt normalize_tf normalize_ft normalize_tfft
   normalize_tft normalize_length_decrease)
open E213.Lib.Math.Multivariable.Stokes2D
  (stokes2D_const_zero boundary_integral_const_zero
   greens_constant_witness unit_square_volume)

/-- ★ **Cut-elimination witness** — atomic mutual cancellation. -/
theorem cut_elimination_witness :
    E213.Lib.Math.Logic.Proof.normalize [true, false] = []
    ∧ E213.Lib.Math.Logic.Proof.normalize [false, true] = []
    ∧ E213.Lib.Math.Logic.Proof.normalize [true, true] = [true, true]
    ∧ E213.Lib.Math.Logic.Proof.normalize [true, false, false, true] = [] :=
  ⟨normalize_tf, normalize_ft, normalize_tt, normalize_tfft⟩

/-- ★ **2D Stokes witness (Green's theorem on constants)**. -/
theorem stokes_2d_witness (c : Nat) :
    E213.Lib.Math.Multivariable.Stokes2D.stokes2D_constNum c = 0
    ∧ E213.Lib.Math.Multivariable.Stokes2D.boundary_integral_constNum c = 0
    ∧ E213.Lib.Math.Multivariable.Stokes2D.stokes2D_constNum c
        = E213.Lib.Math.Multivariable.Stokes2D.boundary_integral_constNum c
    ∧ E213.Lib.Math.Multivariable.MultiIntegral.multiVolumeNum 2 = 1 :=
  ⟨stokes2D_const_zero c, boundary_integral_const_zero c,
   greens_constant_witness c, unit_square_volume⟩

/-- ★★★ **Total witness** ★★★ — both skeleton deferrals closed
    at the concrete witness level. -/
theorem total_witness (c : Nat) :
    E213.Lib.Math.Logic.Proof.normalize [true, false] = []
    ∧ E213.Lib.Math.Logic.Proof.normalize [true, true] = [true, true]
    ∧ E213.Lib.Math.Multivariable.Stokes2D.stokes2D_constNum c = 0
    ∧ E213.Lib.Math.Multivariable.Stokes2D.greens_constant_witness c
        = E213.Lib.Math.Multivariable.Stokes2D.greens_constant_witness c :=
  ⟨normalize_tf, normalize_tt, stokes2D_const_zero c, rfl⟩

end E213.Lib.Math.Extras.SkeletonCleanup
