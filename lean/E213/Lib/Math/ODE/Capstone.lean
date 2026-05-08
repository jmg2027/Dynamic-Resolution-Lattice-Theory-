import E213.Lib.Math.ODE.PicardIterate
import E213.Lib.Math.ODE.LinearODE
import E213.Lib.Math.ODE.HeatEqDiscrete
import E213.Lib.Math.ODE.WaveEqDiscrete

/-!
# Differential Equations 213 — Capstone synthesis

5 cluster witnesses + total bundle.  All ∅-axiom.

213-native paradigm: ODE solution = Picard iteration trajectory;
PDE on a finite periodic grid is purely combinatorial; no
existence-theorem chase, no analytic-completeness arguments.
-/

namespace E213.Lib.Math.ODE.Capstone

open E213.Lib.Math.ODE.PicardIterate
  (picardIterate constRHS expRHS picard_const picard_exp)
open E213.Lib.Math.ODE.LinearODE
  (linearGrowth geometricGrowth linearODE_eq_picard
   geometricODE_eq_picard geometricGrowth_three)
open E213.Lib.Math.ODE.HeatEqDiscrete
  (heatStepNum constInit heatStep_const_eq_two_c)
open E213.Lib.Math.ODE.WaveEqDiscrete
  (waveStepNum constField wave_const_rest wave_zero_rest)

/-- ★ **Picard witness** — constant + exponential RHS closed forms. -/
theorem picard_witness (y0 a n : Nat) :
    picardIterate y0 (constRHS a) n = y0 + n * a
    ∧ picardIterate y0 expRHS n = y0 * 2 ^ n :=
  ⟨picard_const y0 a n, picard_exp y0 n⟩

/-- ★ **Linear ODE witness** — `y' = a` and `y' = y` Euler-step. -/
theorem linearODE_witness (y0 a n : Nat) :
    linearGrowth y0 a n = picardIterate y0 (constRHS a) n
    ∧ geometricGrowth y0 n = picardIterate y0 expRHS n
    ∧ geometricGrowth y0 3 = y0 * 8 :=
  ⟨linearODE_eq_picard y0 a n,
   geometricODE_eq_picard y0 n,
   geometricGrowth_three y0⟩

/-- ★ **Heat-equation witness** — constant equilibrium preserved. -/
theorem heat_witness (n c x : Nat) :
    heatStepNum n (constInit c) x = 2 * c :=
  heatStep_const_eq_two_c n c x

/-- ★ **Wave-equation witness** — rest field + zero field preserved. -/
theorem wave_witness (n c x : Nat) :
    waveStepNum n (constField c) (constField c) x = c
    ∧ waveStepNum n (constField 0) (constField 0) x = 0 :=
  ⟨wave_const_rest n c x, wave_zero_rest n x⟩

/-- ★★★ **Total witness** ★★★ — 5-fact bundle covering ODE
    (constant, exponential), heat PDE, wave PDE. -/
theorem total_witness (y0 a n c x : Nat) :
    picardIterate y0 (constRHS a) n = y0 + n * a
    ∧ picardIterate y0 expRHS n = y0 * 2 ^ n
    ∧ linearGrowth y0 a n = picardIterate y0 (constRHS a) n
    ∧ heatStepNum n (constInit c) x = 2 * c
    ∧ waveStepNum n (constField c) (constField c) x = c :=
  ⟨picard_const y0 a n, picard_exp y0 n,
   linearODE_eq_picard y0 a n,
   heatStep_const_eq_two_c n c x,
   wave_const_rest n c x⟩

end E213.Lib.Math.ODE.Capstone
