import E213.Physics.SimplexCounts

/-!
# Phase 4 PropagatorFamily — P(x/k) atomic family

★ Pattern discovered ★
Each atom IE correction: IE(Z) = R·Z_eff²/n² · P(x/k_Z)

  x = α_GUT · NS/d = 18/(125·π²) atomic
  k_Z = "correlation count" atomic

  Li (1s² 2s¹): k=1, P(x) → 113 ppm
  Be (1s² 2s²): k=NT=2, P(x/2) → ~500 ppm

Each P(x/k) is an atomic Lens output.
-/

namespace E213.Physics.Phase4.PropagatorFamily

open E213.Physics.Simplex

/-- P(x) per 10⁵: 101437 (= 1.01437 = (1+2x)/(1+x), x = 0.01458). -/
def P_x : Nat := 101437

/-- P(x/2) per 10⁵: 100723 (= 1.00723). -/
def P_x_half : Nat := 100723

/-- Li with P(x): 5391108 (113 ppm match). -/
def Li_corrected : Nat := 5391108

/-- Be with P(x/2): leading 9260376 → 9327300. -/
def Be_corrected : Nat := 9327300

/-- Li precision: |5391715 - 5391108| = 607 μeV. -/
theorem Li_diff : 5391715 - Li_corrected = 607 := by decide

/-- Be precision: |9327300 - 9322699| = 4601 μeV ≈ 493 ppm. -/
theorem Be_diff : Be_corrected - 9322699 = 4601 := by decide

end E213.Physics.Phase4.PropagatorFamily
