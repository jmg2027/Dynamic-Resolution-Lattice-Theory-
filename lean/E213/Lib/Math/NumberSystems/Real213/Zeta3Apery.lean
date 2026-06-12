import E213.Lib.Math.NumberTheory.AperyRecurrence
import E213.Lib.Math.NumberSystems.Real213.Zeta3Cut

/-!
# Zeta3Apery — `zeta3Den n = (n!)³·B(n)` (the orbit ↔ binomial-sum bridge)

The repo's `zeta3Den` is defined by the factorial-cleared Apéry recurrence
(`aperyOrbit 1 5`).  `AperyRecurrence.B n = Σ_k C(n,k)²C(n+k,k)²` is the binomial
Apéry number, now proven (`apery_recurrence`) to satisfy Apéry's recurrence.  This
file closes the bridge: **`zeta3Den n = (n!)³·B(n)`**, by 2-step induction — both
sides satisfy the same recurrence (`aperyOrbit_exact` for the orbit, `P_recurrence`
for `(n!)³·B`) with matching seeds `1, 5`.

This identifies the recurrence-defined convergent denominators with the explicit
binomial sums — the last bridge of the recurrence-divisibility route to
`zeta3HolonomicReal`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Zeta3Apery

open E213.Lib.Math.NumberTheory.AperyRecurrence (B aperyLead aperyLead_prod apery_recurrence)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ)
open E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic (aperyBot)
open E213.Lib.Math.NumberSystems.Real213.Zeta3Cut (aperyOrbit zeta3Den aperyOrbit_exact)
open E213.Tactic.NatHelper (add_right_cancel)

/-- The two `aperyLead` polynomials agree: `34m³+153m²+231m+117`. -/
theorem aperyLead_eq (m : Nat) :
    aperyLead m = E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic.aperyLead m := by
  rw [aperyLead_prod]
  unfold E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic.aperyLead
  ring_nat

/-- The cleared Apéry number `P n = (n!)³·B n`. -/
def P (n : Nat) : Nat := factorial n * factorial n * factorial n * B n

/-- `P` satisfies the orbit recurrence (additive form):
    `P(m+2) + (aperyBot m)²·P(m) = aperyLead(m)·P(m+1)`.  From `apery_recurrence`
    times `((m+1)!)³`, using `(m+2)!=(m+2)(m+1)!`, `(m+1)!=(m+1)m!`. -/
theorem P_recurrence (m : Nat) :
    P (m + 2) + aperyBot m * aperyBot m * P m
      = E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic.aperyLead m * P (m + 1) := by
  have hrec := apery_recurrence m
  have hf2 : factorial (m + 2) = (m + 2) * factorial (m + 1) := factorial_succ (m + 1)
  have hf1 : factorial (m + 1) = (m + 1) * factorial m := factorial_succ m
  unfold P aperyBot
  calc factorial (m + 2) * factorial (m + 2) * factorial (m + 2) * B (m + 2)
          + (m + 1) * (m + 1) * (m + 1) * ((m + 1) * (m + 1) * (m + 1))
              * (factorial m * factorial m * factorial m * B m)
      = (factorial (m + 1) * factorial (m + 1) * factorial (m + 1))
          * ((m + 2) * (m + 2) * (m + 2) * B (m + 2) + (m + 1) * (m + 1) * (m + 1) * B m) := by
        rw [hf2, hf1]; ring_nat
    _ = (factorial (m + 1) * factorial (m + 1) * factorial (m + 1)) * (aperyLead m * B (m + 1)) := by
        rw [hrec]
    _ = E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic.aperyLead m
          * (factorial (m + 1) * factorial (m + 1) * factorial (m + 1) * B (m + 1)) := by
        rw [aperyLead_eq]; ring_nat

/-- ★★★ **The orbit ↔ binomial-sum bridge**: `zeta3Den n = (n!)³·B(n)`.
    2-step induction; both satisfy the same recurrence with seeds `1, 5`. -/
theorem zeta3Den_eq (n : Nat) : zeta3Den n = P n := by
  have key : ∀ n, zeta3Den n = P n ∧ zeta3Den (n + 1) = P (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by decide, by decide⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have hex : zeta3Den (m + 2) + aperyBot m * aperyBot m * zeta3Den m
          = E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic.aperyLead m * zeta3Den (m + 1) :=
        aperyOrbit_exact 1 5 (by decide) m
      have hP := P_recurrence m
      rw [ih.1, ih.2, ← hP] at hex
      exact add_right_cancel hex
  exact (key n).1

end E213.Lib.Math.NumberSystems.Real213.Zeta3Apery
