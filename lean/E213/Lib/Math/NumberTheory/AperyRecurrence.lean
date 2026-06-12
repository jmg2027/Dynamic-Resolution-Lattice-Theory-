import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# AperyRecurrence — the binomial Apéry numbers `Bₙ = Σ_k C(n,k)²C(n+k,k)²`

The denominator Apéry numbers as an explicit binomial sum (manifestly `ℕ`).  The
**nucleus** of the ζ(3) program (see `research-notes/frontiers/zeta3_blueprint.md`,
"THE NUCLEUS") is the recurrence

  `(j+2)³·B(j+2) + (j+1)³·B(j) = aperyLead(j)·B(j+1)`,   `aperyLead j = 34j³+153j²+231j+117`

(subtraction-free additive form).  This is **Apéry's recurrence** = the WZ /
creative-telescoping identity; once proven, `zeta3Den n = (n!)³·B(n)` follows by
induction (seeds `B 0 = 1`, `B 1 = 5` match), closing the recurrence-divisibility
route to `zeta3HolonomicReal`.

This file pins the *definition* and validates the recurrence on base layers; the
general identity is the recorded research frontier.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AperyRecurrence

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-- The Apéry summand `C(n,k)²·C(n+k,k)²` (squares as explicit products). -/
def aperySummand (n k : Nat) : Nat :=
  choose n k * choose n k * (choose (n + k) k * choose (n + k) k)

/-- The denominator Apéry number `Bₙ = Σ_{k=0}^n C(n,k)²·C(n+k,k)²`. -/
def B (n : Nat) : Nat := sumTo (n + 1) (aperySummand n)

/-- `aperyLead j = 34j³+153j²+231j+117` — the leading Apéry polynomial (matches
    `DepthAperyCubic.aperyLead` as a polynomial in `j`). -/
def aperyLead (j : Nat) : Nat := 34 * j ^ 3 + 153 * j ^ 2 + 231 * j + 117

/-- Seeds: `B 0 = 1`, `B 1 = 5` (match `zeta3Den 0, zeta3Den 1`). -/
theorem B_zero : B 0 = 1 := by decide
theorem B_one : B 1 = 5 := by decide
theorem B_two : B 2 = 73 := by decide
theorem B_three : B 3 = 1445 := by decide

/-- The Apéry recurrence on base layers (validation of the nucleus statement).
    The general `∀ j` form is the WZ frontier. -/
theorem apery_recurrence_at0 :
    (0 + 2) ^ 3 * B (0 + 2) + (0 + 1) ^ 3 * B 0 = aperyLead 0 * B (0 + 1) := by decide
theorem apery_recurrence_at1 :
    (1 + 2) ^ 3 * B (1 + 2) + (1 + 1) ^ 3 * B 1 = aperyLead 1 * B (1 + 1) := by decide
theorem apery_recurrence_at2 :
    (2 + 2) ^ 3 * B (2 + 2) + (2 + 1) ^ 3 * B 2 = aperyLead 2 * B (2 + 1) := by decide

end E213.Lib.Math.NumberTheory.AperyRecurrence
