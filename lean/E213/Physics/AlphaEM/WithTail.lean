import E213.Physics.AlphaEM.V137Tight
import E213.Physics.Couplings.AlphaGUT

/-!
# 1/α_em(IR) candidate WITH Dyson tail α_GUT/(NS+1).

  1/α_em = 60·ζ(2) + 30 + 25/3 + α_GUT/(NS+1)
         = principal + α_GUT/4                    [NS+1 = 4]
         = principal + 1/(100·ζ(2))               [α_GUT = 1/(25·ζ(2))]

Bracket form with ζ(2) ∈ [S(N), upper(N)]:

  inv_lower_with_tail(N) = inv_lower_tight(N) + 1/(100·upper(N))
  inv_upper_with_tail(N) = inv_full_upper(N)  + 1/(100·S(N))     (N ≥ 1)

This file makes the structural-gap closure a 0-axiom statement: the
Dyson tail shifts the bracket asymptote 137.0294 → 137.0354, and at
small N the wider bracket contains observed 137.036 = (137036, 1000).
-/

namespace E213.Physics.AlphaEM.WithTail

open E213.Physics.AlphaEM.V137 (inv_full_upper)
open E213.Physics.AlphaEM.V137Tight (inv_lower_tight)
open E213.Physics.Basel.Bound (S upper)

/-- inv_lower_tight(N) + 1/(100·upper(N)) as `(num, den)`. -/
def inv_lower_with_tail (N : Nat) : (Nat × Nat) :=
  let p := inv_lower_tight N
  let u := upper N
  (p.1 * (100 * u.1) + u.2 * p.2, p.2 * (100 * u.1))

/-- inv_full_upper(N) + 1/(100·S(N)) as `(num, den)`. N ≥ 1. -/
def inv_upper_with_tail (N : Nat) : (Nat × Nat) :=
  let P := inv_full_upper N
  let s := S N
  (P.1 * (100 * s.1) + s.2 * P.2, P.2 * (100 * s.1))

/-- Observed 137.036 = (137036, 1000) ∈ with-tail bracket at N=20. -/
theorem n20_with_tail_contains_observed :
    let lo := inv_lower_with_tail 20
    let hi := inv_upper_with_tail 20
    lo.1 * 1000 < 137036 * lo.2 ∧ 137036 * hi.2 < 1000 * hi.1 := by decide

/-- Same at N=50 — narrower bracket still covers observed. -/
theorem n50_with_tail_contains_observed :
    let lo := inv_lower_with_tail 50
    let hi := inv_upper_with_tail 50
    lo.1 * 1000 < 137036 * lo.2 ∧ 137036 * hi.2 < 1000 * hi.1 := by decide

/-- Candidate asymptote 137.03545 = (1370354, 10000) at N=20.
    With tail, the formula's own value sits comfortably inside. -/
theorem n20_with_tail_contains_candidate :
    let lo := inv_lower_with_tail 20
    let hi := inv_upper_with_tail 20
    lo.1 * 10000 < 1370354 * lo.2 ∧ 1370354 * hi.2 < 10000 * hi.1 := by decide

end E213.Physics.AlphaEM.WithTail

#print axioms E213.Physics.AlphaEM.WithTail.n20_with_tail_contains_observed
#print axioms E213.Physics.AlphaEM.WithTail.n50_with_tail_contains_observed
#print axioms E213.Physics.AlphaEM.WithTail.n20_with_tail_contains_candidate
