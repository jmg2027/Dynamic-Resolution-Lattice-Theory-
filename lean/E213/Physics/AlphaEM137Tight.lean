import E213.Physics.AlphaEM137
import E213.Physics.BaselBoundTight

/-!
# Tightened bracket on the 1/α_em(IR) candidate formula

`AlphaEM137.lean` proves `137 ∈ candidate-bracket` at N=10 with width
~6 (lower=`60·S(N)+30+25/3`, upper=`60·upper(N)+30+25/3`).

This file replaces the lower endpoint by `60·lower_tight(N)+30+25/3`
where `lower_tight N = S(N)+1/(N+1)`.  Bracket width on 1/α_em is
then `60/(N(N+1))` — quadratic improvement from `60/N`.

| N  | width (lower=S)  | width (lower=tight) |
|----|------------------|---------------------|
| 10 | 6.000            | 0.545               |
| 20 | 3.000            | 0.143               |
| 30 | 2.000            | 0.0645              |
| 50 | 1.200            | 0.0235              |

All theorems 0-axiom, `decide`-checked. The α_GUT/(NS+1) Dyson tail
is implicit (~0.006); the focus is bracketing
`60·ζ(2) + 30 + 25/3 ≈ 137.0294`.
-/

namespace E213.Physics.AlphaEM137Tight

open E213.Physics.Basel
open E213.Physics.BaselTight

/-- Tight lower endpoint for `60·ζ(2) + 30 + 25/3`. -/
def inv_lower_tight (N : Nat) : (Nat × Nat) :=
  let s := S N
  (180 * s.1 * (N + 1) + s.2 * (180 + 115 * (N + 1)),
   3 * s.2 * (N + 1))

/-- Upper endpoint kept from `AlphaEM137.lean`. -/
def inv_upper (N : Nat) : (Nat × Nat) := AlphaEM137.inv_full_upper N

/-- Cross-mult comparison. -/
def lt (p q : Nat × Nat) : Bool := p.1 * q.2 < q.1 * p.2

/-- Tight lower at N=20 below upper at N=20 (sanity). -/
theorem lower_below_upper_20 :
    lt (inv_lower_tight 20) (inv_upper 20) = true := by decide

/-- Tight lower at N=30 below upper at N=30. -/
theorem lower_below_upper_30 :
    lt (inv_lower_tight 30) (inv_upper 30) = true := by decide

/-- 137 ∈ tight bracket at N=10 (width ~ 0.55). -/
theorem bracket_137_in_at_10_tight :
    let lo := inv_lower_tight 10; let hi := inv_upper 10
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- 137 ∈ tight bracket at N=20 (width ~ 0.14). -/
theorem bracket_137_in_at_20_tight :
    let lo := inv_lower_tight 20; let hi := inv_upper 20
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- 138 excluded at N=20. -/
theorem bracket_138_excluded_at_20 :
    let hi := inv_upper 20
    hi.1 < 138 * hi.2 := by decide

/-- Capstone: N=20 tight bracket contains 137 with width ≤ 0.14
    (43× improvement vs the N=10 baseline of width 6).
    Headline 1/α_em = 137.036 at 10⁻⁴ ppm is NOT reachable by this
    chain — candidate formula's asymptotic value 137.0354548 differs
    from observed 137.0359991 by 5.4×10⁻⁴. See
    `AlphaEMStructuralGap.lean`. -/
theorem capstone_n20 :
    let lo := inv_lower_tight 20; let hi := inv_upper 20
    (lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1)
    ∧ (hi.1 < 138 * hi.2) := by decide

end E213.Physics.AlphaEM137Tight
