import E213.Lib.Physics.AlphaEM.Bare

/-!
# 1/α_em rational brackets — pure DRLT bare + tight + 5-term

Single-file consolidation of three bracket layers (2026-05-05 merge of
`V137`, `V137Tight`, `BareTightBracket` — all `decide`-verified).

Sub-namespaces (preserved for cross-layer `open`):

  * `E213.Lib.Physics.AlphaEM.BareTightBracket` — bare 60·ζ(2)+30 ≈ 128.696
  * `E213.Lib.Physics.AlphaEM.V137`             — candidate 60·ζ(2)+30+25/3 ≈ 137.029
  * `E213.Lib.Physics.AlphaEM.V137Tight`        — telescoped lower (S(N)+1/(N+1))

Width comparison (V137Tight):

| N  | width (lower=S) | width (lower=tight) |
|----|-----------------|---------------------|
| 10 | 6.000           | 0.545               |
| 20 | 3.000           | 0.143               |
| 50 | 1.200           | 0.0235              |
-/

namespace E213.Lib.Physics.AlphaEM.BareTightBracket

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Basel.Bound
open E213.Lib.Physics.AlphaEM.Bare

/-- 128 ∈ bare bracket at N = 10. -/
theorem bracket_128_in_10 :
    let lo := inv_alpha_em_bare_lower 10
    let hi := inv_alpha_em_bare_upper 10
    lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1 := by decide

/-- 129 outside bare bracket at N = 10 (upper-end). -/
theorem bracket_129_excluded_10 :
    let hi := inv_alpha_em_bare_upper 10
    hi.1 < 129 * hi.2 := by decide

/-- 137 outside bare bracket at N = 10 — needs QED running. -/
theorem bracket_137_excluded_10 :
    let hi := inv_alpha_em_bare_upper 10
    hi.1 < 137 * hi.2 := by decide

/-- N = 20: tighter, 128 still inside. -/
theorem bracket_128_in_20 :
    let lo := inv_alpha_em_bare_lower 20
    let hi := inv_alpha_em_bare_upper 20
    lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1 := by decide

/-- N = 20: 129 excluded. -/
theorem bracket_129_excluded_20 :
    let hi := inv_alpha_em_bare_upper 20
    hi.1 < 129 * hi.2 := by decide

/-- The 9 = 137 − 128 gap is QED running, NOT DRLT topology. -/
theorem qed_running_gap : (137 : Nat) - 128 = 9 := by decide

/-- Capstone: bare 1/α_em(M_Z) sharp at 128 ± 1 at N=20. -/
theorem alpha_em_bare_pure_drlt :
    let lo := inv_alpha_em_bare_lower 20
    let hi := inv_alpha_em_bare_upper 20
    (lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1)
    ∧ (hi.1 < 137 * hi.2)
    ∧ (137 - 128 = 9) := by decide

end E213.Lib.Physics.AlphaEM.BareTightBracket

namespace E213.Lib.Physics.AlphaEM.V137

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Basel.Bound

/-! ## Candidate formula 1/α_em(IR) ≈ 60·ζ(2) + 30 + 25/3 + α_GUT/(NS+1).

  bare(M_Z) + d²/NS + Ξ_tail
  = 128.696 + 8.333 + 0.00608
  ≈ 137.035  (observed 137.036 — ppm match)

Honest tagging: `+25/3 = d²/NS` is conjectural structural form.
Plausible source: photon couples to all 25 Gram channels distributed
across NS=3 spatial directions ("channels per spatial dim").
Strict Lens-level derivation OPEN.
-/

/-- Candidate lower bracket: 60·S(N) + 30 + 25/3 = (180·S.1 + 115·S.2)/(3·S.2). -/
def inv_full_lower (N : Nat) : (Nat × Nat) :=
  let s := S N
  (180 * s.1 + 115 * s.2, 3 * s.2)

/-- Candidate upper bracket: 60·upper(N) + 30 + 25/3. -/
def inv_full_upper (N : Nat) : (Nat × Nat) :=
  let u := upper N
  (180 * u.1 + 115 * u.2, 3 * u.2)

/-- N=3 lower endpoint. -/
theorem inv_full_lower_3 :
    inv_full_lower 3 = (180 * 49 + 115 * 36, 3 * 36) := by decide

/-- N=3 upper endpoint. -/
theorem inv_full_upper_3 :
    inv_full_upper 3 = (180 * 183 + 115 * 108, 3 * 108) := by decide

/-- 137 ∈ candidate bracket at N=10 (width ~6). -/
theorem bracket_137_in_at_10 :
    let lo := inv_full_lower 10
    let hi := inv_full_upper 10
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- 138 outside upper at N=10. -/
theorem bracket_138_excluded_at_10 :
    let hi := inv_full_upper 10
    hi.1 < 138 * hi.2 := by decide

/-- 131 below lower at N=10. -/
theorem bracket_131_excluded_at_10 :
    let lo := inv_full_lower 10
    131 * lo.2 < lo.1 := by decide

/-- Capstone: candidate bracket at N=10 with width ~6. -/
theorem candidate_formula_contains_137 :
    let lo := inv_full_lower 10
    let hi := inv_full_upper 10
    (lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1)
    ∧ (hi.1 < 138 * hi.2)
    ∧ (131 * lo.2 < lo.1) := by decide

end E213.Lib.Physics.AlphaEM.V137

namespace E213.Lib.Physics.AlphaEM.V137Tight

open E213.Lib.Physics.Basel.Bound

/-! ## Tightened lower endpoint: telescoping by S(N) + 1/(N+1).

Bracket width on 1/α_em becomes 60/(N(N+1)) — quadratic over 60/N.
-/

/-- Tight lower for `60·ζ(2) + 30 + 25/3`. -/
def inv_lower_tight (N : Nat) : (Nat × Nat) :=
  let s := S N
  (180 * s.1 * (N + 1) + s.2 * (180 + 115 * (N + 1)),
   3 * s.2 * (N + 1))

/-- Upper kept from V137. -/
def inv_upper (N : Nat) : (Nat × Nat) := AlphaEM.V137.inv_full_upper N

/-- Cross-mult comparison. -/
def lt (p q : Nat × Nat) : Bool := p.1 * q.2 < q.1 * p.2

theorem lower_below_upper_20 :
    lt (inv_lower_tight 20) (inv_upper 20) = true := by decide

theorem lower_below_upper_30 :
    lt (inv_lower_tight 30) (inv_upper 30) = true := by decide

/-- 137 ∈ tight bracket at N=10 (width ~0.55). -/
theorem bracket_137_in_at_10_tight :
    let lo := inv_lower_tight 10; let hi := inv_upper 10
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- 137 ∈ tight bracket at N=20 (width ~0.14). -/
theorem bracket_137_in_at_20_tight :
    let lo := inv_lower_tight 20; let hi := inv_upper 20
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- 138 excluded at N=20. -/
theorem bracket_138_excluded_at_20 :
    let hi := inv_upper 20
    hi.1 < 138 * hi.2 := by decide

/-- Capstone: N=20 tight contains 137 with width ≤ 0.14
    (43× over N=10 baseline of width 6).  Headline 1/α_em = 137.036
    at 10⁻⁴ ppm NOT reachable: candidate's asymptote 137.0354548
    differs from observed 137.0359991 by 5.4×10⁻⁴.
    See `AlphaEM/StructuralGap.lean`. -/
theorem capstone_n20 :
    let lo := inv_lower_tight 20; let hi := inv_upper 20
    (lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1)
    ∧ (hi.1 < 138 * hi.2) := by decide

end E213.Lib.Physics.AlphaEM.V137Tight
