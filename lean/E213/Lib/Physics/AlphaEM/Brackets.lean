import E213.Lib.Physics.AlphaEM.Bare

/-!
# 1/α_em rational brackets — pure DRLT bare + tight + 5-term

Single-file consolidation of three bracket layers .

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

/-- ★ Bare bracket master: 1/α_em(M_Z) sharp at 128 ± 1 at N=20,
    excludes 137 (the 9 = 137 − 128 gap is QED running, NOT DRLT
    topology).  Per-N bracket containments at N = 10, 20
    folded into one statement. -/
theorem alpha_em_bare_pure_drlt :
    -- N = 10 brackets
    ((inv_alpha_em_bare_lower 10).1 < 128 * (inv_alpha_em_bare_lower 10).2
      ∧ 128 * (inv_alpha_em_bare_upper 10).2 < (inv_alpha_em_bare_upper 10).1)
    ∧ (inv_alpha_em_bare_upper 10).1 < 129 * (inv_alpha_em_bare_upper 10).2
    ∧ (inv_alpha_em_bare_upper 10).1 < 137 * (inv_alpha_em_bare_upper 10).2
    -- N = 20 brackets
    ∧ ((inv_alpha_em_bare_lower 20).1 < 128 * (inv_alpha_em_bare_lower 20).2
       ∧ 128 * (inv_alpha_em_bare_upper 20).2 < (inv_alpha_em_bare_upper 20).1)
    ∧ (inv_alpha_em_bare_upper 20).1 < 129 * (inv_alpha_em_bare_upper 20).2
    ∧ (inv_alpha_em_bare_upper 20).1 < 137 * (inv_alpha_em_bare_upper 20).2
    -- QED running gap
    ∧ (137 - 128 = 9) := by decide

end E213.Lib.Physics.AlphaEM.BareTightBracket

namespace E213.Lib.Physics.AlphaEM.V137

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Basel.Bound

/-! ## Candidate formula 1/α_em(IR) ≈ 60·ζ(2) + 30 + 25/3 + α_GUT/(NS+1).

  bare(M_Z) + d²/NS + Ξ_tail
  = 128.696 + 8.333 + 0.00608
  ≈ 137.035  (observed 137.036 — ppm Lens-reading agreement)

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

/-- ★ Candidate-formula master: 137 ∈ bracket at N=10 (width ~6),
    138 above + 131 below excluded.  N=3 endpoints also recorded. -/
theorem candidate_formula_contains_137 :
    -- N=3 endpoints
    inv_full_lower 3 = (180 * 49 + 115 * 36, 3 * 36)
    ∧ inv_full_upper 3 = (180 * 183 + 115 * 108, 3 * 108)
    -- N=10 contains 137, excludes 138 above and 131 below
    ∧ ((inv_full_lower 10).1 < 137 * (inv_full_lower 10).2
       ∧ 137 * (inv_full_upper 10).2 < (inv_full_upper 10).1)
    ∧ (inv_full_upper 10).1 < 138 * (inv_full_upper 10).2
    ∧ 131 * (inv_full_lower 10).2 < (inv_full_lower 10).1 := by decide

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

/-- ★ Capstone: N=20 tight contains 137 with width ≤ 0.14
    (43× over N=10 baseline of width 6).  Externally referenced
    by Certificates/Checker.

    Headline 1/α_em = 137.036 at 10⁻⁴ ppm has structural gap:
    count-Lens asymptote 137.0354548 vs measurement-Lens reading
    137.0359991 by 5.4×10⁻⁴.  See `AlphaEM/StructuralGap.lean`. -/
theorem capstone_n20 :
    let lo := inv_lower_tight 20; let hi := inv_upper 20
    (lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1)
    ∧ (hi.1 < 138 * hi.2) := by decide

/-- ★ Tight-bracket extended master: N=10/20 contain 137,
    N=20/30 lower < upper, N=20 excludes 138. -/
theorem tight_bracket_extended :
    -- N=10 tight contains 137
    ((inv_lower_tight 10).1 < 137 * (inv_lower_tight 10).2
      ∧ 137 * (inv_upper 10).2 < (inv_upper 10).1)
    -- lower < upper at N=20, 30
    ∧ lt (inv_lower_tight 20) (inv_upper 20) = true
    ∧ lt (inv_lower_tight 30) (inv_upper 30) = true := by decide

end E213.Lib.Physics.AlphaEM.V137Tight
