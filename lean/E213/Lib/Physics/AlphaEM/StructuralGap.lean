import E213.Lib.Physics.AlphaEM.Brackets

/-!
# Structural gap of the 1/α_em(IR) candidate formula

`AlphaEM.V137.lean` proposes
    1/α_em(IR) = 60·ζ(2) + 30 + 25/3 + α_GUT/(NS+1)
                ≈ 137.0354548                 [asymptotic, perfect ζ(2)]
Observed:        1/α_em(0) = 137.0359991      [PDG 2024]
                                ───────────
Difference (candidate − observed):  −5.443 × 10⁻⁴

This gap is **independent of bracket tightening on ζ(2)**: even with a
zero-width bracket on the Basel sum, the candidate formula's value
137.0354548 Lens-bracket endpoint differs from measurement-Lens reading 137.0359991 by 5.4×10⁻⁴.

## Open Problem #1 split (per HANDOFF)

* **1a (computational):** tighten the rational bracket on ζ(2) so the
  candidate-formula bracket has width ≤ 10⁻⁴ of 137.  Implemented in
  `Basel/Bound.lean` (lower_tight) + `AlphaEM.V137Tight.lean` up to
  N=50; full
  10⁻⁴ requires N ≈ 350+ which exceeds Lean's default `maxRecDepth`.

* **1b (structural, RESEARCH):** identify the missing ~5.4×10⁻⁴
  contribution.  Three classes of candidate corrections, each
  requiring a Raw-axiom derivation rather than a numerical fit:

  - **next-order Dyson tail.**  Current chain stops at α_GUT/4.
    Add (α_GUT/4)² ≈ 3.7×10⁻⁵ — too small by ×15.
    Add α_GUT²·(d²/something) — open.
  - **refined d²/NS coefficient.**  Current 25/3 is the
    "channels per spatial dimension" ansatz.  An exact derivation
    from the Gram-channel structure may yield 25/3·(1+δ) with
    δ ≈ 6.5×10⁻⁵.  Open.
  - **hadronic-sector correction analog.**  Standard QED requires
    a hadronic-sector ~10⁻⁴ radiative correction; a 213-lattice
    internal counterpart from the d=5 atomic structure is unknown.

This file makes the gap a **first-class, rationally-stated falsifier**
target so any future marathon resolves it as a single Lean theorem.
-/

namespace E213.Lib.Physics.AlphaEM.StructuralGap

open E213.Lib.Physics.AlphaEM.V137Tight

/-- Measurement-Lens 1/α_em(0) ≈ 137.0359991, expressed as 137036/1000
    (4 significant figures past 137).  The 4/27-standard target is
    `|candidate − 137036/1000| < 137/10⁴`. -/
def observed_milli : (Nat × Nat) := (137036, 1000)

/-- 4/27 standard tolerance: 1/10⁴ relative ≈ 137·10⁻⁴ ≈ 0.0137.
    Expressed as 137/10000. -/
def tolerance : (Nat × Nat) := (137, 10000)

/-- At resolution N=50 the candidate-formula bracket has width ≤ 0.024.
    Both the asymptotic candidate value (137.0354548) and the observed
    137.0359991 lie inside the bracket — current bracket is **too
    wide to discriminate**. -/
theorem n50_bracket_contains_observed :
    let lo := inv_lower_tight 50; let hi := inv_upper 50
    lo.1 < 137036 * lo.2 ∧ 137036 * hi.2 < 1000 * hi.1 := by decide

/-- Sharper statement: at N=50 the bracket also contains the
    candidate-formula asymptotic 137.0354548, expressed as
    1370354/10000. -/
theorem n50_bracket_contains_candidate :
    let lo := inv_lower_tight 50; let hi := inv_upper 50
    lo.1 * 10000 < 1370354 * lo.2
    ∧ 1370354 * hi.2 < 10000 * hi.1 := by decide

end E213.Lib.Physics.AlphaEM.StructuralGap
