import E213.Lib.Physics.Mixing.CKMHierarchy

/-!
# JarlskogApex — atomic candidate for the CKM apex `(ρ,η)` / Jarlskog magnitude

`research-notes/frontiers/ckm_rho_eta_apex.md`: the Jarlskog magnitude was
over-predicted ×2.66 because DRLT's `s₁₃ = A·λ³` omits the Wolfenstein apex
factor `R_u = √(ρ²+η²) ≈ 0.38`. This file records the **atomic candidate**
that closes the gap to ~6%:

  **R_u = c/d = 2/5**   (equivalently `|V_ub|/|V_cb| = λ·R_u = c/D = 2/22`,
  where `D = d²−d+c = 22` is the Cabibbo denominator).

Numerically (computed from the full Jarlskog formula with this factor):
- `s₁₃ = A·λ³·(c/d) = 0.00380`  vs observed `|V_ub| = 0.00382` (0.5%)
- `R_u = 0.40`  vs observed `0.38–0.42` (≤4%)
- `J = 3.27×10⁻⁵`  vs observed `3.08×10⁻⁵` (6.2%) — was `8.18×10⁻⁵` (166%)
- `η = (c/d)·sin(π/φ²) = 0.373`  vs observed `η̄ ≈ 0.348` (7%)

## Status — CANDIDATE, not forced (`seed/AXIOM/05_no_exterior.md` §5.4)

The atomic *identities* below are exact (PURE). The *match to observation*
is a candidate-level claim (~4–6%), not a precision theorem: `R_u = c/d` is
a pattern (`0.40 ≈ 0.40`) with a suggestive structural story — `V_ub` is the
`λ³` (third-level) transition, and crossing the extra level multiplies the
ratio by the multiplicity `c` over the base `d` (cf. the `c` = inter-level
multiplicity reading, `AlphaEM/AssignmentForcing`). What is **not** yet a
theorem: *why* `|V_ub|/|V_cb| = c/D` is forced (the numerator `c`). Until
that is derived, this stays a candidate — strong, but labelled.

All theorems PURE.
-/

namespace E213.Lib.Physics.Mixing.JarlskogApex

def NS : Nat := 3
def NT : Nat := 2
def c  : Nat := 2
def d  : Nat := 5

/-- Cabibbo denominator `D = d²−d+c = 22` (atomic; shared with `λ = d/D`). -/
def cabibboDenom : Nat := d * d - d + c

theorem cabibbo_denom_22 : cabibboDenom = 22 := by decide

/-! ## §1 — the apex candidate `R_u = c/d` -/

/-- Apex magnitude candidate `R_u = √(ρ²+η²)` as a `(num, den)` pair:
    `c/d = 2/5`. -/
def Ru : Nat × Nat := (c, d)

theorem Ru_is_c_over_d : Ru = (2, 5) := by decide

/-! ## §2 — the induced |V_ub|/|V_cb| candidate `= c/D = 2/22` -/

/-- `|V_ub|/|V_cb| = λ·R_u = (d/D)·(c/d) = c/D`.  As a fraction identity:
    `(d·c)/(D·d) = c/D`, i.e. the cross-multiplication `(d·c)·D = c·(D·d)`. -/
theorem vub_vcb_eq_c_over_D :
    (d * c) * cabibboDenom = c * (cabibboDenom * d) := by decide

/-- The candidate value: `|V_ub|/|V_cb| = c/D = 2/22`. -/
theorem vub_vcb_candidate : (c, cabibboDenom) = (2, 22) := by decide

/-! ## §3 — consistency with observation (candidate-level bracket) -/

/-- `R_u = c/d = 0.40` (×100 = 40) lies in the observed band
    `[0.38, 0.42]` (√(ρ̄²+η̄²) ≈ 0.383 … |V_ub|/(λ|V_cb|) ≈ 0.416).
    Falsifier: a future apex measurement of `R_u` outside `[0.38, 0.42]`
    discards the `c/d` candidate. -/
theorem Ru_in_observed_bracket :
    c * 100 / d = 40
    ∧ 38 ≤ c * 100 / d ∧ c * 100 / d ≤ 42 := by decide

/-! ## §4 — capstone -/

/-- **Atomic-apex candidate.**  `R_u = c/d`, `|V_ub|/|V_cb| = c/D = 2/22`,
    both atomic; the value `R_u = 0.40` is consistent with the observed
    `[0.38, 0.42]`.  With this factor the Jarlskog magnitude matches
    observation to ~6% (vs 166% without).  CANDIDATE — the numerator `c` is
    not yet a forcing theorem.  Frontier: `ckm_rho_eta_apex.md`. -/
theorem jarlskog_apex_candidate :
    Ru = (2, 5)
    ∧ cabibboDenom = 22
    ∧ (c, cabibboDenom) = (2, 22)
    ∧ c * 100 / d = 40
    ∧ 38 ≤ c * 100 / d ∧ c * 100 / d ≤ 42 := by decide

end E213.Lib.Physics.Mixing.JarlskogApex
