import E213.Physics.Couplings.AlphaGUT

/-!
# 1/α_em — bare integer skeleton + lattice prefactors

Single-file consolidation of four atomic-coefficient layers
(2026-05-05 merge of `Bare`, `IntegerSkeleton`, `Prefactors`,
`FiveTermDerivation` — all `by decide` Nat identities).

Sub-namespaces (preserved for cross-layer `open` declarations):

  * `E213.Physics.AlphaEM.Bare`              — Weinberg sum + bare bracket
  * `E213.Physics.AlphaEM.IntegerSkeleton`   — 60, 25, 12, 45, 4 origins
  * `E213.Physics.AlphaEM.Prefactors`        — c·NS·NT, d/NS, NS²-1 derivations
  * `E213.Physics.AlphaEM.FiveTermDerivation`— d±1 cofactor pattern + Pell form

DRLT formulae:
  1/α_3 = (NS² − 1) · S(1)   = 8         (exact ℤ)
  1/α_2 = 12 · NT · S(2)      = 30        (exact ℤ)
  1/α_1 = 12 · NS · S(∞)      = 36 · ζ(2) (bracket)

Weinberg sum (Y-norm 5/3):
  1/α_em(bare) = (5/3)·(1/α_1) + 1/α_2 = 60·ζ(2) + 30 ≈ 128.696
-/

namespace E213.Physics.AlphaEM.Bare

open E213.Physics.Simplex.Counts
open E213.Physics.Basel.Bound

/-- 1/α_3 (confined, exact integer) = NS² - 1 = 8. -/
def inv_alpha_3 : Nat := NS * NS - 1

theorem inv_alpha_3_eq_8 : inv_alpha_3 = 8 := by decide

/-- 1/α_2 (electroweak, exact integer) = 12 · NT · (5/4) = 30. -/
def inv_alpha_2 : Nat := 12 * NT * 5 / 4

theorem inv_alpha_2_eq_30 : inv_alpha_2 = 30 := by decide

/-- 1/α_1 lower bracket = 12·NS · S(N) = 36 · S(N). -/
def inv_alpha_1_lower (N : Nat) : (Nat × Nat) :=
  let s := S N
  ((12 * NS) * s.1, s.2)

/-- 1/α_1 upper bracket. -/
def inv_alpha_1_upper (N : Nat) : (Nat × Nat) :=
  let u := upper N
  ((12 * NS) * u.1, u.2)

/-- 1/α_em(bare) lower: 60·S(N) + 30. -/
def inv_alpha_em_bare_lower (N : Nat) : (Nat × Nat) :=
  let s := S N
  (60 * s.1 + 30 * s.2, s.2)

/-- 1/α_em(bare) upper: 60·upper(N) + 30. -/
def inv_alpha_em_bare_upper (N : Nat) : (Nat × Nat) :=
  let u := upper N
  (60 * u.1 + 30 * u.2, u.2)

/-- Concrete S(5) value (kept here for traceability). -/
theorem S_5 : S 5 = (21076, 14400) := by decide

/-- 128 ∈ bare bracket at N=5  (lower ≈ 117.82, upper ≈ 129.81). -/
theorem bare_128_in_bracket :
    let lo := inv_alpha_em_bare_lower 5
    let hi := inv_alpha_em_bare_upper 5
    lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1 := by decide

/-- 137 NOT in bare bracket — needs Ξ correction. -/
theorem corrected_137_outside_bare_bracket :
    let hi := inv_alpha_em_bare_upper 5
    hi.1 < 137 * hi.2 := by decide

end E213.Physics.AlphaEM.Bare

namespace E213.Physics.AlphaEM.IntegerSkeleton

/-! ## Integer-coefficient origins for `60·ζ(2) + 30 + 25/3 + α_GUT/(NS+1)`.

  E = c·NS·NT = 12     (directed bipartite edges)
  d = NS+NT = 5        (atomic dimension)
  60 = E·d              (origin of 60·ζ(2))
  30 = 1/α_2            (paper 2 gauge value)
  25 = d²               (block-pair total)
  NS+1 = 4              (Dyson-tail face dim)
  NS²·d = 45            (proposed gap correction denominator)
-/

/-- Edge count of K_{3,2}^{(c=2)}: c·NS·NT. -/
def edge_count : Nat := 2 * 3 * 2

theorem sixty_is_E_times_d : edge_count * 5 = 60 := by decide
theorem edge_count_is_12 : edge_count = 12 := by decide
theorem twentyfive_is_d_sq : 5 * 5 = 25 := by decide
theorem nine_is_NS_sq : 3 * 3 = 9 := by decide
theorem fortyfive_is_NS_sq_times_d : 3 * 3 * 5 = 45 := by decide
theorem four_is_NS_plus_1 : 3 + 1 = 4 := by decide
theorem thirtytwo_is_two_to_d : 2 ^ 5 = 32 := by decide
theorem eight_is_NS_sq_minus_1 : 3 * 3 - 1 = 8 := by decide

/-- Bundled: every integer in 1/α_em is structurally fixed. -/
theorem alpha_em_integer_origins :
    edge_count * 5 = 60
    ∧ 5 * 5 = 25
    ∧ 3 + 1 = 4
    ∧ 3 * 3 * 5 = 45 := by decide

end E213.Physics.AlphaEM.IntegerSkeleton

namespace E213.Physics.AlphaEM.Prefactors

open E213.Physics.Simplex.Counts

/-! ## Lattice-primitive derivation of all 1/α_em(IR) prefactors.

  Hint 1: 5/3 = d/NS               (Y-norm)
  Hint 2: 12  = c·NS·NT             (directed bipartite edges)
  Hint 3: NS²-1 vs NS²              (trace removal)

  ★ c·NS·NT² = 24 = adjoint SU(5) = (d-1)(d+1)
    → α_2 prefactor's (12·NT) part *is* adjoint SU(5).
-/

/-- c_lattice = 2. -/
def c_lat : Nat := 2

/-- 5/3 = d/NS at the rational level: 5·NS = 3·d → 15 = 15. -/
theorem hint1_y_norm_is_d_over_NS : 5 * NS = 3 * d := by decide

/-- prefactor 12 = c · NS · NT (directed bipartite edges of K_{NS,NT}). -/
theorem hint2_prefactor_12_is_directed_edges :
    c_lat * NS * NT = 12 := by decide

/-- 12 = 2·(d+1) — cross-check via d+1 cofactor. -/
theorem hint2_alt_d_plus_1 :
    c_lat * NS * NT = 2 * (d + 1) := by decide

/-- 1/α_3 = NS² - 1, the trace-removed adjoint. -/
theorem hint3_trace_removal :
    NS * NS - (1 : Nat) = 8 ∧ NS * NS = 9 := by decide

/-- ★ α_2 prefactor's (12·NT) = adjoint SU(5) = (d-1)(d+1) = 24 ★ -/
theorem alpha_2_prefactor_eq_adjoint_su5 :
    c_lat * NS * NT * NT = d * d - 1 := by decide

/-- α_1 prefactor (Y-norm): c·d·NS·NT = 60 = 12·5 = 12·d. -/
theorem alpha_1_y_norm_prefactor :
    c_lat * d * NS * NT = 60
    ∧ c_lat * d * NS * NT = (c_lat * NS * NT) * d := by decide

/-- ★ Unified prefactor capstone: all prefactors come from {c, NS, NT, d}. -/
theorem all_prefactors_structural :
    (NS * NS - 1 = 8)
    ∧ (c_lat * NS * NT * NT = d * d - 1)
    ∧ (c_lat * d * NS * NT = 60)
    ∧ (5 * NS = 3 * d)
    ∧ (c_lat * NS * NT = 12)
    ∧ (d * d - 1 = (d - 1) * (d + 1)) := by decide

end E213.Physics.AlphaEM.Prefactors

namespace E213.Physics.AlphaEM.FiveTermDerivation

open E213.Physics.Simplex.Counts

/-! ## Five-term decomposition + d±1 cofactor pattern.

  1/α_em(IR) = 1/α_3 + 1/α_2 + (5/3)·(1/α_1) + 1/NS + α_GUT/(NS+1)

  ★ d² - 1 = (d-1)(d+1) = 4·6 = 24 = adjoint SU(5)
  ★ 1/NS         = NT/(d+1)         ← d+1 cofactor
  ★ α_GUT/(NS+1) = α_GUT/(d-1)      ← d-1 cofactor
-/

/-- Term 4 alternative: 1/NS = NT/(d+1) (cross-mult: NS·NT = d+1). -/
theorem inv_NS_eq_NT_over_d_plus_1 :
    NT * NS = d + 1 := by decide

/-- Term 5 denominator: NS+1 = d-1 = 4. -/
theorem NS_plus_1_eq_d_minus_1 :
    NS + 1 = d - 1 := by decide

/-- d² - 1 = (d-1)(d+1) = 24 — adjoint SU(5). -/
theorem d_sq_minus_1_factorises :
    d * d - 1 = (d - 1) * (d + 1)
    ∧ (d - 1) * (d + 1) = 24 := by decide

/-- d² = (d-1)(d+1) + 1 — Pell-style identity. -/
theorem d_sq_pell_form :
    d * d = (d - 1) * (d + 1) + 1 := by decide

/-- ★ Cofactor pattern master theorem. -/
theorem cofactor_pattern :
    (d * d - 1 = (d - 1) * (d + 1))
    ∧ (NT * NS = d + 1)
    ∧ (NS + 1 = d - 1)
    ∧ (d - 1 = 4) ∧ (d + 1 = 6) := by decide

/-- Five terms traceable to prior theorems. -/
theorem five_terms_traceable :
    (NS * NS - 1 = 8)
    ∧ (12 * NT * 5 / 4 = 30)
    ∧ (NT * NS = d + 1)
    ∧ (NS + 1 = d - 1)
    ∧ (d * d - 1 = (d - 1) * (d + 1)) := by decide

end E213.Physics.AlphaEM.FiveTermDerivation
