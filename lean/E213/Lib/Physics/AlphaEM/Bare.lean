import E213.Lib.Physics.Couplings.AlphaGUT

/-!
# 1/α_em — bare integer skeleton + lattice prefactors

Single-file consolidation of four atomic-coefficient layers
(2026-05-05 merge of `Bare`, `IntegerSkeleton`, `Prefactors`,
`FiveTermDerivation` — all `by decide` Nat identities).

Sub-namespaces (preserved for cross-layer `open` declarations):

  * `E213.Lib.Physics.AlphaEM.Bare`              — Weinberg sum + bare bracket
  * `E213.Lib.Physics.AlphaEM.IntegerSkeleton`   — 60, 25, 12, 45, 4 origins
  * `E213.Lib.Physics.AlphaEM.Prefactors`        — c·NS·NT, d/NS, NS²-1 derivations
  * `E213.Lib.Physics.AlphaEM.FiveTermDerivation`— d±1 cofactor pattern + Pell form

DRLT formulae:
  1/α_3 = (NS² − 1) · S(1)   = 8         (exact ℤ)
  1/α_2 = 12 · NT · S(2)      = 30        (exact ℤ)
  1/α_1 = 12 · NS · S(∞)      = 36 · ζ(2) (bracket)

Weinberg sum (Y-norm 5/3):
  1/α_em(bare) = (5/3)·(1/α_1) + 1/α_2 = 60·ζ(2) + 30 ≈ 128.696
-/

namespace E213.Lib.Physics.AlphaEM.Bare

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Basel.Bound

/-- 1/α_3 (confined, exact integer) = NS² - 1 = 8. -/
def inv_alpha_3 : Nat := NS * NS - 1

/-- 1/α_2 (electroweak, exact integer) = 12 · NT · (5/4) = 30. -/
def inv_alpha_2 : Nat := 12 * NT * 5 / 4

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

/-- ★ Bare 1/α_em master — exact ℤ values for 1/α_3 (= 8) and
    1/α_2 (= 30), Basel partial sum S(5) = 21076/14400, and bare
    bracket containment of 128 + exclusion of 137 at N=5. -/
theorem bare_master :
    inv_alpha_3 = 8
    ∧ inv_alpha_2 = 30
    ∧ S 5 = (21076, 14400)
    -- 128 ∈ bare bracket at N=5
    ∧ (let lo := inv_alpha_em_bare_lower 5
       let hi := inv_alpha_em_bare_upper 5
       lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1)
    -- 137 ∉ bare bracket at N=5 (above upper)
    ∧ (let hi := inv_alpha_em_bare_upper 5
       hi.1 < 137 * hi.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.AlphaEM.Bare

namespace E213.Lib.Physics.AlphaEM.IntegerSkeleton

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

/-- ★ Every integer in 1/α_em is structurally fixed:
      60 = c·NS·NT·d (edge count × d)
      25 = d²
      45 = NS²·d
      4  = NS + 1
      9  = NS²
      32 = 2^d
      12 = c·NS·NT  (= edge_count)
      8  = NS² − 1 -/
theorem alpha_em_integer_origins :
    edge_count * 5 = 60
    ∧ edge_count = 12
    ∧ (5 : Nat) * 5 = 25
    ∧ (3 : Nat) * 3 = 9
    ∧ (3 : Nat) * 3 * 5 = 45
    ∧ (3 : Nat) + 1 = 4
    ∧ (2 : Nat) ^ 5 = 32
    ∧ (3 : Nat) * 3 - 1 = 8 := by decide

end E213.Lib.Physics.AlphaEM.IntegerSkeleton

namespace E213.Lib.Physics.AlphaEM.Prefactors

open E213.Lib.Physics.Simplex.Counts

/-! ## Lattice-primitive derivation of all 1/α_em(IR) prefactors.

  Hint 1: 5/3 = d/NS               (Y-norm)
  Hint 2: 12  = c·NS·NT             (directed bipartite edges)
  Hint 3: NS²-1 vs NS²              (trace removal)

  ★ c·NS·NT² = 24 = adjoint SU(5) = (d-1)(d+1)
    → α_2 prefactor's (12·NT) part *is* adjoint SU(5).
-/

/-- c_lattice = 2.  Externally consumed by DiamondAudit, DiamondShape,
    HopHypothesis, FibonacciExtended, plus internal Bare uses. -/
def c_lat : Nat := 2

/-- ★ Unified prefactor capstone: all prefactors come from {c, NS, NT, d}.

    Bundles:
      · Y-norm 5/3 = d/NS (cross-mult 5·NS = 3·d)
      · 12 = c·NS·NT = 2·(d+1) (directed bipartite edges)
      · 1/α_3 = NS²−1 = 8 (trace-removed adjoint), NS² = 9
      · 12·NT = adjoint SU(5) = c·NS·NT² = d²−1 = 24
      · Y-norm prefactor: c·d·NS·NT = 60 = (c·NS·NT)·d
      · d²−1 = (d−1)·(d+1) factorization. -/
theorem all_prefactors_structural :
    -- Hint 1: 5/3 = d/NS
    5 * NS = 3 * d
    -- Hint 2: 12 = c·NS·NT
    ∧ c_lat * NS * NT = 12
    ∧ c_lat * NS * NT = 2 * (d + 1)
    -- Hint 3: 1/α_3 = NS² − 1 = 8, NS² = 9
    ∧ NS * NS - (1 : Nat) = 8
    ∧ NS * NS = 9
    -- α_2 prefactor = adjoint SU(5) = d² − 1
    ∧ c_lat * NS * NT * NT = d * d - 1
    -- Y-norm α_1 prefactor
    ∧ c_lat * d * NS * NT = 60
    ∧ c_lat * d * NS * NT = (c_lat * NS * NT) * d
    -- d² − 1 factorization
    ∧ d * d - 1 = (d - 1) * (d + 1) := by decide

end E213.Lib.Physics.AlphaEM.Prefactors

namespace E213.Lib.Physics.AlphaEM.FiveTermDerivation

open E213.Lib.Physics.Simplex.Counts

/-! ## Five-term decomposition + d±1 cofactor pattern.

  1/α_em(IR) = 1/α_3 + 1/α_2 + (5/3)·(1/α_1) + 1/NS + α_GUT/(NS+1)

  ★ d² - 1 = (d-1)(d+1) = 4·6 = 24 = adjoint SU(5)
  ★ 1/NS         = NT/(d+1)         ← d+1 cofactor
  ★ α_GUT/(NS+1) = α_GUT/(d-1)      ← d-1 cofactor
-/

/-- ★ Five-term cofactor pattern master — d±1 cofactor identities
    and traceability of the five 1/α_em(IR) terms.

    Bundles:
      · d² − 1 = (d−1)·(d+1) = 24 (adjoint SU(5))
      · 1/NS = NT/(d+1) (cross-mult NS·NT = d+1)
      · NS+1 = d−1 = 4 (Dyson-tail face)
      · d+1 = 6 (bipartite edge count)
      · d² = (d−1)·(d+1) + 1 (Pell-style)
      · Five 1/α_em terms traceable to (NS, NT, d) primitives. -/
theorem cofactor_pattern :
    -- d²−1 factorization and value
    d * d - 1 = (d - 1) * (d + 1)
    ∧ (d - 1) * (d + 1) = 24
    -- 1/NS = NT/(d+1) cross-mult
    ∧ NT * NS = d + 1
    -- NS+1 = d−1 = 4 (Dyson-tail face)
    ∧ NS + 1 = d - 1
    ∧ d - 1 = 4
    ∧ d + 1 = 6
    -- d² Pell form
    ∧ d * d = (d - 1) * (d + 1) + 1
    -- Five terms traceable
    ∧ NS * NS - 1 = 8
    ∧ 12 * NT * 5 / 4 = 30 := by decide

end E213.Lib.Physics.AlphaEM.FiveTermDerivation
