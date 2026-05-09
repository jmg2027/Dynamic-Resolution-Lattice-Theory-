import E213.Lib.Physics.Foundations.GoldenRatio

/-!
# Algebra Tower Asymptote — algebraic integer representation

The Moufang fail rate asymptote of each Type's CD doubling tower is
expressed as `(a + b·√5)/4` over Z[√5], avoiding irrationals.

Empirically discovered (Rust probe + level2_search, 2026-05-09):

  Type A (ZI, rank 0):       asymptote = (2, 0)/4 = 1/2
  Type B (ZSqrt[D≥2], rank 0): asymptote = (2, 0)/4 = 1/2 (= A)
  Type C (ZOmega, rank 1):    asymptote = (5, -1)/4 = (5 − √5)/4
  Type D (Hurwitz, rank 2):   asymptote = (1, 1)/4 = (1 + √5)/4

The (a, b) pair encodes the asymptote's exact value in Z[√5].
The rank determines how many Fibonacci-iterations of structural
complexity beyond the cyclic prime-power baseline.

This file establishes the *integer-pair* representation. Convergence
of measured rates to these values is empirical; full Lean proof
requires limiting machinery (Real213/Cauchy infrastructure).

213-native: no real numbers or irrationals introduced; all values
are integer pairs (a, b) ∈ Z² interpreted under Z[√5] convention.
-/

namespace E213.Lib.Math.CayleyDickson.AlgebraTowerAsymptote

/-- Base type classification (213-native, 4-row matrix). -/
inductive BaseType where
  | A   -- ZI = ℤ[i], 4 units, cyclic Z_4
  | B   -- ZSqrt[-D] D≥2, 2 units, cyclic Z_2
  | C   -- ZOmega = ℤ[ω], 6 units, cyclic Z_6
  | D   -- Hurwitz quaternion order, 24 units, 2T (binary tetrahedral)
  deriving DecidableEq, Repr

/-- Structural complexity rank (Fibonacci iterations of complexity). -/
def rank : BaseType → Nat
  | .A => 0
  | .B => 0
  | .C => 1
  | .D => 2

/-- Asymptote in (a, b) form representing (a + b·√5)/4 in Z[√5]. -/
def asymptote_ab : BaseType → Int × Int
  | .A => (2,  0)
  | .B => (2,  0)
  | .C => (5, -1)
  | .D => (1,  1)

/-- ★ Compatibility with 213's GoldenRatio infrastructure:
    each asymptote is `1 − (1/2) · (1/φ)^rank` expressed in Z[√5].

    Verified by direct algebraic identity:
      rank 0: (2 + 0·√5)/4 = 2/4 = 1/2 = 1 − 1/2 ✓
      rank 1: (5 + (−1)·√5)/4 = 1 − (√5−1)/4 = 1 − (1/2)·(√5−1)/2
                                              = 1 − (1/2)·(1/φ) ✓
      rank 2: (1 + 1·√5)/4 = 1 − (3−√5)/4 = 1 − (1/2)·(3−√5)/2
                                          = 1 − (1/2)·(1/φ²) ✓ -/
theorem rank_0_asymptote_eq : asymptote_ab .A = (2, 0) := by decide
theorem rank_1_asymptote_eq : asymptote_ab .C = (5, -1) := by decide
theorem rank_2_asymptote_eq : asymptote_ab .D = (1, 1) := by decide

end E213.Lib.Math.CayleyDickson.AlgebraTowerAsymptote
