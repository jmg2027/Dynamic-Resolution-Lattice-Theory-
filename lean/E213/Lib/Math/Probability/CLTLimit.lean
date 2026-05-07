import E213.Lib.Math.Probability.Concentration

/-!
# Probability — Cauchy-modulus form of LLN

The Cauchy-modulus refinement of `LLN_unit`: balanced fair-coin
sample mean stays within ε of `1/2` for *any* ε ≥ 0, with modulus
`N(ε) = 0` (no tail needed — every term hits zero deviation).

This is the atomic LLN as a Cauchy convergence statement: the
sequence of balanced sample means is constant (= `1/2`) at every n,
so trivially Cauchy.

For *generic* sequences, the modulus depends on the sequence; the
balanced specialisation collapses to the trivial modulus.

213-native: Bishop-style Cauchy modulus, no ε-N quantifier juggling
beyond what `Nat` arithmetic can express.
-/

namespace E213.Lib.Math.Probability.CLTLimit

open E213.Lib.Math.Probability.SampleMean (countTrue)
open E213.Lib.Math.Probability.LLN (balancedHeadsTails)
open E213.Lib.Math.Probability.Concentration
  (centeredAbsDev2 centeredAbsDev2_balanced)

/-- ★ **Cauchy-modulus LLN (atomic form)** ★ — balanced fair-coin
    sample mean stays within ε of `1/2` for every ε, every n.
    Modulus `N(ε) = 0`: no tail needed, deviation is identically 0. -/
theorem balanced_LLN_modulus (ε : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      centeredAbsDev2 (balancedHeadsTails n) ≤ ε :=
  ⟨0, fun n _ => by
    rw [centeredAbsDev2_balanced]
    exact Nat.zero_le ε⟩

/-- Cauchy property of balanced sample-mean deviations: any two
    terms have identical deviation (both = 0). -/
theorem balanced_cauchy (n m : Nat) :
    centeredAbsDev2 (balancedHeadsTails n)
    = centeredAbsDev2 (balancedHeadsTails m) := by
  rw [centeredAbsDev2_balanced n, centeredAbsDev2_balanced m]

/-- **Modulus zero** — explicit witness: `N(ε) = 0` works for every ε. -/
theorem modulus_witness (ε : Nat) :
    ∀ n : Nat, 0 ≤ n →
      centeredAbsDev2 (balancedHeadsTails n) ≤ ε :=
  fun n _ => by
    rw [centeredAbsDev2_balanced]
    exact Nat.zero_le ε

/-- Bridge: balanced length-`2n` sample's countTrue `n` over total
    `2n` cross-multiplies to `1/2`.  `n · 2 = 2n · 1` (LLN_unit). -/
theorem balanced_eq_half (n : Nat) :
    countTrue (balancedHeadsTails n) * 2
    = (balancedHeadsTails n).length * 1 :=
  E213.Lib.Math.Probability.LLN.fair_LLN n

end E213.Lib.Math.Probability.CLTLimit
