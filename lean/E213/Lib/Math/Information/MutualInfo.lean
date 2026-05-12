import E213.Lib.Math.Information.Entropy
import E213.Meta.Tactic.Nat213

/-!
# Information — Joint entropy + mutual information (atomic)

For two independent uniform dyadic distributions (X uniform over
`2^n`, Y uniform over `2^m`):

  * Joint entropy: `H(X, Y) = n + m` (joint uniform over `2^(n+m)`).
  * Mutual information: `I(X; Y) = H(X) + H(Y) − H(X, Y) = 0`.

Independence ⇒ zero mutual information, atomically.

For correlated dyadic distributions (joint not factoring), the
mutual information equals the *redundancy bits* — how much
description-length is shared between X and Y.  Atomic on dyadic
substrate.
-/

namespace E213.Lib.Math.Information.MutualInfo

open E213.Lib.Math.Information.Entropy (shannonEntropyUniformBits)

/-- Joint entropy of two independent dyadic uniforms (sizes 2^n, 2^m)
    is `n + m` bits. -/
def jointEntropyIndependentUniforms (n m : Nat) : Nat := n + m

/-- ★ **Joint of independent uniforms** ★ — additivity of entropy
    under independence (rfl on dyadic substrate). -/
theorem joint_independent_eq_sum (n m : Nat) :
    jointEntropyIndependentUniforms n m
    = shannonEntropyUniformBits n + shannonEntropyUniformBits m := rfl

/-- Mutual information of independent dyadic uniforms = 0. -/
def mutualInfoIndependent (n m : Nat) : Nat :=
  shannonEntropyUniformBits n + shannonEntropyUniformBits m
    - jointEntropyIndependentUniforms n m

/-- ★ **Independence ⇒ zero mutual information** ★ (atomic). -/
theorem mutualInfo_independent_zero (n m : Nat) :
    mutualInfoIndependent n m = 0 := by
  show n + m - (n + m) = 0
  exact Nat.sub_self (n + m)

/-- For correlated dyadic distributions: `I(X; Y) = H(X) + H(Y) -
    H(X, Y)` where the joint may be smaller than the product (i.e.
    correlation reduces joint entropy below the sum). -/
def mutualInfoBits (h_x h_y h_joint : Nat) : Nat :=
  h_x + h_y - h_joint

/-- Mutual info ≥ 0 by `Nat.sub` clamping when joint ≤ marginals
    sum. -/
theorem mutualInfo_clamped (h_x h_y h_joint : Nat) :
    mutualInfoBits h_x h_y h_joint ≥ 0 := Nat.zero_le _

/-- Identical dyadic distributions: `I(X; X) = H(X)` (full
    self-information).  H(X,X) = H(X) (joint of identical = the
    same distribution), so I = 2H - H = H. -/
theorem mutualInfo_self_eq_entropy (h : Nat) :
    mutualInfoBits h h h = h := by
  show h + h - h = h
  exact E213.Tactic.Nat213.add_sub_cancel_right h h

/-- Concrete: fair-coin self-mutual-info = 1 bit. -/
theorem fair_coin_self_info : mutualInfoBits 1 1 1 = 1 := rfl

/-- Concrete: byte self-mutual-info = 8 bits. -/
theorem byte_self_info : mutualInfoBits 8 8 8 = 8 := rfl

end E213.Lib.Math.Information.MutualInfo
