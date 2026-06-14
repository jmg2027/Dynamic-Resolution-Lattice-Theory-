import E213.Lib.Math.Probability.Information.Entropy
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.Pow213

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

namespace E213.Lib.Math.Probability.Information.MutualInfo

open E213.Lib.Math.Probability.Information.Entropy (shannonEntropyUniformBits)

/-- Joint entropy of two independent dyadic uniforms (sizes 2^n, 2^m)
    is `n + m` bits. -/
def jointEntropyIndependentUniforms (n m : Nat) : Nat := n + m

/-- ★ **Joint of independent uniforms** ★ — additivity of entropy
    under independence (rfl in dyadic Lens coordinates). -/
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

/-- `2^a ≤ 2^b ⟹ a ≤ b` — the dyadic exponential reflects order (strict
    monotonicity reversed). -/
theorem exp_le_of_pow_le {a b : Nat} (h : 2 ^ a ≤ 2 ^ b) : a ≤ b := by
  rcases Nat.lt_or_ge b a with hlt | hge
  · exact absurd h (Nat.not_le.mpr (E213.Tactic.Pow213.pow_lt_pow_two b a hlt))
  · exact hge

/-- ★★ **Subadditivity of dyadic entropy.**  If the joint source has `2^j`
    equiprobable outcomes embedded in the product space `2^n × 2^m = 2^(n+m)`
    (`2^j ≤ 2^n · 2^m`), then `H(X,Y) = j ≤ n + m = H(X) + H(Y)`.  The joint cannot
    carry more bits than its marginals together — the content that makes mutual
    information *non-vacuously* non-negative (the `Nat.sub` does not clamp). -/
theorem entropy_subadditive (n m j : Nat) (h : 2 ^ j ≤ 2 ^ n * 2 ^ m) : j ≤ n + m :=
  exp_le_of_pow_le ((E213.Tactic.Pow213.pow_add_two n m).symm ▸ h)

/-- ★ **Mutual information is genuine redundancy** under subadditivity:
    `I(X;Y) + H(X,Y) = H(X) + H(Y)` exactly (`(n+m−j) + j = n+m`, no `Nat.sub`
    clamp), so `I ≥ 0` reflects real shared description length.  `I = 0` iff the
    joint fills the whole product (`j = n+m`, independence). -/
theorem mutualInfo_genuine (n m j : Nat) (h : 2 ^ j ≤ 2 ^ n * 2 ^ m) :
    mutualInfoBits n m j + j = n + m :=
  E213.Tactic.NatHelper.sub_add_cancel (entropy_subadditive n m j h)

/-- Identical dyadic distributions: `I(X; X) = H(X)` (full
    self-information).  H(X,X) = H(X) (joint of identical = the
    same distribution), so I = 2H - H = H. -/
theorem mutualInfo_self_eq_entropy (h : Nat) :
    mutualInfoBits h h h = h := by
  show h + h - h = h
  exact E213.Tactic.NatHelper.add_sub_cancel_right h h

/-- Concrete: fair-coin self-mutual-info = 1 bit. -/
theorem fair_coin_self_info : mutualInfoBits 1 1 1 = 1 := rfl

/-- Concrete: byte self-mutual-info = 8 bits. -/
theorem byte_self_info : mutualInfoBits 8 8 8 = 8 := rfl

end E213.Lib.Math.Probability.Information.MutualInfo
