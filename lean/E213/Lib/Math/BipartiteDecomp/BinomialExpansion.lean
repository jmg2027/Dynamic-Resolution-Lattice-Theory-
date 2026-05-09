import E213.Lib.Math.BipartiteDecomp.AdditiveCheck

/-!
# Binomial Expansion `(3+2)²⁵ = 5²⁵` (∅-axiom)

The CORRECT decomposition: not `3²⁵ + 2²⁵` but
`(3+2)²⁵ = Σ_{k=0}^{25} C(25, k) · 3^k · 2^(25-k)`.

Each binomial term encodes a partition of 25 doublings:
  * `k` of them are S-type (factor 3 = N_S)
  * `25 − k` of them are T-type (factor 2 = N_T)

213-native: the 25-level CD tower is **bipartite** at each level
— S-doubling or T-doubling.  Total branches = `(N_S + N_T)^25
= 5^25 = N_U`.

Atomic content:
  * `(3+2)^25 = 5^25` rfl identity.
  * Concrete binomial term values at `k = 0, 1, 12, 13, 25`.
-/

namespace E213.Lib.Math.BipartiteDecomp.BinomialExpansion

open E213.Lib.Math.BipartiteDecomp.AdditiveCheck (substrate_sum)

/-- ★ **Binomial closure**: `(3+2)^25 = 5^25` exactly. -/
theorem binomial_closure : ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25 := by
  rw [substrate_sum.symm]

/-- ★ **First term**: `k = 0` term = `3^0 · 2^25 = 2^25 = 33554432`.
    The "all-T" partition. -/
theorem first_term : (3 : Nat) ^ 0 * (2 : Nat) ^ 25 = 33554432 := rfl

/-- ★ **Last term**: `k = 25` term = `3^25 · 2^0 = 3^25 = 847288609443`.
    The "all-S" partition. -/
theorem last_term : (3 : Nat) ^ 25 * (2 : Nat) ^ 0 = 847288609443 := rfl

/-- ★ **Edge sum** (k=0 + k=25): the two pure-type partitions
    contribute `2²⁵ + 3²⁵` = naive sum (too small). -/
theorem edge_sum :
    (3 : Nat) ^ 0 * (2 : Nat) ^ 25
    + (3 : Nat) ^ 25 * (2 : Nat) ^ 0
    = 847322163875 := rfl

/-- ★ **Mixed term k=12**: `3^12 · 2^13` (S-doublings dominate
    by 1 less). -/
theorem mid_term_12 :
    (3 : Nat) ^ 12 * (2 : Nat) ^ 13 = 4353564672 := rfl

/-- ★ **Mixed term k=13**: `3^13 · 2^12` (S-doublings dominate). -/
theorem mid_term_13 :
    (3 : Nat) ^ 13 * (2 : Nat) ^ 12 = 6530347008 := rfl

end E213.Lib.Math.BipartiteDecomp.BinomialExpansion
