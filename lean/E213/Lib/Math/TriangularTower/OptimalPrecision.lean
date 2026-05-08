import E213.Lib.Math.TriangularTower.PropertySurvival

/-!
# Optimal Bit Precision per Level (∅-axiom)

Mingu's insight:
> "각 층에 꼭 맞는 비트정밀도(3의 크기)가 있을거같아.
>  그러면 그 층에서는 성질이 버려지지 않겠지"

213-native: in `(3+2)²⁵ = Σ C(25,k) · 3^k · 2^(25-k)`, each
term `k` represents a partition with `k` S-doublings (3-axis
info) and `25-k` T-doublings (2-axis force).

Mingu's hypothesis: each level `n` has optimal `k = n`
preserving all properties.
-/

namespace E213.Lib.Math.TriangularTower.OptimalPrecision

/-- Optimal k per level (hypothesis: identity). -/
def optimalK (n : Nat) : Nat := n

/-- ★ optimal at 0/1/2/25. -/
theorem optimalK_values :
    optimalK 0 = 0
    ∧ optimalK 1 = 1
    ∧ optimalK 2 = 2
    ∧ optimalK 25 = 25 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Optimal contribution at level n: `3^n · 2^(25-n)`. -/
def optimalContribution (n : Nat) : Nat := 3 ^ n * 2 ^ (25 - n)

/-- ★ Optimal contribution at level 0: `2²⁵`. -/
theorem optimalContribution_0 :
    optimalContribution 0 = 33554432 := rfl

/-- ★ Optimal contribution at level 25: `3²⁵`. -/
theorem optimalContribution_25 :
    optimalContribution 25 = 847288609443 := rfl

/-- ★ Optimal contribution at level 12: `3¹² · 2¹³`. -/
theorem optimalContribution_12 :
    optimalContribution 12 = 4353564672 := rfl

/-- ★ **Property preservation hypothesis**: at level n, if the
    partition matches `optimalK n`, then no peeling — all
    surviving properties of level 0 are preserved at level n
    *under the right precision*.

    This is a structural posit (not yet proven from first
    principles); it captures Mingu's insight that the loss is
    a function of mismatch, not unavoidable. -/
def preservesAllProperties (n : Nat) (k : Nat) : Prop :=
  k = optimalK n

/-- ★ At level 0 with k=0, all properties preserved. -/
theorem preserve_at_0 : preservesAllProperties 0 0 := rfl

/-- ★ At level 25 with k=25, the residual (Z/2 + norm + N_U)
    counts as "the level-25 surviving structure" — no further
    loss. -/
theorem preserve_at_25 : preservesAllProperties 25 25 := rfl

end E213.Lib.Math.TriangularTower.OptimalPrecision
