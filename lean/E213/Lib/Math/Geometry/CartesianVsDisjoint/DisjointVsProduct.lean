import E213.Lib.Math.Geometry.CartesianVsDisjoint.CartesianCheck

/-!
# Disjoint Union vs Cartesian Product (∅-axiom)

The structural distinction between two operations on (3, 2):

| Operation | Result | Combinatorial meaning |
|---|---|---|
| Disjoint sum `S ⊔ T` | `|S| + |T| = 5` | union of vertex sets |
| Cartesian product `S × T` | `|S| · |T| = 6` | pairs of vertices |
| Power-sum `(|S| + |T|)^n` | `5^n` | sequences over union |
| Power-product `|S|^n · |T|^n` | `6^n` | sequences over product |

K_{3,2} substrate uses **disjoint union** (5 vertices).  Mingu's
"Cartesian product" hypothesis would correspond to a different
graph (K_{3×2} or product graph).

213-native: the bipartite K_{3,2} has 5 vertices because S and T
are **distinguished but disjoint** roles, not coordinatized pairs.
-/

namespace E213.Lib.Math.Geometry.CartesianVsDisjoint.DisjointVsProduct

/-- ★ **Disjoint sum cardinality**: `|S| + |T| = 5`. -/
theorem disjoint_sum_card : (3 : Nat) + 2 = 5 := rfl

/-- ★ **Cartesian product cardinality**: `|S| × |T| = 6`. -/
theorem cartesian_product_card : (3 : Nat) * 2 = 6 := rfl

/-- ★ **5 ≠ 6**: disjoint sum and Cartesian product distinct. -/
theorem disjoint_neq_cartesian : (5 : Nat) ≠ 6 := by decide

/-- ★ **Power-sum (binomial) vs Power-product**: at level 25,
    binomial gives `5²⁵`, product gives `6²⁵`.  PURE — both sides
    evaluate to literal Nat values, closed by `decide`. -/
theorem power_dichotomy :
    ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25
    ∧ (3 : Nat) ^ 25 * (2 : Nat) ^ 25 = (6 : Nat) ^ 25 :=
  ⟨rfl, by decide⟩

/-- ★ **Strict separation**: `5²⁵ < 6²⁵` (binomial < product). -/
theorem strict_sep :
    (5 : Nat) ^ 25 < (6 : Nat) ^ 25 := by decide

/-- ★ **K_{3,2} structure**: 5-vertex bipartite, NOT 6-vertex
    product.  Edge count `3 · 2 · c = 12` per c=2. -/
theorem k32_disjoint_5 :
    (3 : Nat) + 2 = 5
    ∧ (3 : Nat) * 2 * 2 = 12 :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.Geometry.CartesianVsDisjoint.DisjointVsProduct
