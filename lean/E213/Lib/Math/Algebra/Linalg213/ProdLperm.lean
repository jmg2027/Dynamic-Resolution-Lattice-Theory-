import E213.Lib.Math.Algebra.Linalg213.Permutation

/-!
# Linalg213 — `prodZ` and its permutation-invariance

The multiplicative analog of `Permutation.sumZ` / `sumZ_lperm`: a product of integers is invariant
under reordering (`LPerm`).  The foundation for the reindexing in the **transpose determinant**
`det Mᵀ = det M` (the Leibniz term of `Mᵀ` is the Leibniz term of `M` at the inverse permutation,
up to reordering the diagonal-product factors).  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.ProdLperm

open E213.Lib.Math.Algebra.Linalg213.Permutation (LPerm)

/-- Product of an `Int` list. -/
def prodZ : List Int → Int
  | []      => 1
  | x :: xs => x * prodZ xs

/-- ★ **A product is invariant under `LPerm`** (reordering the factors).  Mirrors `sumZ_lperm`. -/
theorem prodZ_lperm {l₁ l₂ : List Int} (h : LPerm l₁ l₂) : prodZ l₁ = prodZ l₂ := by
  induction h with
  | nil               => rfl
  | cons x _ ih       => show x * prodZ _ = x * prodZ _; rw [ih]
  | swap x y l        =>
    show y * (x * prodZ l) = x * (y * prodZ l)
    exact E213.Meta.Int213.mul_left_comm y x (prodZ l)
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- `prodZ` over an append splits. -/
theorem prodZ_append : ∀ (L M : List Int), prodZ (L ++ M) = prodZ L * prodZ M
  | [],      M => by show prodZ M = 1 * prodZ M; rw [Int.one_mul]
  | x :: xs, M => by
    show x * prodZ (xs ++ M) = x * prodZ xs * prodZ M
    rw [prodZ_append xs M, E213.Meta.Int213.mul_assoc]

end E213.Lib.Math.Algebra.Linalg213.ProdLperm
