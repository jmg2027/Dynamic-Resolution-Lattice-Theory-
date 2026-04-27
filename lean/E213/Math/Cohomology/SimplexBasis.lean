import E213.Math.Cohomology.Cochain

/-!
# Cohomology — k-subset enumeration (Phase CA, file 2)

To define the coboundary δ: Cᵏ → Cᵏ⁺¹, we need a fixed bijection
between `Fin (binom n k)` and the k-element subsets of {0..n-1}.

We use the colex order via the standard recursion:
  k-subsets of {0..n} = (k-subsets of {0..n-1})
                     ∪ {S ∪ {n} | S a (k-1)-subset of {0..n-1}}

The first family has size `binom n k`, the second `binom n (k-1)`.
So `binom (n+1) k = binom n k + binom n (k-1)` (Pascal).
-/

namespace E213.Math.Cohomology

open E213.Physics.Simplex (binom d NS NT)

/-- The i-th k-subset of {0..n-1} in colex order, as a sorted
    list of length k.  Recursion on n.

    For `(n+1, k+1, i)`:
      - first `binom n (k+1)` indices map to k+1-subsets of {0..n-1}
      - remaining `binom n k` map to k-subsets of {0..n-1} ∪ {n}
-/
def kSubset : Nat → Nat → Nat → List Nat
  | 0,     0,     _ => []
  | 0,     _ + 1, _ => []
  | _ + 1, 0,     _ => []
  | n + 1, k + 1, i =>
    let split := binom n (k + 1)
    if i < split then kSubset n (k + 1) i
    else kSubset n k (i - split) ++ [n]

/-- Smoke: the unique 0-subset of {0..n-1} is empty. -/
theorem kSubset_0 (n : Nat) : kSubset n 0 0 = [] := by
  cases n <;> rfl

/-- Smoke: 1-subsets of {0..4} = [[0],[1],[2],[3],[4]]. -/
theorem kSubset_1_of_5 :
    kSubset 5 1 0 = [0]
    ∧ kSubset 5 1 1 = [1]
    ∧ kSubset 5 1 2 = [2]
    ∧ kSubset 5 1 3 = [3]
    ∧ kSubset 5 1 4 = [4] := by decide

/-- Smoke: first 2-subsets of {0..4}. -/
theorem kSubset_2_of_5_first :
    kSubset 5 2 0 = [0, 1]
    ∧ kSubset 5 2 1 = [0, 2]
    ∧ kSubset 5 2 2 = [1, 2] := by decide

/-- Smoke: last 2-subset of {0..4} is [3,4]. -/
theorem kSubset_2_of_5_last :
    kSubset 5 2 9 = [3, 4] := by decide

/-- Smoke: the unique 5-subset of {0..4}. -/
theorem kSubset_5_of_5 :
    kSubset 5 5 0 = [0, 1, 2, 3, 4] := by decide

/-- Smoke: every 1-subset at d=5 has length 1 (decide-checked). -/
theorem kSubset_1_length_d5 :
    (kSubset 5 1 0).length = 1
    ∧ (kSubset 5 1 1).length = 1
    ∧ (kSubset 5 1 2).length = 1
    ∧ (kSubset 5 1 3).length = 1
    ∧ (kSubset 5 1 4).length = 1 := by decide

/-- Smoke: every 2-subset at d=5 has length 2 (decide-checked). -/
theorem kSubset_2_length_d5 :
    (kSubset 5 2 0).length = 2
    ∧ (kSubset 5 2 5).length = 2
    ∧ (kSubset 5 2 9).length = 2 := by decide

end E213.Math.Cohomology
