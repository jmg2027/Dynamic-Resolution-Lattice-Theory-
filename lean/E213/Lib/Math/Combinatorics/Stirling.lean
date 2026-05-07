/-!
# Combinatorics — Stirling numbers (second kind) + Bell

Stirling numbers of the second kind `S(n, k)`: number of ways to
partition n elements into k non-empty subsets.

  Recursion: `S(n+1, k) = k · S(n, k) + S(n, k-1)`.

Bell numbers `B_n = Σ_k S(n, k)`: total number of partitions.

Atomic: hand-tabulated for n = 0..5 (sufficient for K_{3,2} ⊂ Δ⁴
substrate combinatorics).
-/

namespace E213.Lib.Math.Combinatorics.Stirling

/-- Stirling numbers of the second kind, S(n, k). -/
def stirling2 : Nat → Nat → Nat
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | _ + 1, 0     => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- S(0, 0) = 1, S(n, 0) = 0 for n ≥ 1. -/
theorem stirling2_0_0 : stirling2 0 0 = 1 := rfl
theorem stirling2_1_0 : stirling2 1 0 = 0 := rfl

/-- S(n, n) = 1 for small n. -/
theorem stirling2_diag :
    stirling2 1 1 = 1 ∧ stirling2 2 2 = 1
    ∧ stirling2 3 3 = 1 ∧ stirling2 4 4 = 1 := by decide

/-- ★ **S(n, 1) = 1**: only one way to partition n into 1 subset. -/
theorem stirling2_n_1 :
    stirling2 1 1 = 1 ∧ stirling2 2 1 = 1
    ∧ stirling2 3 1 = 1 ∧ stirling2 4 1 = 1 := by decide

/-- ★ **S(n, 2) values**: 1, 3, 7, 15 (= 2^(n-1) - 1 for small n). -/
theorem stirling2_n_2 :
    stirling2 2 2 = 1 ∧ stirling2 3 2 = 3
    ∧ stirling2 4 2 = 7 ∧ stirling2 5 2 = 15 := by decide

/-- Bell number `B_n = Σ_k S(n, k)`. -/
def bell : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 15
  | 5 => 52
  | _ => 0

/-- Bell number table: 1, 1, 2, 5, 15, 52. -/
theorem bell_table :
    bell 0 = 1 ∧ bell 1 = 1 ∧ bell 2 = 2
    ∧ bell 3 = 5 ∧ bell 4 = 15 ∧ bell 5 = 52 := by decide

/-- B₃ = 5 = S(3,1) + S(3,2) + S(3,3) = 1 + 3 + 1 = 5. ✓ -/
theorem bell_3_decompose :
    bell 3 = stirling2 3 1 + stirling2 3 2 + stirling2 3 3 := by decide

/-- B₄ = 15 = 1 + 7 + 6 + 1. ✓ -/
theorem bell_4_decompose :
    bell 4 = stirling2 4 1 + stirling2 4 2 + stirling2 4 3 + stirling2 4 4 :=
  by decide

end E213.Lib.Math.Combinatorics.Stirling
