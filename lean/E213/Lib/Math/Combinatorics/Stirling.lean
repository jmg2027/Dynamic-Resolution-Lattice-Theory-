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

/-- Bell number `B_n = Σ_k S(n, k)`. -/
def bell : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 15
  | 5 => 52
  | _ => 0

/-- ★ Stirling + Bell master — boundary values S(0,0)=1, S(1,0)=0,
    diagonals S(n,n)=1, column-1 S(n,1)=1, column-2 values
    (1, 3, 7, 15), Bell table B_0..B_5 = 1, 1, 2, 5, 15, 52, and
    Bell decomposition B_n = Σ_k S(n, k) at n = 3, 4. -/
theorem stirling_bell_master :
    -- Boundary values
    stirling2 0 0 = 1
    ∧ stirling2 1 0 = 0
    -- Diagonal S(n, n) = 1
    ∧ stirling2 1 1 = 1 ∧ stirling2 2 2 = 1
    ∧ stirling2 3 3 = 1 ∧ stirling2 4 4 = 1
    -- Column S(n, 1) = 1
    ∧ stirling2 2 1 = 1 ∧ stirling2 3 1 = 1 ∧ stirling2 4 1 = 1
    -- Column S(n, 2) values: 1, 3, 7, 15
    ∧ stirling2 3 2 = 3 ∧ stirling2 4 2 = 7 ∧ stirling2 5 2 = 15
    -- Bell table
    ∧ bell 0 = 1 ∧ bell 1 = 1 ∧ bell 2 = 2
    ∧ bell 3 = 5 ∧ bell 4 = 15 ∧ bell 5 = 52
    -- Bell decomposition (sums of stirling2 rows)
    ∧ bell 3 = stirling2 3 1 + stirling2 3 2 + stirling2 3 3
    ∧ bell 4 = stirling2 4 1 + stirling2 4 2 + stirling2 4 3 + stirling2 4 4 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> decide

/-- `S(m, k) = 0` when `m < k` (above the diagonal — can't partition `m` elements
    into more than `m` nonempty blocks). -/
theorem stirling2_zero_above : ∀ {m k : Nat}, m < k → stirling2 m k = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | m + 1, k + 1, h => by
      have hmk : m < k := Nat.lt_of_succ_lt_succ h
      show (k + 1) * stirling2 m (k + 1) + stirling2 m k = 0
      rw [stirling2_zero_above (Nat.lt_succ_of_lt hmk), stirling2_zero_above hmk,
          Nat.mul_zero, Nat.add_zero]

/-- ★ **Stirling diagonal `S(n, n) = 1`** — exactly one way to put `n` elements into
    `n` nonempty blocks (each its own singleton).  General `n` (the existing table
    had only concrete `decide` cases). -/
theorem stirling_diag : ∀ n, stirling2 n n = 1
  | 0     => rfl
  | n + 1 => by
      show (n + 1) * stirling2 n (n + 1) + stirling2 n n = 1
      rw [stirling2_zero_above (Nat.lt_succ_self n), Nat.mul_zero, Nat.zero_add,
          stirling_diag n]

/-- ★ **Stirling column-1 `S(n+1, 1) = 1`** — exactly one way to put `n+1` elements
    into a single block.  General `n`. -/
theorem stirling_col1 : ∀ n, stirling2 (n + 1) 1 = 1
  | 0     => rfl
  | n + 1 => by
      have h0 : stirling2 (n + 1) 0 = 0 := rfl
      show 1 * stirling2 (n + 1) 1 + stirling2 (n + 1) 0 = 1
      rw [stirling_col1 n, h0]

/-- ★ **Stirling column-2 recurrence `S(n+2, 2) = 2·S(n+1, 2) + 1`** — the closed
    form `S(n,2) = 2^(n-1) − 1` as a division-free recurrence (general `n`; the file
    had only the tabulated values `1,3,7,15`). -/
theorem stirling_col2_rec (n : Nat) :
    stirling2 (n + 2) 2 = 2 * stirling2 (n + 1) 2 + 1 := by
  show 2 * stirling2 (n + 1) 2 + stirling2 (n + 1) 1 = 2 * stirling2 (n + 1) 2 + 1
  rw [stirling_col1 n]

end E213.Lib.Math.Combinatorics.Stirling
