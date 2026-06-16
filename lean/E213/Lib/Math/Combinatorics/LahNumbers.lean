import E213.Lib.Math.Combinatorics.Permutations
import E213.Meta.Tactic.NatHelper

/-!
# Unsigned Lah numbers `L(n,k)` — structural identities (∅-axiom)

`L(n,k)` counts partitions of an `n`-set into `k` non-empty ordered lists.
Triangular recurrence (mirrors the `stirling1` style):
  `L(0,0)=1`, `L(0,k+1)=0`, `L(n+1,0)=0`, `L(n+1,k+1) = (n+k+1)·L(n,k+1) + L(n,k)`.

  * ★ `lah_rec` — the defining recurrence.
  * ★ `lah_diag` — `L(n,n) = 1` (general).
  * ★ `lah_col1` — `L(n+1,1) = (n+1)!` (general).
  * `lah_table` — the triangle (rows n=1..4).

Genuinely absent (no Lah numbers in the corpus).  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.LahNumbers

open E213.Lib.Math.Combinatorics.Permutations (fact)

/-- Unsigned Lah numbers, `L(n,k)`. -/
def lah : Nat → Nat → Nat
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | _ + 1, 0     => 0
  | n + 1, k + 1 => (n + k + 1) * lah n (k + 1) + lah n k

/-- ★ Defining recurrence, exposed by `rfl`. -/
theorem lah_rec (n k : Nat) :
    lah (n + 1) (k + 1) = (n + k + 1) * lah n (k + 1) + lah n k := rfl

/-- `L(m,k) = 0` when `m < k`. -/
theorem lah_zero_above : ∀ {m k : Nat}, m < k → lah m k = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | m + 1, k + 1, h => by
      have hmk : m < k := Nat.lt_of_succ_lt_succ h
      show (m + k + 1) * lah m (k + 1) + lah m k = 0
      rw [lah_zero_above (Nat.lt_succ_of_lt hmk), lah_zero_above hmk,
          Nat.mul_zero, Nat.add_zero]

/-- ★ Diagonal: `L(n,n) = 1`. -/
theorem lah_diag : ∀ n, lah n n = 1
  | 0 => rfl
  | n + 1 => by
      show (n + n + 1) * lah n (n + 1) + lah n n = 1
      rw [lah_zero_above (Nat.lt_succ_self n), lah_diag n,
          Nat.mul_zero, Nat.zero_add]

/-- ★ First column: `L(n+1, 1) = (n+1)!` (partitions into a single ordered list =
    the `(n+1)!` orderings).  Induction on `n`; `L(m+1,0)=0` kills the tail term. -/
theorem lah_col1 : ∀ n, lah (n + 1) 1 = fact (n + 1)
  | 0 => rfl
  | n + 1 => by
      show ((n + 1) + 0 + 1) * lah (n + 1) 1 + lah (n + 1) 0 = fact (n + 1 + 1)
      show ((n + 1) + 0 + 1) * lah (n + 1) 1 + 0 = fact (n + 1 + 1)
      rw [Nat.add_zero, lah_col1 n]
      show ((n + 1) + 1) * fact (n + 1) = (n + 1 + 1) * fact (n + 1)
      rfl

/-- The triangle, rows `n = 1..4`. -/
theorem lah_table :
    lah 1 1 = 1 ∧
    lah 2 1 = 2 ∧ lah 2 2 = 1 ∧
    lah 3 1 = 6 ∧ lah 3 2 = 6 ∧ lah 3 3 = 1 ∧
    lah 4 1 = 24 ∧ lah 4 2 = 36 ∧ lah 4 3 = 12 ∧ lah 4 4 = 1 := by decide

end E213.Lib.Math.Combinatorics.LahNumbers
