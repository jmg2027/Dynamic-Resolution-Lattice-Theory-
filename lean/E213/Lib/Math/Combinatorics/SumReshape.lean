import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# 1D ↔ 2D reshape of the `sumTo` toolkit (∅-axiom)

Two genuinely-absent structural counting identities for the corpus Nat `sumTo`
(`E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum`):

  * `sumTo_concat`  — **range concatenation / splitting**
        `Σ_{k<m+n} f k = Σ_{k<m} f k + Σ_{k<n} f (m+k)`
    a sum over `[0, m+n)` splits at any interior point `m` into the head block
    `[0,m)` plus the tail block `[m, m+n)` (reindexed `k ↦ m+k`).

  * `sumTo_reshape` — **1D → 2D reshape (division-algorithm reindexing)**
        `Σ_{k < m·n} g k = Σ_{i<m} Σ_{j<n} g (i·n + j)`
    counting a length-`m·n` line equals counting the `m × n` grid whose `(i,j)`
    cell carries the linear index `i·n + j` — the double-counting principle
    behind `|A×B| = |A|·|B|` and the block-decomposition of a flat sum.

Plus the general constant sum `sumTo_const` (`Σ_{i<n} c = n·c`; only the `c=0,1`
cases existed).  Add-linearity (`sumTo_add_func`), scaling (`sumTo_mul_left`),
`sumTo_congr` and `sumTo_fubini` are already in the corpus and are not duplicated.

All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.SumReshape

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)

/-- **Σ of a constant**: `Σ_{i<n} c = n · c`.  Clean induction on `n`. -/
theorem sumTo_const (c : Nat) : ∀ n, sumTo n (fun _ => c) = n * c
  | 0 => by show (0 : Nat) = 0 * c; rw [Nat.zero_mul]
  | n + 1 => by
    rw [sumTo_succ, sumTo_const c n]
    ring_nat

/-- ★ **Range concatenation / splitting**:
    `Σ_{k<m+n} f k = Σ_{k<m} f k + Σ_{k<n} f (m+k)`.

    A sum over `[0, m+n)` splits at the interior point `m` into the head block
    `[0,m)` plus the tail block `[m, m+n)`, the latter reindexed `k ↦ m+k`.
    Induction on `n`. -/
theorem sumTo_concat (f : Nat → Nat) (m : Nat) :
    ∀ n, sumTo (m + n) f = sumTo m f + sumTo n (fun k => f (m + k))
  | 0 => by
    show sumTo m f = sumTo m f + sumTo 0 (fun k => f (m + k))
    rw [sumTo_zero]
    rw [Nat.add_zero]
  | n + 1 => by
    show sumTo (m + n + 1) f = sumTo m f + sumTo (n + 1) (fun k => f (m + k))
    rw [sumTo_succ, sumTo_concat f m n, sumTo_succ]
    rw [Nat.add_assoc]

/-- ★ **1D → 2D reshape (division-algorithm reindexing)**:
    `Σ_{k < m·n} g k = Σ_{i<m} Σ_{j<n} g (i·n + j)`.

    Counting the flat line `[0, m·n)` equals counting the `m × n` grid whose
    `(i,j)` cell carries the linear index `i·n + j`.  Induction on `m`: split the
    flat range `[0, (m+1)·n)` at `m·n` (via `sumTo_concat`, using `(m+1)·n =
    m·n + n`); the head block matches the IH grid, and the tail block — reindexed
    `j ↦ m·n + j` — is exactly the new row `i = m` (cell index `m·n + j`,
    matched definitionally). -/
theorem sumTo_reshape (g : Nat → Nat) (n : Nat) :
    ∀ m, sumTo (m * n) g = sumTo m (fun i => sumTo n (fun j => g (i * n + j)))
  | 0 => by
    show sumTo (0 * n) g = sumTo 0 (fun i => sumTo n (fun j => g (i * n + j)))
    rw [Nat.zero_mul]
    rfl
  | m + 1 => by
    show sumTo ((m + 1) * n) g
        = sumTo m (fun i => sumTo n (fun j => g (i * n + j)))
          + sumTo n (fun j => g (m * n + j))
    rw [Nat.succ_mul]
    rw [sumTo_concat g (m * n) n, sumTo_reshape g n m]

/-- Smoke: flatten a `3 × 4` grid (`g k = k`) — `Σ_{k<12} k = 66 = Σ_{i<3} Σ_{j<4} (4i+j)`;
    a concat split; and a constant sum. -/
theorem reshape_smoke :
    sumTo 12 (fun k => k) = sumTo 3 (fun i => sumTo 4 (fun j => i * 4 + j))
    ∧ sumTo 5 (fun k => k) = sumTo 2 (fun k => k) + sumTo 3 (fun k => 2 + k)
    ∧ sumTo 7 (fun _ => 5) = 35 := by
  refine ⟨by decide, by decide, by decide⟩

end E213.Lib.Math.Combinatorics.SumReshape
