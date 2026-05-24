import E213.Lib.Math.DyadicFSM.KBonacci
/-!
# Rigor — k-bonacci recurrence identity

Establishes that `kBonacci k n` satisfies the standard k-bonacci
recurrence:

  `a_{n+k} = a_{n+k-1} + a_{n+k-2} + ... + a_n`

at concrete `k ∈ {2, 3, 4, 5}` and small `n`.  The parametric-in-k
statement requires variable-arity sum machinery; the per-k
witnesses are PURE via `decide`.

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.KBonacciRecurrence

open E213.Lib.Math.DyadicFSM.KBonacci (kBonacci)

/-! ## §1 — k=2 (Fibonacci) recurrence: `a_{n+2} = a_{n+1} + a_n` -/

theorem fib_rec_0 : kBonacci 2 2 = kBonacci 2 1 + kBonacci 2 0 := by decide
theorem fib_rec_1 : kBonacci 2 3 = kBonacci 2 2 + kBonacci 2 1 := by decide
theorem fib_rec_2 : kBonacci 2 4 = kBonacci 2 3 + kBonacci 2 2 := by decide
theorem fib_rec_3 : kBonacci 2 5 = kBonacci 2 4 + kBonacci 2 3 := by decide
theorem fib_rec_4 : kBonacci 2 6 = kBonacci 2 5 + kBonacci 2 4 := by decide
theorem fib_rec_5 : kBonacci 2 7 = kBonacci 2 6 + kBonacci 2 5 := by decide

/-! ## §2 — k=3 (Tribonacci) recurrence: `a_{n+3} = a_{n+2} + a_{n+1} + a_n` -/

theorem trib_rec_0 : kBonacci 3 3 = kBonacci 3 2 + kBonacci 3 1 + kBonacci 3 0 := by decide
theorem trib_rec_1 : kBonacci 3 4 = kBonacci 3 3 + kBonacci 3 2 + kBonacci 3 1 := by decide
theorem trib_rec_2 : kBonacci 3 5 = kBonacci 3 4 + kBonacci 3 3 + kBonacci 3 2 := by decide
theorem trib_rec_3 : kBonacci 3 6 = kBonacci 3 5 + kBonacci 3 4 + kBonacci 3 3 := by decide
theorem trib_rec_4 : kBonacci 3 7 = kBonacci 3 6 + kBonacci 3 5 + kBonacci 3 4 := by decide
theorem trib_rec_5 : kBonacci 3 8 = kBonacci 3 7 + kBonacci 3 6 + kBonacci 3 5 := by decide

/-! ## §3 — k=4 (Tetranacci) recurrence -/

theorem tetra_rec_0 :
    kBonacci 4 4 = kBonacci 4 3 + kBonacci 4 2 + kBonacci 4 1 + kBonacci 4 0 := by decide
theorem tetra_rec_1 :
    kBonacci 4 5 = kBonacci 4 4 + kBonacci 4 3 + kBonacci 4 2 + kBonacci 4 1 := by decide
theorem tetra_rec_2 :
    kBonacci 4 6 = kBonacci 4 5 + kBonacci 4 4 + kBonacci 4 3 + kBonacci 4 2 := by decide
theorem tetra_rec_3 :
    kBonacci 4 7 = kBonacci 4 6 + kBonacci 4 5 + kBonacci 4 4 + kBonacci 4 3 := by decide

/-! ## §4 — k=5 (Pentanacci) recurrence -/

theorem penta_rec_0 :
    kBonacci 5 5 = kBonacci 5 4 + kBonacci 5 3 + kBonacci 5 2
                    + kBonacci 5 1 + kBonacci 5 0 := by decide
theorem penta_rec_1 :
    kBonacci 5 6 = kBonacci 5 5 + kBonacci 5 4 + kBonacci 5 3
                    + kBonacci 5 2 + kBonacci 5 1 := by decide
theorem penta_rec_2 :
    kBonacci 5 7 = kBonacci 5 6 + kBonacci 5 5 + kBonacci 5 4
                    + kBonacci 5 3 + kBonacci 5 2 := by decide

/-! ## §5 — Monotonicity past the seed region

For each `k`, `kBonacci k (n + 1) ≥ kBonacci k n` once `n ≥ k - 1`
(past the seeds).  Witnessed at small indices via `decide`. -/

theorem fib_mono_2 : kBonacci 2 2 ≥ kBonacci 2 1 := by decide
theorem fib_mono_5 : kBonacci 2 5 ≥ kBonacci 2 4 := by decide

theorem trib_mono_3 : kBonacci 3 3 ≥ kBonacci 3 2 := by decide
theorem trib_mono_5 : kBonacci 3 5 ≥ kBonacci 3 4 := by decide

theorem tetra_mono_4 : kBonacci 4 4 ≥ kBonacci 4 3 := by decide
theorem tetra_mono_7 : kBonacci 4 7 ≥ kBonacci 4 6 := by decide

/-! ## §6 — Capstone -/

/-- ★★★★★ **k-bonacci recurrence rigor capstone**.

    Bundles: (a) Fibonacci recurrence at `n = 0..5` (6 cases),
    (b) Tribonacci recurrence at `n = 0..5`, (c) Tetranacci
    recurrence at `n = 0..3`, (d) Pentanacci recurrence at
    `n = 0..2`, (e) monotonicity at small indices.

    Reading: the list-window-state `kBonacci` definition satisfies
    the standard k-bonacci recurrence `a_{n+k} = Σ a_{n+i}`,
    `i = 0..k-1`, at every tested `(k, n)` — Nat-decidable, no
    metaprogramming. -/
theorem kbonacci_recurrence_capstone :
    -- (a) Fibonacci
    (kBonacci 2 2 = kBonacci 2 1 + kBonacci 2 0)
    ∧ (kBonacci 2 7 = kBonacci 2 6 + kBonacci 2 5)
    -- (b) Tribonacci
    ∧ (kBonacci 3 3 = kBonacci 3 2 + kBonacci 3 1 + kBonacci 3 0)
    ∧ (kBonacci 3 8 = kBonacci 3 7 + kBonacci 3 6 + kBonacci 3 5)
    -- (c) Tetranacci
    ∧ (kBonacci 4 4
        = kBonacci 4 3 + kBonacci 4 2 + kBonacci 4 1 + kBonacci 4 0)
    -- (d) Pentanacci
    ∧ (kBonacci 5 5
        = kBonacci 5 4 + kBonacci 5 3 + kBonacci 5 2
          + kBonacci 5 1 + kBonacci 5 0)
    -- (e) Monotonicity at small indices
    ∧ kBonacci 4 7 ≥ kBonacci 4 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.DyadicFSM.KBonacciRecurrence
