import E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal
import E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock

/-!
# Mobius213.Px.QFibIdentity — Universal P^n ↔ Fibonacci identity

Proves the universal connection between the 1-step matrix entries
`Q00, Q01, Q11` (from `PnFibonacciUniversal`) and the Fibonacci
sequence `fib` (from `FibonacciAtomicLock`):

  · `Q00 n = fib (2 * n + 1)` — top-left of P^n = fib at odd index
  · `Q01 n = fib (2 * n)`     — off-diagonal of P^n = fib at even index
  · `Q11 n = fib (2 * n - 1)` — bottom-right (handled as `Q11 (n+1) = Q00 n`)

These lift `PnFibonacci`'s concrete checks (n = 0..5) to ∀n.

## Proof strategy

Mutual induction on `n`:
  · Base: `Q00 0 = 1 = fib 1`, `Q01 0 = 0 = fib 0`.
  · Step: use the Fibonacci double-step recurrence
    `fib(2n+3) = 2·fib(2n+1) + fib(2n)` (matching Q00 recurrence)
    and `fib(2n+2) = fib(2n+1) + fib(2n)` (matching Q01 recurrence).

The Fibonacci double-step identity is derived from two applications
of the standard recurrence `fib(k+2) = fib(k+1) + fib(k)`.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.QFibIdentity

open E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)

/-! ## §1 — Fibonacci double-step recurrences -/

/-- Standard Fibonacci recurrence exposed for rewriting. -/
theorem fib_succ_succ (k : Nat) : fib (k + 2) = fib (k + 1) + fib k := rfl

/-- ★ **Fibonacci at even index**: `fib(2n+2) = fib(2n+1) + fib(2n)`.
    This is just `fib_succ_succ` at `k = 2n`. -/
theorem fib_even_step (n : Nat) :
    fib (2 * n + 2) = fib (2 * n + 1) + fib (2 * n) := rfl

/-- ★ **Fibonacci double-step (odd)**: `fib(2n+3) = 2·fib(2n+1) + fib(2n)`.

    Proof: `fib(2n+3) = fib(2n+2) + fib(2n+1)`      — standard recurrence
                      `= (fib(2n+1) + fib(2n)) + fib(2n+1)` — even-step
                      `= 2·fib(2n+1) + fib(2n)`.     — rearrange -/
theorem fib_odd_double_step (n : Nat) :
    fib (2 * n + 3) = 2 * fib (2 * n + 1) + fib (2 * n) := by
  have h1 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  have h2 : fib (2 * n + 2) = fib (2 * n + 1) + fib (2 * n) := rfl
  rw [h1, h2]
  -- (a + b) + a = 2a + b  where a = fib(2n+1), b = fib(2n)
  calc fib (2 * n + 1) + fib (2 * n) + fib (2 * n + 1)
      = fib (2 * n + 1) + fib (2 * n + 1) + fib (2 * n) := by
        rw [Nat.add_assoc, Nat.add_comm (fib (2 * n)) (fib (2 * n + 1)),
            ← Nat.add_assoc]
    _ = 2 * fib (2 * n + 1) + fib (2 * n) := by rw [← Nat.two_mul]

/-! ## §2 — Universal identity: Q00 n = fib(2n+1), Q01 n = fib(2n) -/

/-- ★★★★★★★★★★ **Universal P^n ↔ Fibonacci**: the matrix entry sequences
    `Q00, Q01` are exactly the Fibonacci sequence at even/odd indices.

    Proved by simultaneous induction using the double-step recurrences. -/
theorem Q00_eq_fib_odd_and_Q01_eq_fib_even :
    ∀ n : Nat, Q00 n = fib (2 * n + 1) ∧ Q01 n = fib (2 * n) := by
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨ih00, ih01⟩ := ih
    constructor
    · -- Goal: Q00 (k+1) = fib (2*(k+1) + 1) = fib (2k+3)
      show 2 * Q00 k + Q01 k = fib (2 * (k + 1) + 1)
      rw [ih00, ih01]
      have : 2 * (k + 1) + 1 = 2 * k + 3 := rfl
      rw [this]
      rw [← fib_odd_double_step k]
    · -- Goal: Q01 (k+1) = fib (2*(k+1)) = fib (2k+2)
      show Q00 k + Q01 k = fib (2 * (k + 1))
      rw [ih00, ih01]
      have : 2 * (k + 1) = 2 * k + 2 := rfl
      rw [this]
      rw [← fib_even_step k]

/-- ★★★★★★★★★★ **Q00 n = fib(2n+1)**: top-left entry of P^n is
    the Fibonacci number at odd index `2n+1`. -/
theorem Q00_eq_fib (n : Nat) : Q00 n = fib (2 * n + 1) :=
  (Q00_eq_fib_odd_and_Q01_eq_fib_even n).1

/-- ★★★★★★★★★★ **Q01 n = fib(2n)**: off-diagonal entry of P^n is
    the Fibonacci number at even index `2n`. -/
theorem Q01_eq_fib (n : Nat) : Q01 n = fib (2 * n) :=
  (Q00_eq_fib_odd_and_Q01_eq_fib_even n).2

/-- ★ **Q11 n = fib(2n−1)** for n ≥ 1: bottom-right entry equals
    Fibonacci at odd index `2(n-1)+1 = 2n−1`.  At n=0, Q11 0 = 1
    which corresponds to `fib(-1) = 1` by continuation. -/
theorem Q11_eq_fib_succ (n : Nat) : Q11 (n + 1) = fib (2 * n + 1) := by
  -- Q11 (n+1) = Q00 n by definition
  show Q00 n = fib (2 * n + 1)
  exact Q00_eq_fib n

/-! ## §3 — Capstone: master identity bundling all three entries -/

/-- ★★★★★★★★★★★★ **Universal P^n Fibonacci capstone**: for every n,
    P^n = [[fib(2n+1), fib(2n)], [fib(2n), fib(2n−1)]] where
    the bottom-right uses `Q11 (n+1) = fib(2n+1) = Q00 n`.

    This lifts `PnFibonacci`'s n=0..5 checks to ∀n. -/
theorem pn_fibonacci_universal (n : Nat) :
    Q00 n = fib (2 * n + 1)
    ∧ Q01 n = fib (2 * n)
    ∧ Q11 (n + 1) = fib (2 * n + 1) :=
  ⟨Q00_eq_fib n, Q01_eq_fib n, Q11_eq_fib_succ n⟩

/-! ## §4 — Trace = Lucas-Pell connection -/

/-- **Trace of P^n = fib(2n+1) + fib(2n−1)** for n ≥ 1.
    This is the Lucas-Pell trace `L(n) = trace(P^n)` expressed
    in pure Fibonacci terms. -/
theorem trace_pn_fib (n : Nat) :
    Q00 (n + 1) + Q11 (n + 1) = fib (2 * (n + 1) + 1) + fib (2 * n + 1) := by
  rw [Q00_eq_fib (n + 1), Q11_eq_fib_succ n]

end E213.Lib.Math.Mobius213.Px.QFibIdentity
