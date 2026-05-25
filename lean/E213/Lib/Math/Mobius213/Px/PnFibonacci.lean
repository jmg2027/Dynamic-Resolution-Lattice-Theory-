import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Math.Mobius213.Px.POrbitClosure
import E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock

/-!
# Mobius213.Px.PnFibonacci — P^n entries are consecutive Fibonacci

`FibonacciAtomicLock.lean` proves `P = Q²` where Q is the Fibonacci
shift matrix.  This file extends the connection: every power `P^n`
of P has entries that are consecutive Fibonacci numbers at even
indices.

## Statement

For every `n : Nat`, the matrix `P^n` has the form

  `P^n = [[fib(2n+1), fib(2n)], [fib(2n), fib(2n−1)]]`

(with `fib(−1) := 1` by Fibonacci continuation; we handle the
base case `n = 0` separately to avoid negative indices).

## Consequences

  · `trace(P^n) = fib(2n+1) + fib(2n−1) = L(n)` — the Lucas-Pell
    trace orbit IS the bisected sum of consecutive Fibonacci.
  · `det(P^n) = fib(2n+1) · fib(2n−1) − fib(2n)² = (−1)^(2n−1) = −1`?
    Wait: standard Fibonacci Cassini gives `fib(n−1)·fib(n+1) −
    fib(n)² = (−1)^n`.  At index `2n`: `fib(2n−1)·fib(2n+1) −
    fib(2n)² = (−1)^(2n) = 1 = det(P)^n`.  ✓

So both the trace orbit (Lucas-Pell L) and the determinant
invariant (= 1) of P^n are encoded entirely in Fibonacci data.

## Finite catalog

We verify `P^n` matrix entries against `fib` formulas for
`n ∈ {0, 1, 2, 3, 4, 5}` via `decide`.  Universal claim deferred
to narrative tier (requires matrix-induction with Int polynomial
manipulation).

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.PnFibonacci

open E213.Lib.Physics.Simplex.Counts (NS NT d)
open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)

/-! ## §1 — P^n matrix entries (computed) -/

/-- Explicit P^n matrix entries via Pell-Lucas recurrence on
    individual entries.

    `P^n_{0,0}` (top-left): satisfies the same recurrence as P
    iterated; concretely a, b, c, d entries of P^n form four
    interlocking Pell-Lucas-like sequences. -/
def P00 : Nat → Nat
  | 0     => 1
  | 1     => 2
  | n + 2 => 3 * P00 (n + 1) - P00 n

/-- Top-right entry of P^n. -/
def P01 : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => 3 * P01 (n + 1) - P01 n

/-- Bottom-right entry of P^n. -/
def P11 : Nat → Nat
  | 0     => 1
  | 1     => 1
  | n + 2 => 3 * P11 (n + 1) - P11 n

/-! ## §2 — P^n top-left entry = fib(2n+1) -/

theorem P00_0 : P00 0 = fib 1 := by decide
theorem P00_1 : P00 1 = fib 3 := by decide
theorem P00_2 : P00 2 = fib 5 := by decide
theorem P00_3 : P00 3 = fib 7 := by decide
theorem P00_4 : P00 4 = fib 9 := by decide
theorem P00_5 : P00 5 = fib 11 := by decide

/-! ## §3 — P^n off-diagonal entry = fib(2n) -/

theorem P01_0 : P01 0 = fib 0 := by decide
theorem P01_1 : P01 1 = fib 2 := by decide
theorem P01_2 : P01 2 = fib 4 := by decide
theorem P01_3 : P01 3 = fib 6 := by decide
theorem P01_4 : P01 4 = fib 8 := by decide
theorem P01_5 : P01 5 = fib 10 := by decide

/-! ## §4 — P^n bottom-right entry = fib(2n−1) (with fib(−1) := 1) -/

theorem P11_0 : P11 0 = 1 := by decide  -- fib(-1) := 1 convention
theorem P11_1 : P11 1 = fib 1 := by decide
theorem P11_2 : P11 2 = fib 3 := by decide
theorem P11_3 : P11 3 = fib 5 := by decide
theorem P11_4 : P11 4 = fib 7 := by decide
theorem P11_5 : P11 5 = fib 9 := by decide

/-! ## §5 — Trace = L (Lucas-Pell) = fib(2n+1) + fib(2n−1) -/

/-- `trace(P^0) = P00(0) + P11(0) = 1 + 1 = 2 = L(0)`. -/
theorem trace_0 : P00 0 + P11 0 = (L 0).toNat := by decide

/-- `trace(P^1) = P00(1) + P11(1) = 2 + 1 = 3 = L(1)`. -/
theorem trace_1 : P00 1 + P11 1 = (L 1).toNat := by decide

/-- `trace(P^2) = 5 + 2 = 7 = L(2)`. -/
theorem trace_2 : P00 2 + P11 2 = (L 2).toNat := by decide

/-- `trace(P^3) = 13 + 5 = 18 = L(3)`. -/
theorem trace_3 : P00 3 + P11 3 = (L 3).toNat := by decide

/-- `trace(P^4) = 34 + 13 = 47 = L(4)`. -/
theorem trace_4 : P00 4 + P11 4 = (L 4).toNat := by decide

/-- `trace(P^5) = 89 + 34 = 123 = L(5)`. -/
theorem trace_5 : P00 5 + P11 5 = (L 5).toNat := by decide

/-! ## §6 — Determinant = 1 (Cassini at Fibonacci level) -/

/-- ★★ `det(P^n) = P00(n) · P11(n) − P01(n)² = 1` at n = 0..5.

    This is the standard Fibonacci Cassini identity `fib(n−1) ·
    fib(n+1) − fib(n)² = (−1)^n` specialized to even indices
    `2n`: `(−1)^(2n) = 1 = det(P)^n`. -/
theorem det_Pn_0 : P00 0 * P11 0 - (P01 0)^2 = 1 := by decide
theorem det_Pn_1 : P00 1 * P11 1 - (P01 1)^2 = 1 := by decide
theorem det_Pn_2 : P00 2 * P11 2 - (P01 2)^2 = 1 := by decide
theorem det_Pn_3 : P00 3 * P11 3 - (P01 3)^2 = 1 := by decide
theorem det_Pn_4 : P00 4 * P11 4 - (P01 4)^2 = 1 := by decide
theorem det_Pn_5 : P00 5 * P11 5 - (P01 5)^2 = 1 := by decide

/-! ## §7 — Master: P^n ↔ Fibonacci bridge -/

/-- ★★★★★★★★★ **P^n Fibonacci bridge master**: the matrix
    `P^n` has entries that are consecutive Fibonacci numbers at
    even-index positions (with `fib(−1) := 1` continuation at
    `P11(0)`).  Verified for `n = 0..5` via `decide`.

    For each `n`:

      `P^n = [[fib(2n+1), fib(2n)], [fib(2n), fib(2n−1)]]`

    Consequences (also verified n = 0..5):

      · `trace(P^n) = fib(2n+1) + fib(2n−1) = L(n)`
      · `det(P^n)   = fib(2n+1) · fib(2n−1) − fib(2n)² = 1`

    The first is the Lucas-Pell ↔ Fibonacci bisection identity.
    The second is the Fibonacci Cassini identity at even indices,
    coinciding with `det(P)^n = 1^n = 1`.

    **Structural reading**: every algebraic invariant of P-iteration
    (trace orbit, determinant) is encoded entirely in Fibonacci
    data via bisection.  This sharpens the `P = Q²` lemma of
    `FibonacciAtomicLock`: P-iteration is *all* of Fibonacci at
    even indices. -/
theorem pn_fibonacci_master :
    -- Top-left = fib(2n+1) at n = 0..5
    P00 0 = fib 1 ∧ P00 1 = fib 3 ∧ P00 2 = fib 5
    ∧ P00 3 = fib 7 ∧ P00 4 = fib 9 ∧ P00 5 = fib 11
    -- Off-diagonal = fib(2n) at n = 0..5
    ∧ P01 0 = fib 0 ∧ P01 1 = fib 2 ∧ P01 2 = fib 4
    ∧ P01 3 = fib 6 ∧ P01 4 = fib 8 ∧ P01 5 = fib 10
    -- Trace = L (Lucas-Pell) at n = 0..5
    ∧ P00 0 + P11 0 = (L 0).toNat
    ∧ P00 1 + P11 1 = (L 1).toNat
    ∧ P00 2 + P11 2 = (L 2).toNat
    ∧ P00 3 + P11 3 = (L 3).toNat
    ∧ P00 4 + P11 4 = (L 4).toNat
    ∧ P00 5 + P11 5 = (L 5).toNat
    -- Det = 1 at n = 0..5 (Fibonacci Cassini at even index)
    ∧ P00 0 * P11 0 - (P01 0)^2 = 1
    ∧ P00 1 * P11 1 - (P01 1)^2 = 1
    ∧ P00 2 * P11 2 - (P01 2)^2 = 1
    ∧ P00 3 * P11 3 - (P01 3)^2 = 1
    ∧ P00 4 * P11 4 - (P01 4)^2 = 1
    ∧ P00 5 * P11 5 - (P01 5)^2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Lib.Math.Mobius213.Px.PnFibonacci
