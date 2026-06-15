import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# Fibonacci sum identities (∅-axiom)

Two genuine classical Fibonacci sum identities, both ABSENT from the corpus (no
`sumTo`-based Fibonacci sum identity existed; the Fibonacci infrastructure
carried Cassini / determinant identities but no partial-sum or square-sum):

  * **Partial-sum** `(Σ_{i=0}^{n} F_i) + 1 = F_{n+2}` (`sumFib_succ_one`) — the
    running total of Fibonacci numbers is one short of a later Fibonacci number
    (telescoping via the recurrence).
  * **Sum-of-squares** `Σ_{i=0}^{n} F_i² = F_n · F_{n+1}` (`sumFibSq_eq`) — the
    "Fibonacci rectangle" identity (the geometric φ-rectangle tiling).

Both stated additively (no Nat subtraction), by induction on the recurrence
`F_{n+2} = F_n + F_{n+1}`.  `sumTo` is the corpus FLT summation toolkit.

`fib` is a local two-step recurrence (matching the corpus convention — the math
corpus carries several module-local `fib` defs rather than a single canonical
one; consolidating them is a known organizational smell, deferred).  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.FibonacciSums

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)

/-- Standard Fibonacci: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- The recurrence, as a definitional equality. -/
theorem fib_rec (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-! ## Partial-sum identity: `(Σ_{i=0}^{n} F_i) + 1 = F_{n+2}` -/

/-- `sumFib n = F_0 + F_1 + ... + F_n` (inclusive upper bound `n`). -/
def sumFib (n : Nat) : Nat := sumTo (n + 1) fib

/-- ★ **Partial-sum identity** `(Σ_{i=0}^{n} F_i) + 1 = F_{n+2}`.

    Induction on `n`.  Step uses `F_{n+1} + F_{n+2} = F_{n+3}`. -/
theorem sumFib_succ_one (n : Nat) : sumFib n + 1 = fib (n + 2) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumTo (k + 2) fib + 1 = fib (k + 3)
    rw [sumTo_succ]
    have ih' : sumTo (k + 1) fib + 1 = fib (k + 2) := ih
    have hr : fib (k + 3) = fib (k + 1) + fib (k + 2) := rfl
    rw [hr, ← ih']
    ring_nat

/-! ## Sum of squares: `Σ_{i=0}^{n} F_i² = F_n · F_{n+1}` -/

/-- `sumFibSq n = F_0² + F_1² + ... + F_n²`. -/
def sumFibSq (n : Nat) : Nat := sumTo (n + 1) (fun i => fib i * fib i)

/-- ★ **Sum-of-squares identity** `Σ_{i=0}^{n} F_i² = F_n · F_{n+1}`.

    Induction on `n`.  Step:
    `S(n+1) = S n + F_{n+1}² = F_n·F_{n+1} + F_{n+1}² = F_{n+1}·(F_n + F_{n+1})
            = F_{n+1}·F_{n+2}`. -/
theorem sumFibSq_eq (n : Nat) : sumFibSq n = fib n * fib (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumTo (k + 2) (fun i => fib i * fib i) = fib (k + 1) * fib (k + 2)
    rw [sumTo_succ]
    have ih' : sumTo (k + 1) (fun i => fib i * fib i) = fib k * fib (k + 1) := ih
    have hr : fib (k + 2) = fib k + fib (k + 1) := rfl
    rw [ih', hr]
    ring_nat

/-! ## Smoke checks -/

theorem sumFib_smoke : sumFib 5 = 12 := by decide   -- 0+1+1+2+3+5 = 12 = F_7 - 1
theorem sumFibSq_smoke : sumFibSq 5 = 40 := by decide -- 0+1+1+4+9+25 = 40 = F_5·F_6 = 5·8

end E213.Lib.Math.Combinatorics.FibonacciSums
