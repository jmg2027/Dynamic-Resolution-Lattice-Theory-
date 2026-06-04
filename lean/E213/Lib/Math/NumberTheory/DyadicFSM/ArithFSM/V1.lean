import E213.Lib.Math.NumberTheory.DyadicFSM.Product.LCMClosure

/-!
# ArithFSM₁ — 0-dimensional arithmetic FSM (single state Fin n)

The base case of the ArithFSM family.  Captures linear recurrences
on a 1-component state vector mod n, e.g. multiplication mod p:

  init = a
  step x = (m * x) mod n

Generates the trajectory a, m·a, m²·a, m³·a, ... mod n.

Key application: Legendre symbol via Euler's criterion.
  legendre(D, p) = D^((p-1)/2) mod p
is exactly the value of ArithFSM₁(p) at step (p-1)/2 with
init = 1, step = D·(–) mod p.

This is the "smallest 213-native trajectory" — Legendre symbol
becomes a member of the ArithFSM family rather than an external
number-theoretic fact.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1

/-- 1-state arithmetic FSM with state Fin n. -/
structure ArithFSM1 (n : Nat) where
  init : Fin n
  step : Fin n → Fin n
  out  : Fin n → Bool

/-- Run the FSM for k steps. -/
def ArithFSM1.run {n : Nat} (m : ArithFSM1 n) : Nat → Fin n
  | 0 => m.init
  | k + 1 => m.step (m.run k)

/-- Bit stream: out applied to run state. -/
def ArithFSM1.bits {n : Nat} (m : ArithFSM1 n) (k : Nat) : Bool :=
  m.out (m.run k)

end E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1
