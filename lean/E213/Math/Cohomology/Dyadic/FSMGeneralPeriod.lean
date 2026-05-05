import E213.Math.Cohomology.Dyadic.ArithFSM
import E213.Math.Cohomology.Dyadic.ArithFSM.V3

import E213.Math.Cohomology.Dyadic.ArithFSM.Mod5
/-!
# General FSM period theorem — A task (Pisano predictor reframe)

Replaces per-prime induction proofs with a SINGLE general theorem.

## The pattern

Every per-prime Pisano theorem in the codebase follows this template:

```
theorem pellFSMmodP_run_period_N :
    ∀ k, pellFSMmodP.run (k + N) = pellFSMmodP.run k := by
  intro k
  induction k with
  | zero => decide  -- proves run N = init via N-step compute
  | succ k' ih =>
    show pellFSMmodP.step (pellFSMmodP.run (k' + N))
        = pellFSMmodP.step (pellFSMmodP.run k')
    rw [ih]
```

Two parts:
  1. base case: `run N = init` (decidable for specific N)
  2. step: `step (run (k+N)) = step (run k)` (immediate from IH)

This file abstracts (2) into a UNIVERSAL theorem.

## What's proved

  ArithFSM2.run_period_of_init : ∀ m N,
    m.run N = m.init → ∀ k, m.run (k + N) = m.run k

  ArithFSM2.bits_period_of_init : same for bits

  ArithFSM3.run_period_of_init : same for cubic-class

Each per-prime instance now reduces to a SINGLE decide:
  `m.run N = m.init` (computable in N steps).

This replaces ~30 induction proofs across the Pisano-CRT framework
with ONE general theorem + 30 decide instances.
-/

namespace E213.Math.Cohomology.Dyadic.FSMGeneralPeriod

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)
open E213.Math.Cohomology.Dyadic.ArithFSM.V3 (ArithFSM3)
open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5)


/-- ★★★★★★★ General FSM period theorem (ArithFSM2):
    if running for N steps returns to init, then bits cycle with period N.

    Proof avoids omega — uses Nat.succ_add directly for STRICT 0-AXIOM. -/
theorem ArithFSM2.run_period_of_init {n : Nat} (m : ArithFSM2 n) (N : Nat)
    (h : m.run N = m.init) :
    ∀ k, m.run (k + N) = m.run k := by
  intro k
  induction k with
  | zero =>
    show m.run (0 + N) = m.run 0
    rw [Nat.zero_add]; exact h
  | succ k' ih =>
    show m.run (k' + 1 + N) = m.run (k' + 1)
    rw [Nat.succ_add k' N]
    show m.step (m.run (k' + N)) = m.step (m.run k')
    rw [ih]

/-- ★★★★★★★ General FSM bits period theorem.
    Direct corollary of run_period_of_init. -/
theorem ArithFSM2.bits_period_of_init {n : Nat} (m : ArithFSM2 n) (N : Nat)
    (h : m.run N = m.init) :
    ∀ k, m.bits (k + N) = m.bits k := by
  intro k
  show m.out (m.run (k + N)) = m.out (m.run k)
  rw [m.run_period_of_init N h]

/-- ★★★★★★★ General FSM3 (cubic-class) period theorem.
    Same pattern as ArithFSM2. -/
theorem ArithFSM3.run_period_of_init {n : Nat} (m : ArithFSM3 n) (N : Nat)
    (h : m.run N = m.init) :
    ∀ k, m.run (k + N) = m.run k := by
  intro k
  induction k with
  | zero =>
    show m.run (0 + N) = m.run 0
    rw [Nat.zero_add]; exact h
  | succ k' ih =>
    show m.run (k' + 1 + N) = m.run (k' + 1)
    rw [Nat.succ_add k' N]
    show m.step (m.run (k' + N)) = m.step (m.run k')
    rw [ih]

theorem ArithFSM3.bits_period_of_init {n : Nat} (m : ArithFSM3 n) (N : Nat)
    (h : m.run N = m.init) :
    ∀ k, m.bits (k + N) = m.bits k := by
  intro k
  show m.out (m.run (k + N)) = m.out (m.run k)
  rw [m.run_period_of_init N h]

/-! ### Demo — instant period proofs via the general theorem -/

/-- Pell mod 3 period 4 — derived in ONE LINE via general theorem. -/
example : ∀ k, pellFSMmod3.run (k + 4) = pellFSMmod3.run k :=
  pellFSMmod3.run_period_of_init 4 (by decide)

/-- Pell mod 5 period 10 — ONE LINE. -/
example : ∀ k, pellFSMmod5.run (k + 10) = pellFSMmod5.run k :=
  pellFSMmod5.run_period_of_init 10 (by decide)

/-- Tribonacci mod 2 period 4 — ONE LINE. -/
example : ∀ k, tribFSMmod2.run (k + 4) = tribFSMmod2.run k :=
  tribFSMmod2.run_period_of_init 4 (by decide)

end E213.Math.Cohomology.Dyadic.FSMGeneralPeriod
