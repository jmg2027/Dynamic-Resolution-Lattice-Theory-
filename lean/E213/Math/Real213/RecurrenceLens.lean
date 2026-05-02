import E213.Math.Real213.CutExp

/-!
# Research.Real213RecurrenceLens: Recurrence Lens classification (F3)

Formal structure of the *generating Lens recurrence* for each real.

## Definition

```
structure RecurrenceLens (state : Type) where
  init : state
  transition : state → state
  output : state → Nat → Nat → Bool
```

State + transition + output = Lens recurrence specification.
-/

namespace E213.Math.Real213.RecurrenceLens

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)

/-- **RecurrenceLens**: state-bearing Lens for unfolding a real. -/
structure RecurrenceLens (state : Type) where
  init : state
  transition : state → state
  output : state → Nat → Nat → Bool

/-- Iterate transition n times. -/
def RecurrenceLens.unfoldState {state : Type}
    (rl : RecurrenceLens state) : Nat → state
  | 0 => rl.init
  | n+1 => rl.transition (rl.unfoldState n)

/-- Output cut at index n. -/
def RecurrenceLens.cutAt {state : Type}
    (rl : RecurrenceLens state) (n : Nat) : Nat → Nat → Bool :=
  rl.output (rl.unfoldState n)

end E213.Math.Real213.RecurrenceLens

namespace E213.Math.Real213.RecurrenceLens

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)

/-- **Constant Lens**: trivial recurrence (no state change).
    For rational reals.  state = Unit. -/
def constRecurrenceLens (c : Nat → Nat → Bool) : RecurrenceLens Unit where
  init := ()
  transition := id
  output := fun _ => c

/-- **e Lens**: factorial recurrence for e = Σ 1/i!.
    state = Nat (current degree). -/
def eRecurrenceLens : RecurrenceLens Nat where
  init := 0
  transition := fun n => n + 1
  output := fun n => expCutPartial (constCut 1 1) n

end E213.Math.Real213.RecurrenceLens
