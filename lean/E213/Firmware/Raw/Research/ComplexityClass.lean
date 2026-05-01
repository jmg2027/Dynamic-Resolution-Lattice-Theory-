import E213.Firmware.Raw

/-!
# Research.ComplexityClass: Lens-algorithm complexity class (D2 partial)

Partial Lean formalization of Tier 1 (FSM) from
`research/notes/D2_complexity_class_hierarchy.md`.

## Formal definition of Tier 1

`HasFiniteStateMachine xs` = the sequence xs : Nat → Raw can be
expressed as the unfolding of a *finite state machine*.

- `bound` = state space size - 1 (using Fin (bound + 1)).
- `state k` = state at the k-th index of the sequence.
- `transition` = fixed transition function.
- `output` = state → Raw output.
- `state_step` + `output_correct` = exact unfolding of the state machine.

## Significance

Tier 1 entry point of the 3-tier hierarchy (D2):

- Tier 1 (FSM): an instance of `HasFiniteStateMachine xs` exists.
- Tier 2 (ICT): `HasModulus xs` holds but no FSM instance — a
  negative existence statement, hard to formalize directly in the framework.
- Tier 3: outside the framework.

This file contains the typeclass + 1 trivial instance (constant sequence).
FSM instances for Pell / Sqrt2 sequences are separate work (cyclic mod-N
state).
-/

namespace E213.Firmware.Raw.Research.ComplexityClass

open E213.Firmware

/-- **Tier 1 (FSM)**: sequence expressible as a finite state machine. -/
class HasFiniteStateMachine (xs : Nat → Raw) where
  bound : Nat
  state : Nat → Fin (bound + 1)
  transition : Fin (bound + 1) → Fin (bound + 1)
  state_step : ∀ k, state (k + 1) = transition (state k)
  output : Fin (bound + 1) → Raw
  output_correct : ∀ k, xs k = output (state k)

end E213.Firmware.Raw.Research.ComplexityClass

namespace E213.Firmware.Raw.Research.ComplexityClass

open E213.Firmware

/-! ### Trivial instance: constant sequence -/

/-- Constant sequence xs k = r. -/
def constSeq (r : Raw) : Nat → Raw := fun _ => r

/-- Constant sequence is a 1-state FSM. -/
instance constSeq_FSM (r : Raw) : HasFiniteStateMachine (constSeq r) where
  bound := 0
  state := fun _ => ⟨0, Nat.zero_lt_succ _⟩
  transition := fun s => s
  state_step := fun _ => rfl
  output := fun _ => r
  output_correct := fun _ => rfl

end E213.Firmware.Raw.Research.ComplexityClass

namespace E213.Firmware.Raw.Research.ComplexityClass

open E213.Firmware

/-! ### Non-trivial instance: 2-state alternating sequence -/

/-- Alternating Bool state — true, false, true, false, .... -/
def altState : Nat → Bool
  | 0 => true
  | n + 1 => !altState n

/-- Alternating Raw sequence: a, b, a, b, .... -/
def altSeq (n : Nat) : Raw := if altState n then Raw.a else Raw.b

/-- Bool → Fin 2 (pattern match for definitional unfolding). -/
def boolToFin2 : Bool → Fin 2
  | true => ⟨0, Nat.zero_lt_succ _⟩
  | false => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩

/-- Fin 2 → Bool (pattern match). -/
def fin2ToBool : Fin 2 → Bool
  | ⟨0, _⟩ => true
  | _ => false

/-- Fin 2 → Raw via pattern match. -/
def fin2ToRaw : Fin 2 → Raw
  | ⟨0, _⟩ => Raw.a
  | _ => Raw.b

/-- Alternating sequence is a 2-state FSM. -/
instance altSeq_FSM : HasFiniteStateMachine altSeq where
  bound := 1
  state := fun k => boolToFin2 (altState k)
  transition := fun s => boolToFin2 (!fin2ToBool s)
  state_step := by
    intro k
    show boolToFin2 (altState (k + 1)) = boolToFin2 (!fin2ToBool (boolToFin2 (altState k)))
    show boolToFin2 (!altState k) = boolToFin2 (!fin2ToBool (boolToFin2 (altState k)))
    cases altState k <;> rfl
  output := fin2ToRaw
  output_correct := by
    intro k
    show altSeq k = fin2ToRaw (boolToFin2 (altState k))
    unfold altSeq
    cases altState k <;> rfl

end E213.Firmware.Raw.Research.ComplexityClass
