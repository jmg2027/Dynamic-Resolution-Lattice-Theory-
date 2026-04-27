import E213.Firmware.Raw

/-!
# Research.ComplexityClass: Lens-algorithm complexity class (D2 partial)

`research/notes/D2_complexity_class_hierarchy.md` 의 Tier 1 (FSM)
의 partial Lean formalization.

## Tier 1 의 형식 정의

`HasFiniteStateMachine xs` = sequence xs : Nat → Raw 가 *유한
state machine* 의 unfolding 으 로 표현 가능.

- `bound` = state space size - 1 (Fin (bound + 1) 사용).
- `state k` = sequence 의 k-th index 의 state.
- `transition` = 고정 transition function.
- `output` = state → Raw output.
- `state_step` + `output_correct` = state machine 의 정확 한 unfolding.

## 의의

3-tier hierarchy (D2) 의 Tier 1 entry point:

- Tier 1 (FSM): `HasFiniteStateMachine xs` 의 instance 존재.
- Tier 2 (ICT): `HasModulus xs` 이지만 FSM instance 부재 — negative
  존재 statement, framework 안 직접 형식 화 어 려 움.
- Tier 3: framework 외부.

이 파일 은 typeclass + 1 trivial instance (constant sequence).
Pell / Sqrt2 sequence 의 FSM instance 는 별 도 작업 (cyclic mod-N
state).
-/

namespace E213.Research.ComplexityClass

open E213.Firmware

/-- **Tier 1 (FSM)**: sequence 가 finite state machine 으 로 표현. -/
class HasFiniteStateMachine (xs : Nat → Raw) where
  bound : Nat
  state : Nat → Fin (bound + 1)
  transition : Fin (bound + 1) → Fin (bound + 1)
  state_step : ∀ k, state (k + 1) = transition (state k)
  output : Fin (bound + 1) → Raw
  output_correct : ∀ k, xs k = output (state k)

end E213.Research.ComplexityClass

namespace E213.Research.ComplexityClass

open E213.Firmware

/-! ### Trivial instance: constant sequence -/

/-- Constant sequence xs k = r. -/
def constSeq (r : Raw) : Nat → Raw := fun _ => r

/-- Constant sequence 가 1-state FSM. -/
instance constSeq_FSM (r : Raw) : HasFiniteStateMachine (constSeq r) where
  bound := 0
  state := fun _ => ⟨0, Nat.zero_lt_succ _⟩
  transition := fun s => s
  state_step := fun _ => rfl
  output := fun _ => r
  output_correct := fun _ => rfl

end E213.Research.ComplexityClass

namespace E213.Research.ComplexityClass

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

/-- Alternating sequence 가 2-state FSM. -/
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

end E213.Research.ComplexityClass
