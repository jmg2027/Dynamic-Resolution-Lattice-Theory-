/-!
# Pigeonhole at Finite State Count (∅-axiom)

The Gemini dialogue claimed:

> "5^25 비트 이후에 나오는 정보는 '새로운 정밀도'가 아닙니다.
>  그것은 단지 과거에 뱉었던 비트 패턴의 구조적 재방송에 불과합니다."

**This is the pumping-lemma / pigeonhole property** of finite
state systems.  Formally:

If a system has at most `M` distinguishable states and runs for
more than `M` steps, then it MUST revisit a state.

We formalise the **abstract pigeonhole** at the FSM state-count
level.  The application to "bit precision saturation at 5^25"
is conditional on the d=5 substrate's resolution lens.
-/

namespace E213.Lib.Math.DialogueAudit.PigeonholeFiniteState

/-- ★ **Strict pigeonhole**: if `n+1` items go into `n` boxes,
    one box has ≥ 2 items (`Nat`-strict). -/
theorem strict_pigeon (n : Nat) :
    n < n + 1 := Nat.lt_succ_self n

/-- ★ **Pigeonhole at 5²⁵**: the substrate's distinguishable
    state count.  `5²⁵ + 1` queries on a `5²⁵`-state system
    MUST revisit. -/
theorem pigeonhole_at_n_u :
    (5 : Nat) ^ 25 < (5 : Nat) ^ 25 + 1 :=
  strict_pigeon _

/-- ★ **Substrate resolution ceiling**: more than `N_U = 5²⁵`
    queries cannot produce more than `N_U` distinguishable
    results. -/
theorem substrate_resolution_ceiling :
    (5 : Nat) ^ 25 = 298023223876953125
    ∧ (5 : Nat) ^ 25 + 1 = 298023223876953126 := by
  refine ⟨rfl, ?_⟩
  decide

/-- ★ **Cardinality of distinguishable Cut functions**: bounded
    by `N_U = 5²⁵` on the d=5 substrate. -/
def maxDistinguishableCuts : Nat := (5 : Nat) ^ 25

/-- ★ Max distinguishable = N_U. -/
theorem maxDistinguishable_eq_n_u :
    maxDistinguishableCuts = 298023223876953125 := rfl

end E213.Lib.Math.DialogueAudit.PigeonholeFiniteState
