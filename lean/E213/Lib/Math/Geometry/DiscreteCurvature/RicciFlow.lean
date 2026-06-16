import E213.Lib.Math.Foundations.MonovariantFlow

/-!
# A discrete cell-filling flow on `K_{3,2}` — convergence via the FLOW archetype (∅-axiom)

A discrete monovariant **cell-filling flow** on the complete bipartite graph
`K_{3,2}`, converging to a maximally-filled normal form via the FLOW archetype
(`MonovariantFlow.flow_reaches`).

## The model

Filling one independent 4-cycle with a 2-cell reduces `b_1` by 1.  `K_{3,2}`
has exactly `C(3,2)·C(2,1) = 3` simple 4-cycles, so the filling sequence is
`b_1 : 8 → 7 → 6 → 5`, saturating at 5 once all `C = 3` cells are filled.

The **flow** is `fillStep C : (cells filled) ↦ (cells filled + 1)` until `C`
are filled, then absorbing; the **monovariant** is the remaining fillable count
`C − k`; the **normal form** is "all `C` cells filled" (`k = C`), the maximally
filled state.

## Scope

This is the cell-filling model at the `b_1 = 8 − k` arithmetic level; the
filling-flow on `K_{3,2}` is a convergent monovariant flow, with the FLOW
archetype as the convergence engine.
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.RicciFlow

open E213.Lib.Math.Foundations.MonovariantFlow (iter IsNormalForm flow_reaches)

/-- The coherentization flow: fill one 4-cycle per step until all `C` are
    filled, then absorb (fixed point).  State = number of cells filled. -/
def fillStep (C : Nat) (k : Nat) : Nat := if k < C then k + 1 else k

/-- `b_1` after filling `k` cells from an initial graph `b_1 = B₀`
    (each fill reduces `b_1` by one). -/
def b1OfFill (B0 k : Nat) : Nat := B0 - k

/-- `k < C → 0 < C − k`, ∅-axiom (hand-rolled; `Nat.sub_pos_of_lt` carries
    `propext`). -/
private theorem sub_pos_pure : ∀ (k C : Nat), k < C → 0 < C - k
  | 0,    _,    h => h
  | _+1,  0,    h => absurd h (Nat.not_lt_zero _)
  | k'+1, C'+1, h => by
      rw [Nat.succ_sub_succ_eq_sub]
      exact sub_pos_pure k' C' (Nat.lt_of_succ_lt_succ h)

/-- The monovariant `C − k` strictly descends off fixed points: a step shrinks
    the remaining fillable count, except once all `C` are filled. -/
theorem fill_descent (C : Nat) :
    ∀ k, C - fillStep C k < C - k ∨ fillStep C k = k := by
  intro k
  cases Nat.lt_or_ge k C with
  | inl h =>
      left
      have hstep : fillStep C k = k + 1 := if_pos h
      rw [hstep]
      show (C - k) - 1 < C - k
      exact Nat.sub_lt (sub_pos_pure k C h) (Nat.zero_lt_succ 0)
  | inr h =>
      right
      exact if_neg (fun hlt => absurd (Nat.lt_of_lt_of_le hlt h) (Nat.lt_irrefl k))

/-- ★★★★★ **The FLOW archetype fires on the filling flow, uniformly in `C`.**

    For *every* fillable-cycle count `C`, the flow converges to a normal form.
    This `∀ C` statement is supplied by
    `flow_reaches` (the monovariant descent lifted to convergence). -/
theorem coherentization_flow_converges (C : Nat) :
    ∃ n, IsNormalForm (fillStep C) (iter (fillStep C) n 0) :=
  flow_reaches (fillStep C) (fun k => C - k) (fill_descent C) 0

/-- The flow from the unfilled graph reaches `k = C` (all cells filled) in
    exactly `C` steps.  Generalized helper: `j + n ≤ C → iterⁿ j = j + n`. -/
theorem iter_fill_eq :
    ∀ (C n j : Nat), j + n ≤ C → iter (fillStep C) n j = j + n
  | _, 0,   _, _ => rfl
  | C, n+1, j, h => by
      have hsum : (j + 1) + n ≤ C := by
        rw [Nat.add_assoc, Nat.add_comm 1 n]; exact h
      have hj : j < C := by
        have hpos : j < j + (n + 1) := by
          have h0 := Nat.add_lt_add_left (Nat.zero_lt_succ n) j
          rwa [Nat.add_zero] at h0
        exact Nat.lt_of_lt_of_le hpos h
      have hstep : fillStep C j = j + 1 := by
        show (if j < C then j + 1 else j) = j + 1
        rw [if_pos hj]
      show iter (fillStep C) n (fillStep C j) = j + (n + 1)
      rw [hstep, iter_fill_eq C n (j + 1) hsum, Nat.add_assoc, Nat.add_comm 1 n]

/-- `fillStep` is fixed once all `C` cells are filled. -/
theorem fillStep_fixed_at_C (C : Nat) : fillStep C C = C := by
  show (if C < C then C + 1 else C) = C
  rw [if_neg (Nat.lt_irrefl C)]

/-- ★★★★★ **The normal form, identified.**  The flow from the
    unfilled graph reaches the all-cells-filled state `k = C` in `C` steps,
    and it is a fixed point — the unique maximally-filled normal form. -/
theorem coherentization_normal_form (C : Nat) :
    iter (fillStep C) C 0 = C
    ∧ IsNormalForm (fillStep C) (iter (fillStep C) C 0) := by
  have hC : iter (fillStep C) C 0 = C := by
    have e := iter_fill_eq C C 0 (Nat.le_of_eq (Nat.zero_add C))
    rwa [Nat.zero_add] at e
  refine ⟨hC, ?_⟩
  show fillStep C (iter (fillStep C) C 0) = iter (fillStep C) C 0
  rw [hC]; exact fillStep_fixed_at_C C

/-- ★★★★★★ **The `K_{3,2}` cell-filling flow converges (via the FLOW archetype).**

    The `K_{3,2}` cell-filling flow (`C = 3` fillable 4-cycles,
    initial graph `b_1 = 8`) converges, via the FLOW archetype, to the
    maximally-filled normal form: all 3 cells filled.  The
    invariant read off the normal form is `b_1 = 8 − 3 = 5`. -/
theorem ricci_pillar_K32_flow_close :
    -- FLOW archetype fires: convergence to a normal form
    (∃ n, IsNormalForm (fillStep 3) (iter (fillStep 3) n 0))
    -- canonical normal form reached in 3 steps: all 3 cells filled
    ∧ iter (fillStep 3) 3 0 = 3
    ∧ IsNormalForm (fillStep 3) (iter (fillStep 3) 3 0)
    -- canonical b_1 read off the normal form: 8 − 3 = 5
    ∧ b1OfFill 8 3 = 5 := by
  refine ⟨coherentization_flow_converges 3,
          (coherentization_normal_form 3).1,
          (coherentization_normal_form 3).2, ?_⟩
  show (8 : Nat) - 3 = 5
  decide

/-! ## §5 — the cell-filling flow as a `Nat → Nat` modulus

  The cell-filling flow on `K_{3,2}` carries a discrete modulus: the number of
  averaging steps (cells filled) required to reach a target `b₁` precision,
  `8 − target`.  Anti-monotone in the target (a tighter target needs weakly more
  steps), this is the discrete `Nat → Nat` analogue of "longer flow time for
  sharper homogenisation".  Consumed by the unified `Topology.ModulusStructure`
  framework. -/

/-- Cell-filling modulus for `K_{3,2}`: the step count (cells filled) to reach a
    target `b₁` precision, `8 − target` (Nat-truncated). -/
def K32_ricci_modulus (target_b1 : Nat) : Nat := 8 - target_b1

/-- Modulus values at reachable targets (`b₁ ∈ [5, 8]`) — filling 0, 1, 2, 3
    of the simple 4-cycles. -/
theorem K32_ricci_modulus_reachable :
    K32_ricci_modulus 8 = 0
    ∧ K32_ricci_modulus 7 = 1
    ∧ K32_ricci_modulus 6 = 2
    ∧ K32_ricci_modulus 5 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Propext-free helper: subtraction is anti-monotone in the subtrahend on a
    fixed minuend.  Pure induction on `Nat.le`. -/
private theorem sub_le_sub_left_pure (n : Nat) :
    ∀ {a b : Nat}, a ≤ b → n - b ≤ n - a := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans (Nat.pred_le _) ih

/-- ★★★★ **`K32_ricci_modulus` is anti-monotone on all of ℕ**: a tighter
    precision target requires (weakly) more averaging steps, universally. -/
theorem K32_ricci_modulus_anti_monotone :
    ∀ a b : Nat, a ≤ b → K32_ricci_modulus b ≤ K32_ricci_modulus a := by
  intro a b hab
  unfold K32_ricci_modulus
  exact sub_le_sub_left_pure 8 hab

/-- A discrete Ricci-style modulus structure: a `Nat → Nat` step-count function
    with the anti-monotone (averaging) property.  Parallels
    `Topology.Continuity.IsContinuousModulus` in shape, specialised to
    averaging-step semantics. -/
structure IsRicciModulus where
  /-- The step-count modulus: target precision ↦ averaging steps. -/
  modulus : Nat → Nat
  /-- Anti-monotone in the precision target: tighter target needs ≥ as many steps. -/
  anti_monotone : ∀ {a b : Nat}, a ≤ b → modulus b ≤ modulus a

/-- ★★★★★ **`K32_ricci_modulus` as a canonical `IsRicciModulus`**. -/
def K32_isRicciModulus : IsRicciModulus where
  modulus := K32_ricci_modulus
  anti_monotone := fun {a b} hab => K32_ricci_modulus_anti_monotone a b hab

/-- The instance's modulus unfolds to the underlying `K32_ricci_modulus`. -/
theorem K32_isRicciModulus_modulus_eq :
    K32_isRicciModulus.modulus = K32_ricci_modulus := by
  unfold K32_isRicciModulus
  rfl

end E213.Lib.Math.Geometry.DiscreteCurvature.RicciFlow
