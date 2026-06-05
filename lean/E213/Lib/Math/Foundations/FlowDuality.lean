import E213.Lib.Math.Foundations.MonovariantFlow

/-!
# LOOP ⟷ FLOW, witnessed: ascent and descent are one principle by order-reversal

`MonovariantFlow.flow_reaches` is the **FLOW** archetype: a self-map with a
`Nat`-monovariant that strictly **descends** off fixed points reaches a normal
form (settle *down* — the ν / greatest-fixed-point direction).  Its **dual** is
the **LOOP**-shaped build-*up*: a measure that strictly **ascends** but is
**bounded above** also reaches a fixed point (the µ / least-fixed-point
direction, capped).

The two are the *same* well-founded principle on `ℕ`, mirrored by the
order-reversal `μ ↦ B − μ`: ascent of `μ` under a cap `B` is descent of `B − μ`.
This file proves the ascending dual *by reducing it to* `flow_reaches` through
that reflection — the LOOP ⟷ FLOW duality made into a theorem
(`theory/essays/proof_isa/lift_archetypes_order_and_duality.md`).
-/

namespace E213.Lib.Math.Foundations.FlowDuality

open E213.Lib.Math.Foundations.MonovariantFlow (IsNormalForm flow_reaches iter)

/-- `a < b ≤ B ⟹ B − b < B − a` (∅-axiom; `Nat.sub_lt_sub_left` carries
    `propext`).  The order-reversal step: subtracting more leaves strictly less. -/
private theorem sub_lt_sub_left_pure :
    ∀ (B a b : Nat), a < b → b ≤ B → B - b < B - a
  | 0, _, _, hab, hbB => absurd (Nat.lt_of_lt_of_le hab hbB) (Nat.not_lt_zero _)
  | B + 1, 0, b, _, hbB => by
      -- (B+1) - b < (B+1) - 0 = B+1, since b ≥ 1
      match b, hbB with
      | b' + 1, hbB =>
          have : B + 1 - (b' + 1) ≤ B := by
            rw [Nat.succ_sub_succ_eq_sub]; exact Nat.sub_le B b'
          exact Nat.lt_succ_of_le this
  | B + 1, a' + 1, b, hab, hbB => by
      match b, hab, hbB with
      | b' + 1, hab, hbB =>
          rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
          exact sub_lt_sub_left_pure B a' b'
            (Nat.lt_of_succ_lt_succ hab) (Nat.le_of_succ_le_succ hbB)

/-- ★★★★★ **The ascending dual of FLOW (LOOP direction)**: a self-map with a
    `Nat`-measure that strictly **ascends** off fixed points and is **bounded
    above** by `B` reaches a normal form.  Proved by reflecting to `flow_reaches`
    with the reversed measure `B − μ` — descent of the mirror *is* ascent of the
    original.  LOOP (build up to a cap) and FLOW (settle down) are one well-
    founded principle. -/
theorem flow_reaches_ascending {X : Type _} (f : X → X) (μ : X → Nat) (B : Nat)
    (hbound : ∀ x, μ x ≤ B)
    (ascent : ∀ x, μ x < μ (f x) ∨ f x = x) (x : X) :
    ∃ n, IsNormalForm f (iter f n x) := by
  refine flow_reaches f (fun y => B - μ y) (fun y => ?_) x
  cases ascent y with
  | inr h => exact Or.inr h
  | inl h => exact Or.inl (sub_lt_sub_left_pure B (μ y) (μ (f y)) h (hbound (f y)))

end E213.Lib.Math.Foundations.FlowDuality
