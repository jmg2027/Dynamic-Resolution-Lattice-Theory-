import E213.Term.Tactic.Nat213
open E213.Tactic.Nat213

/-!
# Arity Forcing: `k = 2` is the unique non-degenerate, non-vacuous choice

For a signature `{obj : Fin 2 → Raw_k, rel_k : Raw_k^k → Raw_k}` with
Reachable requiring pairwise-distinct arguments:

- `k = 0`: `rel` is a constant. No recursion (degenerate).
- `k = 1`: `rel` is unary, no distinctness constraint. Linear chain.
- `k ≥ 3`: `rel` needs `k` pairwise-distinct arguments, but the base
  `Fin 2` has only 2 distinct elements. The step rule **never fires**.
  No rel-term is ever Reachable (**vacuous**).
- `k = 2` (Clean213): unique value that is non-degenerate AND
  non-vacuous on `Fin 2`.

This file formalizes the `k = 3` vacuousness; the argument lifts
verbatim to any `k ≥ 3` by the same pigeonhole. Arity 0/1 degeneracy
is evident from the signatures themselves (no need for Lean proof).
-/

namespace E213.Theory.Atomicity.ArityForcing
/-- Arity-3 analog of `Raw`. -/
inductive Raw3 where
  | object : Fin 2 → Raw3
  | rel3   : Raw3 → Raw3 → Raw3 → Raw3
  deriving DecidableEq, Repr

/-- Reachable for arity-3 signature: requires pairwise distinct args. -/
inductive Reachable3 : Raw3 → Prop where
  | base : (i : Fin 2) → Reachable3 (.object i)
  | step : Reachable3 x → Reachable3 y → Reachable3 z →
           x ≠ y → y ≠ z → x ≠ z →
           Reachable3 (.rel3 x y z)

/-- **Vacuousness theorem.** With `Fin 2` base, every Reachable3 term
    is a base object. The step constructor can never fire because it
    demands 3 pairwise-distinct Reachable terms, and only `{object 0,
    object 1}` are ever produced. -/
theorem reachable3_only_object {x : Raw3} (h : Reachable3 x) :
    ∃ i : Fin 2, x = .object i := by
  induction h with
  | base i => exact ⟨i, rfl⟩
  | @step x y z _ _ _ hxy hyz hxz ihx ihy ihz =>
      obtain ⟨ix, rfl⟩ := ihx
      obtain ⟨iy, rfl⟩ := ihy
      obtain ⟨iz, rfl⟩ := ihz
      exfalso
      have hxy' : ix.val ≠ iy.val :=
        fun h => hxy (congrArg Raw3.object (Fin.ext h))
      have hyz' : iy.val ≠ iz.val :=
        fun h => hyz (congrArg Raw3.object (Fin.ext h))
      have hxz' : ix.val ≠ iz.val :=
        fun h => hxz (congrArg Raw3.object (Fin.ext h))
      -- Pigeonhole: three pairwise-distinct values, all < 2 → contradiction.
      match cases_lt_two ix.isLt, cases_lt_two iy.isLt, cases_lt_two iz.isLt with
      | Or.inl hx0, Or.inl hy0, _ => exact hxy' (hx0.trans hy0.symm)
      | Or.inr hx1, Or.inr hy1, _ => exact hxy' (hx1.trans hy1.symm)
      | _, Or.inl hy0, Or.inl hz0 => exact hyz' (hy0.trans hz0.symm)
      | _, Or.inr hy1, Or.inr hz1 => exact hyz' (hy1.trans hz1.symm)
      | Or.inl hx0, _, Or.inl hz0 => exact hxz' (hx0.trans hz0.symm)
      | Or.inr hx1, _, Or.inr hz1 => exact hxz' (hx1.trans hz1.symm)

/-- Corollary: no arity-3 relation term is ever Reachable3. -/
theorem no_reachable_rel3 (x y z : Raw3) : ¬ Reachable3 (.rel3 x y z) := by
  intro h
  obtain ⟨_, hi⟩ := reachable3_only_object h
  cases hi

-- Conclusion (informal): with `Fin 2` base, arity 2 is the unique
-- value of `k` that is both non-degenerate (arity 0, 1 produce no
-- tree structure) and non-vacuous (arity ≥ 3 produces no Reachable
-- relation at all).

end E213.Theory.Atomicity.ArityForcing