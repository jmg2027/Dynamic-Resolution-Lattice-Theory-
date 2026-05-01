import E213.Math.Pigeonhole

/-!
# Arity Forcing (general N): for any `k` and any base `Fin N` with
`N < k`, no Reachable relation term exists.

We parameterize `Raw` by both base size `N` and relation arity `k`,
and prove that whenever `N < k`, the step constructor can never fire
(every Reachable term reduces to a base object via pigeonhole).

This generalizes `E213.Firmware.Atomicity.ArityForcing` (which handled `N = 2, k = 3`)
to arbitrary `N, k` with `N < k`, using `E213.Math.Pigeonhole.no_inj_lt`.
-/

namespace E213.Firmware.Atomicity.ArityForcingGeneral
/-- Raw with base `Fin N` and relation arity `k` (encoded as functions
    `Fin k → RawNk`). -/
inductive RawNk (N k : Nat) where
  | object : Fin N → RawNk N k
  | rel    : (Fin k → RawNk N k) → RawNk N k

/-- Reachable: base + step with pairwise-distinct arguments. -/
inductive ReachableNk {N k : Nat} : RawNk N k → Prop where
  | base : (i : Fin N) → ReachableNk (RawNk.object i)
  | step : {f : Fin k → RawNk N k} →
           (∀ i, ReachableNk (f i)) →
           (∀ i j, i ≠ j → f i ≠ f j) →
           ReachableNk (RawNk.rel f)

/-- **Main vacuousness theorem.** If `N < k`, every Reachable term is
    a base object; no rel-term is Reachable. -/
theorem reachable_base_only {N k : Nat} (h : N < k) :
    ∀ {x : RawNk N k}, ReachableNk x → ∃ i : Fin N, x = .object i := by
  intro x hr
  induction hr with
  | base i => exact ⟨i, rfl⟩
  | @step f _ hne ih =>
      exfalso
      -- Each f i is a base object: f i = .object (g i) for some g i.
      let g : Fin k → Fin N := fun i => (ih i).choose
      have hg : ∀ i, f i = .object (g i) := fun i => (ih i).choose_spec
      -- g is injective (inherited from f).
      have g_inj : ∀ i j : Fin k, i ≠ j → g i ≠ g j := by
        intro i j hij heq
        apply hne i j hij
        rw [hg i, hg j, heq]
      -- Pigeonhole: N < k + g injective ⟹ False.
      exact E213.Math.Pigeonhole.no_inj_lt h g g_inj

/-- Corollary: no rel-term is ever Reachable when `N < k`. -/
theorem no_reachable_rel {N k : Nat} (h : N < k)
    (f : Fin k → RawNk N k) : ¬ ReachableNk (RawNk.rel f) := by
  intro hr
  obtain ⟨_, hi⟩ := reachable_base_only h hr
  cases hi

-- Summary: `(arity k, base Fin N)` is non-vacuous iff `N ≥ k`.
-- Combined with arity ≥ 2 (non-degenerate) and N minimal,
-- `(k = 2, N = 2)` is the unique minimal non-degenerate, non-vacuous
-- choice.

end E213.Firmware.Atomicity.ArityForcingGeneral