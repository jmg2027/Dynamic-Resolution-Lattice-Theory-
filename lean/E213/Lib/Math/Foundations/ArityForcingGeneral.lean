import E213.Lib.Math.Combinatorics.Pigeonhole

/-!
# Arity Forcing (general N): for any `k` and any base `Fin N` with
`N < k`, no Reachable relation term exists.

We parameterize `Raw` by both base size `N` and relation arity `k`,
and prove that whenever `N < k`, the step constructor can never fire
(every Reachable term reduces to a base object via pigeonhole).

This generalizes `E213.Theory.Atomicity.ArityForcing` (which handled `N = 2, k = 3`)
to arbitrary `N, k` with `N < k`, using `E213.Lib.Math.Combinatorics.Pigeonhole.no_inj_lt`.

213-native (∅-axiom): the original used `(ih i).choose` which
pulls `Classical.choice`. Per `research-notes/G5_213_as_sublanguage.md`
§3, `Classical.choice` is a *theorem* in 213 for `Reachable` trajectories
— the witness is a structurally extracted `Fin N` index, not a
Hilbert-ε.  Here we replace `Exists.choose` by a `Bool`-guard
`isBase` + a constructive total function `getBase`.
-/

namespace E213.Lib.Math.Foundations.ArityForcingGeneral
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

/-- Bool-guard: `x` is an `.object` constructor.  Constructive
    replacement of the Prop-level `∃ i, x = .object i`. -/
def isBase {N k : Nat} : RawNk N k → Bool
  | .object _ => true
  | .rel _    => false

/-- Constructive index extraction.  `Classical.choice`-free analogue
    of `Exists.choose`: given `h : isBase x = true`, returns the
    `Fin N` witness by structural pattern match. -/
def getBase {N k : Nat} : (x : RawNk N k) → isBase x = true → Fin N
  | .object i, _ => i
  | .rel _,    h => by cases h

/-- The witness recovered by `getBase` indeed makes `x = .object _`. -/
theorem getBase_eq {N k : Nat} :
    ∀ (x : RawNk N k) (h : isBase x = true), x = .object (getBase x h)
  | .object _, _ => rfl
  | .rel _,    h => by cases h


/-- **Constructive core.**  ReachableNk x → isBase x = true.
    The step case discharges via pigeonhole; the witness `g i` is
    extracted by `getBase` (no `Classical.choice`). -/
theorem reachable_isBase {N k : Nat} (h : N < k) :
    ∀ {x : RawNk N k}, ReachableNk x → isBase x = true := by
  intro x hr
  induction hr with
  | base i => rfl
  | @step f _ hne ih =>
      exfalso
      let g : Fin k → Fin N := fun i => getBase (f i) (ih i)
      have hgeq : ∀ i, f i = .object (g i) :=
        fun i => getBase_eq (f i) (ih i)
      have g_inj : ∀ i j : Fin k, i ≠ j → g i ≠ g j := by
        intro i j hij heq
        apply hne i j hij
        rw [hgeq i, hgeq j, heq]
      exact E213.Lib.Math.Combinatorics.Pigeonhole.no_inj_lt h g g_inj

/-- **Main vacuousness theorem.** If `N < k`, every Reachable term is
    a base object; no rel-term is Reachable.  Recovered constructively
    from `reachable_isBase` + `getBase_eq` — no `Classical.choice`. -/
theorem reachable_base_only {N k : Nat} (h : N < k) :
    ∀ {x : RawNk N k}, ReachableNk x → ∃ i : Fin N, x = .object i := by
  intro x hr
  exact ⟨getBase x (reachable_isBase h hr), getBase_eq x _⟩

/-- Corollary: no rel-term is ever Reachable when `N < k`. -/
theorem no_reachable_rel {N k : Nat} (h : N < k)
    (f : Fin k → RawNk N k) : ¬ ReachableNk (RawNk.rel f) := by
  intro hr
  have hb : isBase (RawNk.rel f) = true := reachable_isBase h hr
  cases hb

-- Summary: `(arity k, base Fin N)` is non-vacuous iff `N ≥ k`.
-- Combined with arity ≥ 2 (non-degenerate) and N minimal,
-- `(k = 2, N = 2)` is the unique minimal non-degenerate, non-vacuous
-- choice.

end E213.Lib.Math.Foundations.ArityForcingGeneral