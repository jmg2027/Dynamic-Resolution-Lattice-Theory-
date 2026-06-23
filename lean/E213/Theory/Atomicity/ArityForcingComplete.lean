import E213.Lib.Math.Foundations.ArityForcingGeneral

/-!
# Arity Forcing — lower half: `k = 2` characterized, not asserted

`ArityForcing.lean` and `ArityForcingGeneral.lean` prove the **upper**
half of the arity forcing — that arity `k ≥ 3` is *vacuous* over a base
of size `< k` (the pigeonhole `no_reachable_rel`). The **lower** half —
that arity `0` and `1` are *degenerate* and that the minimal base size is
`2` — was, until now, left as a code comment ("evident from the
signatures themselves... no need for Lean proof",
`ArityForcing.lean` §, and `ArityForcingGeneral.lean` summary). An
adversarial audit flagged this as the framework's most load-bearing
unproven step: the whole "`(N_S, N_T, d) = (3, 2, 5)` is *forced*, with
no exterior dialer" claim rests on arity-2 / base-2 being derived rather
than chosen.

This file closes the lower half on the existing parametric type
`RawNk N k` / `ReachableNk` (`ArityForcingGeneral`), ∅-axiom.

## What is forced, stated honestly

The relation arity `k = 2` is the unique value that is simultaneously:

* **a genuine distinction** — its step relates two *distinct* argument
  positions: `GenuineDistinction k ↔ 2 ≤ k` (`exists_distinct_iff_two_le`).
  Below `k = 2` there are no two distinct `Fin k` indices, so the step's
  pairwise-distinctness hypothesis is *vacuous* — the "relation" never
  relates two distinct things (`all_eq_of_le_one`). That is what arity-0
  and arity-1 *degeneracy* means, now a theorem, not a comment;
* **non-vacuous on the minimal 2-element base** — some relation term is
  actually `ReachableNk`: `NonvacuousOnBase2 k ↔ k ≤ 2` (the `≥ 3` side is
  `no_reachable_rel`; the `≤ 2` side is exhibited at `k = 2` by
  `arity_two_nonvacuous`).

Their conjunction holds **iff `k = 2`** (`arity_two_forced`).

What remains an *input* (named, not hidden): that the step *requires*
pairwise-distinct arguments at all. But that requirement **is clause 4**
(no self-pairing, `x / x` undefined — `02_axiom.md` §2.2 clause 4). So
arity-2 is not a free choice: it reduces to {clause 4, minimal
distinguishing base}. The base size `2` is forced the same way
(`exists_distinct_iff_two_le` read on `N`): a base admits a distinction
iff it has `≥ 2` elements, and `2` is minimal.
-/

namespace E213.Theory.Atomicity.ArityForcingComplete

open E213.Lib.Math.Foundations.ArityForcingGeneral

/-! ## §1 — The distinction-count lemma (`∅`-axiom, hand-rolled) -/

/-- `n < 1 → n = 0`, structural (core `Nat.lt_one_iff` leaks `propext`). -/
private theorem eq_zero_of_lt_one {n : Nat} (h : n < 1) : n = 0 := by
  match n with
  | 0     => rfl
  | (m+1) => exact absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero m)

/-- **The distinction lemma.** A `Fin n` admits two distinct elements iff
    `n ≥ 2`. Read on the relation arity it is "genuine distinction";
    read on the base size it is "the base can distinguish." -/
theorem exists_distinct_iff_two_le (n : Nat) :
    (∃ i j : Fin n, i ≠ j) ↔ 2 ≤ n := by
  constructor
  · rintro ⟨i, j, hij⟩
    match n with
    | 0     => exact absurd i.isLt (Nat.not_lt_zero _)
    | 1     =>
        exact absurd
          (Fin.ext ((eq_zero_of_lt_one i.isLt).trans (eq_zero_of_lt_one j.isLt).symm))
          hij
    | (m+2) => exact Nat.le_add_left 2 m
  · intro h
    exact ⟨⟨0, Nat.lt_of_lt_of_le (by decide) h⟩,
           ⟨1, Nat.lt_of_lt_of_le (by decide) h⟩,
           fun he => Nat.zero_ne_one (congrArg Fin.val he)⟩

/-- **Degeneracy at `k ≤ 1`.** When the arity (or base) is `≤ 1`, *every*
    pair of indices is equal — so the step's pairwise-distinctness
    requirement is vacuously satisfiable and relates nothing distinct.
    This is the formal content of "arity 0/1 is degenerate." -/
theorem all_eq_of_le_one {k : Nat} (h : k ≤ 1) (i j : Fin k) : i = j :=
  Fin.ext ((eq_zero_of_lt_one (Nat.lt_of_lt_of_le i.isLt h)).trans
           (eq_zero_of_lt_one (Nat.lt_of_lt_of_le j.isLt h)).symm)

/-! ## §2 — Non-vacuity at arity 2, base 2 -/

/-- **Non-vacuity witness.** At arity `2` over the `Fin 2` base, the step
    *fires*: `rel (object 0, object 1)` is `ReachableNk` (the two base
    objects are distinct, satisfying clause 4). So arity 2 is non-vacuous
    on the minimal base — the converse direction to `no_reachable_rel`. -/
theorem arity_two_nonvacuous :
    ReachableNk (N := 2) (k := 2) (RawNk.rel (fun i => RawNk.object i)) :=
  ReachableNk.step (fun i => ReachableNk.base i)
    (fun _ _ hij h => hij (RawNk.object.inj h))

/-! ## §3 — The forcing capstone -/

/-- The relation relates two distinct positions (genuine distinction). -/
def GenuineDistinction (k : Nat) : Prop := ∃ i j : Fin k, i ≠ j

/-- Some relation term is actually reachable on the 2-element base. -/
def NonvacuousOnBase2 (k : Nat) : Prop :=
  ∃ f : Fin k → RawNk 2 k, ReachableNk (RawNk.rel f)

/-- ★★★★★ **ARITY-2 CHARACTERIZATION (given the clause-4 distinctness
    gate).** The relation arity `k = 2` is the *unique* value that is both a
    genuine distinction (`2 ≤ k`) and non-vacuous on the minimal 2-element
    base (`k ≤ 2`). This converts the previously *comment-only* lower half
    of the arity argument ("arity 0/1 degeneracy is evident, no Lean proof")
    into a ∅-axiom theorem, and — crucially — names the one remaining
    *input* sharply rather than burying it: the result is a characterization
    **relative to the distinctness gate** `i ≠ j → f i ≠ f j` built into
    `ReachableNk.step`. That gate **is** clause 4 (no self-pairing); this
    theorem does **not** prove the gate itself is forced — it shows that,
    *given* clause 4, arity 2 is the unique non-degenerate non-vacuous arity
    on the minimal base. Honest scope: a typed-conditional characterization,
    not an unconditional "arity 2 forced, full stop." -/
theorem arity_two_forced (k : Nat) :
    (GenuineDistinction k ∧ NonvacuousOnBase2 k) ↔ k = 2 := by
  constructor
  · rintro ⟨hgen, f, hf⟩
    have h2le : 2 ≤ k := (exists_distinct_iff_two_le k).mp hgen
    have hk2 : k ≤ 2 :=
      match Nat.lt_or_ge 2 k with
      | Or.inl hlt => absurd hf (no_reachable_rel hlt f)
      | Or.inr hge => hge
    exact Nat.le_antisymm hk2 h2le
  · intro hk
    subst hk
    refine ⟨(exists_distinct_iff_two_le 2).mpr (by decide), ?_⟩
    exact ⟨fun i => RawNk.object i, arity_two_nonvacuous⟩

/-- The base size `2` is forced the same way: a base admits a distinction
    iff it has `≥ 2` elements, and `2` is minimal. -/
theorem base_two_minimal :
    (∀ N, (∃ i j : Fin N, i ≠ j) → 2 ≤ N) ∧ (∃ i j : Fin 2, i ≠ j) :=
  ⟨fun N h => (exists_distinct_iff_two_le N).mp h,
   (exists_distinct_iff_two_le 2).mpr (by decide)⟩

end E213.Theory.Atomicity.ArityForcingComplete
