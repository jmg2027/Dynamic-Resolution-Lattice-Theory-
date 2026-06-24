import E213.Lib.Math.NumberTheory.MulDescentRec
import E213.Lib.Math.Foundations.IsPartGroundedInduction

/-!
# FTA existence with its descent grounded in the distinguishing (`isPart_wf`) — ∅-axiom

The descent leg's bar (`research-notes/frontiers/the_descent_leg.md`): a deep multiplicative discipline
must terminate via **`Raw`'s own descent** `isPart_wf`, not borrowed `Nat.strongRecOn`.  The current
`MulDescentRec.mul_factorization_exists` fails it — a direct closure walk shows `Nat.strongRecOn` in
its cone (from `mulDescentRec`'s `Ω`-recursion).

This file rebuilds factorisation existence with the **descent** re-routed through
`Foundations.IsPartGroundedInduction.measureInduction_grounded` (whose well-founded engine is the
distinguishing's descent — verified clean on its own: `isPart_wf` present, `Nat.lt_wfRel`/
`Nat.strongRecOn` absent).  The peel `n ↦ n / minFac n` strictly decreases `n`, so the `id`-measure
descends.

**The honest accounting (measured by direct kernel-closure walk — NOT the hoped-for clean result).**
After the rebuild the closure of `mul_factorization_exists_grounded` is:

  * `isPart_wf` — **now present** (it was *absent* from the old `mul_factorization_exists`): the
    factorisation **descent** now terminates on `Raw`'s descent.  Real, measured progress.
  * `Nat.strongRecOn` — **still present** (closure walk: `true`).  *The descent no longer introduces
    it, but a reused supporting lemma does* — traced precisely to `minFac_spec` →
    `leastFactorFrom_spec` (the correctness proof of the least-factor search uses strong recursion).
    So swapping the descent was necessary but **not sufficient**: the `minFac` *specification chain*
    must also be rebuilt on structural-fuel induction before the bar is cleared.
  * `Nat.lt_wfRel` — present, from `Nat.div`/`Nat.mod` (kernel WF-recursion) — a separate borrowed
    arithmetic primitive (the deep carrier-rebuild, `the_genesis_seam.md`).

**Status (honest).**  The descent leg's bar is **not yet cleared for FTA** — `Nat.strongRecOn`
survives via `leastFactorFrom_spec`.  What *is* achieved: the reusable engine is clean and verified
(`IsPartGroundedInduction`), the factorisation descent is grounded (`isPart_wf` enters the cone), and
the **remaining blocker is named and isolated** (`leastFactorFrom_spec`).  That precise accounting —
which lemma carries the borrowing, and what must be rebuilt next — is the deliverable, exactly the
"measured claim, win or lose" the frontier note calls for.  ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.MulDescentGrounded

open E213.Lib.Math.NumberTheory.PrimeFactorization
  (prodL minFac minFac_spec minFac_prime)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.Foundations.IsPartGroundedInduction (measureInduction_grounded)

/-- ★★★ **Factorisation existence, descent re-routed through `isPart_wf`.**  Every `n ≥ 1` is a
    product of primes — proved by `measureInduction_grounded` on the `id`-measure (the peel
    `n ↦ n / minFac n` strictly decreases `n`).  The factorisation **descent** now terminates on the
    distinguishing's descent `isPart_wf` (it enters the cone, where the old proof had none).  *Honest
    measurement*: `Nat.strongRecOn` nonetheless **survives** via the reused `minFac_spec` →
    `leastFactorFrom_spec` — so this grounds the descent but does **not** yet clear the FTA bar; the
    `minFac` specification chain is the named remaining blocker (file header).  ∅-axiom. -/
theorem mul_factorization_exists_grounded :
    ∀ n, 1 ≤ n → ∃ L : List Nat, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n := by
  refine measureInduction_grounded (fun n => n)
    (P := fun n => 1 ≤ n → ∃ L : List Nat, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n) ?_
  intro n ih hn
  rcases Nat.lt_or_ge n 2 with hlt | h2
  · -- n = 1: the empty product
    have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hn
    subst hn1
    exact ⟨[], fun p hp => absurd hp (List.not_mem_nil p), rfl⟩
  · -- n ≥ 2: peel the least prime factor
    obtain ⟨hge, hdvd, hle, _⟩ := minFac_spec h2
    have hpos : 0 < n := Nat.lt_of_lt_of_le (by decide) h2
    have hquot_lt : n / minFac n < n := Nat.div_lt_self hpos hge
    have hquot_pos : 1 ≤ n / minFac n := by
      rcases Nat.eq_zero_or_pos (n / minFac n) with h0 | h0
      · exfalso
        have hc : minFac n * (n / minFac n) = n := Nat.mul_div_cancel' hdvd
        have hz : n = 0 :=
          ((hc.symm.trans (congrArg (minFac n * ·) h0)).trans (Nat.mul_zero (minFac n)))
        exact Nat.lt_irrefl 0 (hz ▸ hpos)
      · exact h0
    obtain ⟨L', hL'prime, hL'prod⟩ := ih (n / minFac n) hquot_lt hquot_pos
    refine ⟨minFac n :: L', ?_, ?_⟩
    · intro p hp
      cases hp with
      | head => exact minFac_prime h2
      | tail _ h => exact hL'prime p h
    · show minFac n * prodL L' = n
      exact (congrArg (minFac n * ·) hL'prod).trans (Nat.mul_div_cancel' hdvd)

end E213.Lib.Math.NumberTheory.MulDescentGrounded
