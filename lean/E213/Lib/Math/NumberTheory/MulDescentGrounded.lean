import E213.Lib.Math.NumberTheory.MulDescentRec
import E213.Lib.Math.Foundations.IsPartGroundedInduction

/-!
# FTA existence with its descent grounded in the distinguishing (`isPart_wf`) — ∅-axiom

The descent leg's bar: a deep multiplicative discipline
must terminate via **`Raw`'s own descent** `isPart_wf`, not borrowed `Nat.strongRecOn`.  The current
`MulDescentRec.mul_factorization_exists` fails it — a direct closure walk shows `Nat.strongRecOn` in
its cone (from `mulDescentRec`'s `Ω`-recursion).

This file rebuilds factorisation existence with the **descent** re-routed through
`Foundations.IsPartGroundedInduction.measureInduction_grounded` (whose well-founded engine is the
distinguishing's descent — verified clean on its own: `isPart_wf` present, `Nat.lt_wfRel`/
`Nat.strongRecOn` absent).  The peel `n ↦ n / minFac n` strictly decreases `n`, so the `id`-measure
descends.

**The accounting (measured by direct kernel-closure walk + `#print axioms`).**  The closure of
`mul_factorization_exists_grounded` is:

  * `isPart_wf` — **present** (absent from the old `mul_factorization_exists`): the factorisation
    descent terminates on `Raw`'s descent;
  * `Nat.strongRecOn` — **absent** (the bar's target): no non-structural well-founded recursion on
    `Nat`.  Cleared in two moves — (i) this file's descent uses `measureInduction_grounded` not
    `mulDescentRec`; (ii) `AddMod213.div_add_mod` was rebuilt on structural fuel (it was the single
    point keeping `strongRecOn` in the whole `minFac`/`leastFactorFrom` chain), and `Nat.div_lt_self`
    / `Nat.mul_div_cancel'` (both `strongRecOn`/`propext`-laden in core) were replaced by `div_lt_self'`
    and a `div_add_mod`+`mod_zero_of_dvd` cancellation;
  * `Nat.lt_wfRel` — **present**, isolated to `Nat.div`/`Nat.mod` (kernel WF-recursion) — a separate
    borrowed arithmetic primitive (the deep carrier-rebuild, `the_genesis_seam.md`).

And `#print axioms` is empty — **∅-axiom** (no `propext`).

**Status.**  The descent leg's bar — *factorisation terminates via `Raw`'s own descent, not borrowed
`Nat.strongRecOn`* — is **cleared for FTA existence**: `isPart_wf` in, `Nat.strongRecOn` out,
∅-axiom.  This is precisely what `the_genesis_seam.md` found FTA-over-`Nat213` *failing*.  The only
residual borrowing is `Nat.div`'s internal `lt_wfRel` (division as a primitive), cleanly named — the
next, separate frontier.
-/

namespace E213.Lib.Math.NumberTheory.MulDescentGrounded

open E213.Lib.Math.NumberTheory.PrimeFactorization
  (prodL minFac minFac_spec minFac_prime)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.Valuation (mod_zero_of_dvd)
open E213.Lib.Math.Foundations.IsPartGroundedInduction (measureInduction_grounded)

/-- `n / m < n` for `0 < n`, `2 ≤ m` — proved from the (now `strongRecOn`-free) `div_add_mod`, so it
    does **not** pull `Nat.strongRecOn` (unlike core `Nat.div_lt_self`). -/
private theorem div_lt_self' {n m : Nat} (hn : 0 < n) (hm : 2 ≤ m) : n / m < n := by
  rcases Nat.lt_or_ge (n / m) n with h | h
  · exact h
  · exfalso
    have key : m * (n / m) + n % m = n := E213.Meta.Nat.AddMod213.div_add_mod n m
    have hmq_le : m * (n / m) ≤ n :=
      Nat.le_trans (Nat.le_add_right (m * (n / m)) (n % m)) (Nat.le_of_eq key)
    have hstep : 2 * n ≤ m * (n / m) := Nat.mul_le_mul hm h
    have hstep' : n + n ≤ m * (n / m) :=
      Nat.le_trans (Nat.le_of_eq (Nat.two_mul n).symm) hstep
    exact Nat.lt_irrefl n
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hn) (Nat.le_trans hstep' hmq_le))

/-- ★★★ **Factorisation existence, descent grounded in `isPart_wf` — the descent-leg bar cleared for
    FTA.**  Every `n ≥ 1` is a product of primes, by `measureInduction_grounded` on the `id`-measure
    (the peel `n ↦ n / minFac n` strictly decreases `n`).  Verified by direct closure walk:
    `isPart_wf` **present**, `Nat.strongRecOn` **absent** — the factorisation recursion terminates on
    the distinguishing's own descent, not borrowed `Nat` well-foundedness; and `#print axioms` is
    empty (∅-axiom, no `propext`).  Residual `Nat.lt_wfRel` is isolated to `Nat.div` (file header).
    This is the result `the_genesis_seam.md` found FTA-over-`Nat213` *failing*. -/
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
    have hmpos : 0 < minFac n := Nat.lt_of_lt_of_le (by decide) hge
    -- propext-free `minFac n * (n / minFac n) = n`, from div_add_mod + mod_zero_of_dvd
    have hcancel : minFac n * (n / minFac n) = n := by
      have hmod0 : n % minFac n = 0 := mod_zero_of_dvd hmpos hdvd
      have hkey : minFac n * (n / minFac n) + n % minFac n = n :=
        E213.Meta.Nat.AddMod213.div_add_mod n (minFac n)
      exact ((Nat.add_zero (minFac n * (n / minFac n))).symm.trans
        (congrArg (fun z => minFac n * (n / minFac n) + z) hmod0.symm)).trans hkey
    have hquot_lt : n / minFac n < n := div_lt_self' hpos hge
    have hquot_pos : 1 ≤ n / minFac n := by
      rcases Nat.eq_zero_or_pos (n / minFac n) with h0 | h0
      · exfalso
        have hz : n = 0 :=
          ((hcancel.symm.trans (congrArg (minFac n * ·) h0)).trans (Nat.mul_zero (minFac n)))
        exact Nat.lt_irrefl 0 (hz ▸ hpos)
      · exact h0
    obtain ⟨L', hL'prime, hL'prod⟩ := ih (n / minFac n) hquot_lt hquot_pos
    refine ⟨minFac n :: L', ?_, ?_⟩
    · intro p hp
      cases hp with
      | head => exact minFac_prime h2
      | tail _ h => exact hL'prime p h
    · show minFac n * prodL L' = n
      exact (congrArg (minFac n * ·) hL'prod).trans hcancel

end E213.Lib.Math.NumberTheory.MulDescentGrounded
