import E213.Lib.Math.Combinatorics.SpernerChains

/-!
# The LYM inequality (∅-axiom) — the per-term refinement Sperner discards

**The named theorem (L3).**  The Lubell–Yamamoto–Meshalkin inequality
(`Bollobás`–LYM): for *every* antichain `F` of the Boolean lattice `2^[n]`,

  `Σ_{A ∈ F}  1 / C(n, |A|)  ≤  1`.

Cleared of denominators (multiply by `n!`, using `C(n,k)·k!·(n−k)! = n!`,
`Sperner.binom_mul_fact`) this is the **division-free integer form**

  `Σ_{A ∈ F}  |A|! · (n − |A|)!  ≤  n!`  — `lym_antichain`.

**Why it is its own theorem, not a step inside Sperner.**  The Sperner
development (`Sperner.sperner_upper_bound`, `SpernerChains.sperner`) immediately
collapses each summand to its minimum `(⌊n/2⌋)!·(⌈n/2⌉)!` (via
`Sperner.fact_mul_ge_mid`) and reads off `|F| ≤ C(n,⌊n/2⌋)`.  That throws away
the per-term structure.  LYM keeps it: it is the statement *before* the
minimum is taken, and it is strictly stronger — Sperner is the one-line
corollary `sperner_via_lym` (replace each term by the minimum, then cancel).

**The compilation (`seed/PROOF_ISA.md`).**  LYM is exactly the
double-counting / dual-union-bound face of `COUNT`, already built abstractly as
`Sperner.lym_double_count` (each maximal chain meets the antichain ≤ once, so
the chains-through-`A` total over `F` is ≤ the chain total `n!`).  This file
does no new counting — it instantiates that engine over the *same* geometric
chain model as `SpernerChains` (`chain_cap` = `hcap`, `chain_low` = `hlow`) and
*stops before the minimum*, exposing the named inequality and its tightness.

## What is closed (∅-axiom)

  · `lym_inequality` — the **engine form**: over any chain model with the two
    counts (`chains.length = n!`, `≥ |A|!·(n−|A|)!` chains through each `A`,
    ≤ 1 member per chain), `Σ_{A∈F} |A|!·(n−|A|)! ≤ n!`.
  · `lym_antichain` — the **named bound**, unconditional: every antichain of
    `2^[n]` satisfies `Σ_{A∈F} |A|!·(n−|A|)! ≤ n!` (= `Σ 1/C(n,|A|) ≤ 1`).
  · `lym_tight_layer` — **tightness / the equality case**: a single full layer
    `kLayer n k` (`k ≤ n`) *saturates* LYM, `Σ = n!`.  So the inequality is
    sharp, and the extremal antichains are exactly the layers.
  · `sperner_via_lym` — **LYM ⟹ Sperner**: bound each term below by the middle
    `(⌊n/2⌋)!·(⌈n/2⌉)!`, cancel, recover `|F| ≤ C(n,⌊n/2⌋)`.

Companion essay: `theory/essays/proof_isa/lym_inequality.md`.
-/

namespace E213.Lib.Math.Combinatorics.LymInequality

open E213.Lib.Math.Combinatorics.Sperner
open E213.Lib.Math.Combinatorics.SpernerChains
open E213.Lib.Math.Combinatorics.Permutations (fact perms)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Tactic.List213 (mem_filter)

/-! ## §1 — the engine form

No new counting: `Sperner.lym_double_count` gives the column read
`Σ_{A∈F} (#chains through A) ≤ #chains`; the row read `#chains through A ≥
|A|!·(n−|A|)!` (the chain model's `hlow`) turns the left side into the LYM sum.
Where `Sperner.sperner_count_bound` next replaces every term by its minimum,
this stops one step earlier — that is the whole difference. -/

/-- ★ **LYM, engine form.**  Under the chain-model hypotheses — `#chains = n!`,
    each chain incident to ≤ 1 antichain member (`hcap`), ≥ `|A|!·(n−|A|)!`
    chains through each member (`hlow`) — the LYM sum is bounded by `n!`:

      `Σ_{A∈F}  |A|! · (n − |A|)!  ≤  n!`.

    Abstract and ∅-axiom; the geometric model discharges the hypotheses in
    `lym_antichain`. -/
theorem lym_inequality {γ : Type _} (n : Nat)
    (F : List (List Bool)) (chains : List γ) (inc : List Bool → γ → Bool)
    (hchains : chains.length = fact n)
    (hcap : ∀ c, c ∈ chains → lcount (fun A => inc A c) F ≤ 1)
    (hlow : ∀ A, A ∈ F → fact (cardB A) * fact (n - cardB A) ≤ lcount (inc A) chains) :
    sumOver (fun A => fact (cardB A) * fact (n - cardB A)) F ≤ fact n := by
  have hlym := lym_double_count F chains inc hcap
  rw [hchains] at hlym
  exact Nat.le_trans (sumOver_le (fun A hA => hlow A hA)) hlym

/-! ## §2 — the named bound (unconditional)

Instantiate `lym_inequality` with the geometric chain model of `SpernerChains`
— maximal chains as orderings of `[n]` (`perms (idxList n)`), `inc` = prefix-set
— whose two hypotheses are already discharged there (`chain_cap`, `chain_low`). -/

/-- ★★ **The LYM inequality (named, division-free).**  Every antichain `F` of
    the Boolean lattice `2^[n]` (duplicate-free, length-`n` members, no two
    comparable) satisfies

      `Σ_{A∈F}  |A|! · (n − |A|)!  ≤  n!`.

    This is `Σ_{A∈F} 1/C(n,|A|) ≤ 1` cleared of denominators
    (`C(n,k)·k!·(n−k)! = n!`, `Sperner.binom_mul_fact`).  ∅-axiom: the chain
    model supplies `chains_length` (= `n!`), `chain_cap`, `chain_low`. -/
theorem lym_antichain {n : Nat} (F : List (List Bool))
    (hF : IsAntichain F) (hnd : F.Nodup) (hlen : ∀ A, A ∈ F → A.length = n) :
    sumOver (fun A => fact (cardB A) * fact (n - cardB A)) F ≤ fact n :=
  lym_inequality n F (perms (idxList n)) (inc n)
    (chains_length n)
    (chain_cap F hF hnd)
    (fun A hA => chain_low A (hlen A hA))

/-! ## §3 — tightness: a full layer saturates LYM

LYM is sharp.  A single size-`k` layer `kLayer n k` (`k ≤ n`) is an antichain
(`Sperner.kLayer_isAntichain`) whose LYM sum is *exactly* `n!`: every member has
`|A| = k`, contributing `k!·(n−k)!`, and there are `C(n,k)` of them
(`Sperner.kLayer_card`), so the sum is `C(n,k)·k!·(n−k)! = n!`
(`Sperner.binom_mul_fact`).  Hence the layers are the extremal antichains:
they are exactly the ones meeting the bound. -/

/-- ★ **Tightness / equality case.**  A full layer saturates LYM: for `k ≤ n`,

      `Σ_{A ∈ kLayer n k}  |A|! · (n − |A|)!  =  n!`.

    So `lym_antichain` is sharp, and the layers are the extremal antichains. -/
theorem lym_tight_layer {n k : Nat} (hk : k ≤ n) :
    sumOver (fun A => fact (cardB A) * fact (n - cardB A)) (kLayer n k) = fact n := by
  have hterm : ∀ A, A ∈ kLayer n k →
      fact (cardB A) * fact (n - cardB A) = fact k * fact (n - k) := by
    intro A hA
    have hc : cardB A = k := Nat.eq_of_beq_eq_true (mem_filter hA).2
    rw [hc]
  rw [sumOver_congr hterm, sumOver_const, kLayer_card, Nat.mul_comm]
  exact binom_mul_fact n k hk

/-! ## §4 — LYM ⟹ Sperner

The corollary that makes "LYM is strictly stronger" precise: replace each LYM
term by its minimum `(⌊n/2⌋)!·(⌈n/2⌉)!` (the factorial product is minimised at
the middle, `Sperner.fact_mul_ge_mid`), pull the constant out as
`|F|·(min term)`, and cancel it against `C(n,⌊n/2⌋)·(min term) = n!`
(`Sperner.binom_mul_fact`).  This re-derives `SpernerChains.sperner` *through*
the named inequality, witnessing LYM ⊃ Sperner. -/

/-- ★ **Sperner via LYM.**  Bounding each LYM term below by the middle value
    `(⌊n/2⌋)!·(⌈n/2⌉)!` and cancelling recovers Sperner's bound
    `|F| ≤ C(n, ⌊n/2⌋)` — the named inequality is strictly stronger than the
    extremal *number* it implies. -/
theorem sperner_via_lym {n : Nat} (F : List (List Bool))
    (hF : IsAntichain F) (hnd : F.Nodup) (hlen : ∀ A, A ∈ F → A.length = n) :
    F.length ≤ binom n (half n) := by
  have hlym := lym_antichain F hF hnd hlen
  have hcard : ∀ A, A ∈ F → cardB A ≤ n :=
    fun A hA => Nat.le_trans (cardB_le_length A) (Nat.le_of_eq (hlen A hA))
  have hstep : F.length * (fact (half n) * fact (n - half n)) ≤ fact n := by
    calc F.length * (fact (half n) * fact (n - half n))
        = sumOver (fun _ => fact (half n) * fact (n - half n)) F := by
            rw [sumOver_const]; exact Nat.mul_comm _ _
      _ ≤ sumOver (fun A => fact (cardB A) * fact (n - cardB A)) F :=
            sumOver_le (fun A hA => fact_mul_ge_mid (hcard A hA))
      _ ≤ fact n := hlym
  have hfn := binom_mul_fact n (half n) (half_le_self n)
  rw [← hfn, Nat.mul_comm F.length (fact (half n) * fact (n - half n)),
      Nat.mul_comm (binom n (half n)) (fact (half n) * fact (n - half n))] at hstep
  exact Nat.le_of_mul_le_mul_left hstep
    (Nat.mul_pos (fact_pos (half n)) (fact_pos (n - half n)))

/-! ## §5 — confirmation

The tight layers at small `n`: each saturates LYM at `n!`.  `n = 3, k = 1`:
three singletons, each `1!·2! = 2`, sum `6 = 3!`.  `n = 4, k = 2`: six pairs,
each `2!·2! = 4`, sum `24 = 4!`. -/

/-- LYM saturation at `(n,k) = (3,1)` and `(4,2)`. -/
theorem lym_tight_examples :
    sumOver (fun A => fact (cardB A) * fact (3 - cardB A)) (kLayer 3 1) = 6
    ∧ sumOver (fun A => fact (cardB A) * fact (4 - cardB A)) (kLayer 4 2) = 24 :=
  ⟨lym_tight_layer (by decide), lym_tight_layer (by decide)⟩

end E213.Lib.Math.Combinatorics.LymInequality
