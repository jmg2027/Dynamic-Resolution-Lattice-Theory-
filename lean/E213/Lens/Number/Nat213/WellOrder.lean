import E213.Lens.Number.Nat213.Factorization

/-!
# Lens.Number.Nat213.WellOrder — strong induction + well-ordering over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, leg-2 — `Nat213`'s well-foundedness exposed as a reusable named API.
`Factorization.wf_lt : WellFounded lt` (proved by structural `acc_lt`, no `Nat` measure) is the
foundation the discipline's well-founded recursions descend on; here it is packaged:

- **`strong_induction`** — the ergonomic named form of `wf_lt.induction`: to prove `C n` it suffices
  to prove it for `n` given `C` on every strictly smaller element.
- **`well_ordering`** — every inhabited **decidable** predicate has a `lt`-minimal witness.  (The
  general-`Prop` well-ordering needs excluded middle; the decidable form is constructive, decided by
  `Factorization.decBoundedExists` at each descent step — ∅-axiom, no `Classical`.)

This is the order-theoretic capstone of the `Nat213` discipline: the distinguishing's own counting
object is well-ordered, generated all the way down.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.WellOrder

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Order (lt le le_of_lt)
open E213.Lens.Number.Nat213.Factorization (wf_lt decBoundedExists)

/-- ★ **Strong induction on the native `lt`** — the named, ergonomic form of `wf_lt.induction`:
    `C` holds everywhere if it holds at each `n` whenever it holds at every `m < n`.  The reusable
    descent principle the discipline's recursions (`gcd_exists_mul`, `exists_factorization`) all
    use. -/
theorem strong_induction {C : Nat213 → Prop}
    (ih : ∀ n, (∀ m, lt m n → C m) → C n) (n : Nat213) : C n :=
  wf_lt.induction n ih

/-- ★★★ **Well-ordering over the Raw-generated ℕ₊**: every inhabited decidable predicate has a
    `lt`-minimal witness `m` (`P m` and no smaller `k` satisfies `P`).  Strong induction on the
    given witness `n`: at each step decide (via `decBoundedExists`) whether some `k < n` satisfies
    `P` — if so recurse into it, else `n` itself is minimal.  Decidable-`P` only (the general form
    needs excluded middle); ∅-axiom — the decision is `Factorization`'s constructive bounded search,
    no `Classical`. -/
theorem well_ordering {P : Nat213 → Prop} [DecidablePred P] (h : ∃ n, P n) :
    ∃ m, P m ∧ ∀ k, lt k m → ¬ P k := by
  obtain ⟨n, hn⟩ := h
  refine strong_induction
    (C := fun n => P n → ∃ m, P m ∧ ∀ k, lt k m → ¬ P k) ?_ n hn
  intro n ih hn
  cases decBoundedExists (fun c => lt c n ∧ P c) (fun _ => inferInstance) n with
  | isTrue hex =>
      obtain ⟨c, _, hlt, hpc⟩ := hex
      exact ih c hlt hpc
  | isFalse hno =>
      exact ⟨n, hn, fun k hk hpk => hno ⟨k, le_of_lt hk, hk, hpk⟩⟩

end E213.Lens.Number.Nat213.WellOrder
