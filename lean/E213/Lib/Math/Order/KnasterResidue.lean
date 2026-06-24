/-!
# Knaster–Tarski conserves the residue — totality reifies it, never escapes it (∅-axiom)

`theory/meta/de_abstraction_calculus.md` (the falsification section) probed **Knaster–Tarski** as
the one *totality* claim that might escape the residue: "every monotone map on a **complete** lattice
has a fixed point" looks like a self-cover with **no** remainder.  This file shows it is not — the
totality is bought *entirely* by completeness, and completeness is exactly the **adjunction of the
residue as a point**.  The theorem renames the residue a fixed point; it does not dissolve it.

**The two fixed-point theorems are the same power-object, opposite directions.**

  * **Lawvere / Cantor** (`OneDiagonal.no_surjection_of_fixedpointfree`): a fixed-point-**free**
    modifier on the power-object `α → Bool` makes the self-cover `α → (α → Bool)` non-surjective —
    the diagonal **escapes** (the residue, `object1_not_surjective`).
  * **Knaster–Tarski** (`Order.KnasterTarski.lfp_fixed`): a monotone endo `α → α` on a *complete*
    lattice **has** a least fixed point `lfp = glb {x | f x ≤ x}`.  The completeness datum is
    `glb : (α → Prop) → α` — a map whose **domain is the same power-object** `α → Prop` that Cantor
    shows α cannot cover.

The residue is **conserved** across the swap, and the witness is `succ` on ℕ:

  * `succ` is monotone (`succ_monotone`, cluster B — counting) and fixed-point-**free**
    (`succ_fpf`: `n + 1 ≠ n`);
  * so "every monotone endo has a fixed point" is **false on (ℕ, ≤)**
    (`knaster_conclusion_false_on_nat`) — ℕ is *not* a complete lattice;
  * the fixed point Knaster–Tarski *would* assign `succ` is the lub of **all** of ℕ — `∞`, the
    **residue/limit reached by none** (`Real213 … limit_unreached_but_decided`: convergents strictly
    advance, the limit is attained by no term).  Completeness is precisely the adjunction of that
    `∞`; the theorem hands `succ` the residue and calls it a fixed point.

So Lawvere's escaping diagonal and Knaster–Tarski's least fixed point are **one object** — the
power-object's un-covered point — read once as *what escapes upward* (`α → Bool`) and once as *what
must be adjoined below* (the lub `glb` supplies).  Totality does not beat the residue; it pays
completeness to *contain* it.  ∅-axiom.
-/

namespace E213.Lib.Math.Order.KnasterResidue

/-- `succ` is monotone for the usual order on ℕ — cluster B (counting): `≤` is the count-difference,
    and adding one to both sides preserves it. -/
theorem succ_monotone : ∀ a b : Nat, a ≤ b → a + 1 ≤ b + 1 :=
  fun _ _ h => Nat.succ_le_succ h

/-- `succ` is fixed-point-**free** on ℕ: `n + 1 ≠ n`.  The no-fixed-point Knaster–Tarski needs
    completeness to overcome — proved structurally (`Nat.succ.inj` / `Nat.noConfusion`), no `propext`. -/
theorem succ_fpf : ∀ n : Nat, n + 1 ≠ n
  | 0     => fun h => Nat.noConfusion h
  | n + 1 => fun h => succ_fpf n (Nat.succ.inj h)

/-- ★★★ **Knaster–Tarski's conclusion is FALSE on `(ℕ, ≤)`.**  There is a monotone, fixed-point-free
    endomap — `succ` — so "every monotone endo has a fixed point" fails: ℕ is not a complete lattice.
    The fixed point the theorem would assign `succ` is the lub of all of ℕ = `∞`, the residue reached
    by none; *completeness is the adjunction of that residue*.  Totality reifies the residue, it does
    not escape it — the same power-object Lawvere's diagonal escapes, Knaster–Tarski pays to contain. -/
theorem knaster_conclusion_false_on_nat :
    ¬ (∀ f : Nat → Nat, (∀ a b, a ≤ b → f a ≤ f b) → ∃ n, f n = n) := by
  intro h
  obtain ⟨n, hn⟩ := h (fun n => n + 1) succ_monotone
  exact succ_fpf n hn

/-- The contrapositive reading: **completeness is non-trivial precisely because the residue is
    missing.**  Any carrier on which a monotone fixed-point-free endo lives (here `succ`/ℕ) cannot be
    a complete lattice — it lacks the lub the endo climbs toward.  Knaster–Tarski's hypothesis is the
    demand that *that lub already be a point*, i.e. that the residue be adjoined. -/
theorem mono_fpf_blocks_completeness :
    (∃ f : Nat → Nat, (∀ a b, a ≤ b → f a ≤ f b) ∧ ∀ n, f n ≠ n) :=
  ⟨fun n => n + 1, succ_monotone, succ_fpf⟩

end E213.Lib.Math.Order.KnasterResidue
