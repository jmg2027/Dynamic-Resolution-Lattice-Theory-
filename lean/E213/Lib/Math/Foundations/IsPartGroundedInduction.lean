import E213.Theory.Raw.API

/-!
# ℕ-induction grounded in the distinguishing's own descent (`isPart_wf`) — ∅-axiom

The descent leg names the
central open bar: a deep discipline (factorisation / FTA) over the generated ℕ must have its
**termination grounded in `Raw`'s own descent** `Lambek.isPart_wf` (the distinguishing's
well-foundedness, proved by `Raw.rec`), **not** in Lean's borrowed `Nat.strongRecOn`.  The honest
finding there: FTA-over-`Nat213` currently completes through `Nat`'s strong recursion — so the
"generation" is still re-derivation at the descent layer.

This file supplies the missing **engine**: strong/measure induction on `ℕ` whose well-founded
recursion is `isPart_wf` itself, transported along the primitive tower `rawTower : ℕ → Raw`.  Any
descent built on `strongInduction_grounded` / `measureInduction_grounded` therefore recurses on the
*distinguishing's* descent, clearing the descent-leg bar for whatever discipline uses it.

**The grounding, exactly.**  `m < n` embeds into `TransGen IsPart (rawTower m) (rawTower n)`
(`tower_lt_transGen` — each `+1` is one `IsPart` rung, `tower_ascent_isPart`).  `IsPart` is
well-founded (`isPart_wf`), its transitive closure is too (`transGen_wf`), and well-foundedness pulls
back along `rawTower` (`InvImage.wf`) and down a subrelation (`Subrelation.wf`).  So `Nat`'s `<` is
well-founded **because the distinguishing's descent is** — the recursion engine is `isPart_wf`.

*Honest scope.*  The *embedding* lemma `tower_lt_transGen` uses `Nat` structural recursion (it proves
an inequality); the **descent engine** — the `WellFounded` that powers the recursion — is `isPart_wf`,
not `Nat.strongRecOn`.  That is the criterion the descent leg states.  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Foundations.IsPartGroundedInduction

open Relation (TransGen)
open E213.Theory.Raw.Lambek (IsPart isPart_wf)
open E213.Theory.Raw.PrimitiveTower (rawTower)
open E213.Theory.Raw.MuNuMirror (tower_ascent_isPart)

/-! ## §1 — transitive closure preserves well-foundedness -/

/-- Accessibility is preserved by transitive closure. -/
theorem acc_transGen {α : Sort u} {r : α → α → Prop} {a : α} (h : Acc r a) :
    Acc (TransGen r) a := by
  induction h with
  | intro x _ ih =>
    refine Acc.intro x (fun y hy => ?_)
    cases hy with
    | single hyx => exact ih y hyx
    | tail hyb hbx => exact (ih _ hbx).inv hyb

/-- The transitive closure of a well-founded relation is well-founded. -/
theorem transGen_wf {α : Sort u} {r : α → α → Prop} (h : WellFounded r) :
    WellFounded (TransGen r) :=
  ⟨fun a => acc_transGen (h.apply a)⟩

/-! ## §2 — `<` on ℕ embeds into `TransGen IsPart` along the primitive tower -/

/-- Each `m < n` is a chain of `IsPart` rungs `rawTower m ⟶⁺ rawTower n` — one rung per `+1`
    (`tower_ascent_isPart`). -/
theorem tower_lt_transGen : ∀ {m n : Nat}, m < n →
    TransGen IsPart (rawTower m) (rawTower n)
  | m, n + 1, h => by
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with heq | hlt
    · subst heq
      exact TransGen.single (tower_ascent_isPart _)
    · exact TransGen.tail (tower_lt_transGen hlt) (tower_ascent_isPart n)

/-! ## §3 — `Nat.lt` is well-founded *because* the distinguishing's descent is -/

/-- ★★★ **`Nat`'s `<` is well-founded, grounded in `isPart_wf`.**  Not `Nat.lt_wfRel`: this proof's
    well-founded engine is the distinguishing's own descent `isPart_wf`, pulled back along the
    primitive tower (`tower_lt_transGen` + `InvImage.wf` + `Subrelation.wf` + `transGen_wf`).  The
    descent leg's bar — termination grounded in `Raw`, not borrowed `Nat` WF — at the level of the
    induction engine. -/
theorem nat_lt_wf_via_isPart : WellFounded (fun m n : Nat => m < n) :=
  Subrelation.wf
    (r := InvImage (TransGen IsPart) rawTower)
    (fun h => tower_lt_transGen h)
    (InvImage.wf rawTower (transGen_wf isPart_wf))

/-! ## §4 — the induction engines, grounded in the distinguishing -/

/-- ★★★ **Strong induction on `ℕ`, grounded in `isPart_wf`.**  To prove `P n` for all `n`, prove it
    from all strictly-smaller values — with the well-founded recursion powered by the distinguishing's
    descent, not `Nat.strongRecOn`.  Any discipline whose descent routes through this clears the
    descent-leg bar. -/
theorem strongInduction_grounded {P : Nat → Prop}
    (ind : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n :=
  fun n => nat_lt_wf_via_isPart.induction n ind

/-- ★★★ **Measure induction grounded in `isPart_wf`.**  The `f`-measure descent version — the shape
    `FTA` existence needs (`Ω`-descent: peel a prime, the prime-count drops).  Powered by the
    distinguishing's descent via `strongInduction_grounded`. -/
theorem measureInduction_grounded {α : Sort u} (f : α → Nat) {P : α → Prop}
    (ind : ∀ a, (∀ b, f b < f a → P b) → P a) : ∀ a, P a := by
  have key : ∀ n a, f a < n → P a := by
    refine strongInduction_grounded (P := fun n => ∀ a, f a < n → P a) ?_
    intro n ih a ha
    exact ind a (fun b hb => ih (f a) ha b hb)
  exact fun a => key (f a + 1) a (Nat.lt_succ_self (f a))

end E213.Lib.Math.Foundations.IsPartGroundedInduction
