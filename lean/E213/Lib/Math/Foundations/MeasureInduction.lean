/-!
# `measureInduction` — the descent cluster's engine (structural, ∅-axiom)

`theory/meta/de_abstraction_calculus.md` maps the corpus's results onto a lattice by their
*removal-fingerprint*.  One cluster — the residue (`object1_not_surjective`), `δ²=0`
(`delta_sq_zero_general`), even-cardinality cancellation (`even_card_cancel`) — shares the
**fixed-point-free involution** bottom, with `XorInvolution.xorFold_involution` as its engine
and `xor b b = false` (the *binary* distinguishing) as its kernel.

This file gives a **second** cluster its engine.  FTA / multiplicative descent
(`MulDescentRec.mulDescentRec`), the additive Raw descent (`Theory.Raw.no_infinite_descent`),
the `Ω`-descent (`BigOmega.no_infinite_mul_descent`) do *not* bottom in an involution; they
bottom in **measure-descent**: a measure into `ℕ` that strictly decreases has no infinite
chain.  Their shared engine is

  `measureInduction f ind : ∀ a, P a`  — from `∀ a, (∀ b, f b < f a → P b) → P a`.

**Why a named structural engine.**  `measureInduction` is proved by **structural `Nat.rec`**
on a bound (the `mulDescentRec` technique): `cic_footprint` verdict MINIMAL-STRUCTURAL, no
`Acc.rec`.  It is the reusable engine that *names* cluster B's bottom.

*Honest scope (a refuted prediction)*: a first draft claimed routing descent through this
**drops a CIC fragment** versus `Nat.strongRecOn` (whose *constant* is EXTENDED-FRAGMENT —
`Acc.rec`/`WellFounded.rec`).  `cic_footprint` **refuted that**: corpus proofs using `induction
… using Nat.strongRecOn` (e.g. `OddPartDecomposition.decomp_and_odd`) already measure
MINIMAL-STRUCTURAL — the equation compiler emits structural `brecOn` and never pulls the
`Nat.strongRecOn` constant (with its `Acc.rec`) into the closure.  So there is **no footprint
improvement** here; this engine's value is reuse + explicitness, not de-CIC-ing.

**The two bottoms.**  Cluster A's kernel is the *binary* distinguishing (`Bool`, `xor b b`);
this cluster's kernel is the *iterated* distinguishing (`ℕ` = `succ`, `Nat.rec`).  The lattice's
two resolution-bottoms are the distinguishing's two basic readings — binary and counted —
exactly `Bool` (the first distinguishing) and `ℕ` (its count-Lens).  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Foundations.MeasureInduction

/-- ★★★ **Measure induction (structural).**  To prove `P a` for all `a`, it suffices to prove
    `P a` from `P b` for every `b` of strictly smaller `f`-measure.  The descent cluster's
    engine — proved by `Nat.rec` on a bound (MINIMAL-STRUCTURAL, no `Acc.rec`/`WellFounded`),
    so anything routed through it stays in the minimal CIC fragment.  ∅-axiom. -/
theorem measureInduction {α : Sort u} (f : α → Nat) {P : α → Prop}
    (ind : ∀ a, (∀ b, f b < f a → P b) → P a) : ∀ a, P a := by
  have key : ∀ n a, f a < n → P a := by
    intro n
    induction n with
    | zero => intro a ha; exact absurd ha (Nat.not_lt_zero (f a))
    | succ n ih =>
      intro a ha
      exact ind a (fun b hb => ih b (Nat.lt_of_lt_of_le hb (Nat.le_of_lt_succ ha)))
  exact fun a => key (f a + 1) a (Nat.lt_succ_self (f a))

/-- Strong induction on `ℕ` — the `f = id` instance of `measureInduction`. -/
theorem natStrongInduction {P : Nat → Prop}
    (ind : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n :=
  measureInduction (fun n => n) ind

end E213.Lib.Math.Foundations.MeasureInduction
