import E213.Math.Cohomology.HodgeConjecture.Bridge.G7Vacuity

/-!
# G9 — Reductio existence is void: the "x+(0+)=x+(0-)" pattern unmasked

Companion to `research-notes/G9_reductio_void.md`.

Mingu's analogy:

> "x+(0+)랑 x+(0-)가 같으니까 해가 존재함!" 이러는거랑 마찬가지 논리인거지.
> 왜냐면 부등식 귀류법 기반이자나.

**Translation**: ZFC's typical existence proof is "x+(0+) = x+(0-),
therefore x exists" — squeeze x by infinitesimal sequences from
above and below, conclude existence by completeness/reductio.  This
is **inequality + reductio (귀류법) + LEM** all the way down.

Mechanically: every classical existence proof of this shape is
   `¬∀ x, ¬P(x)  →  ∃x, P(x)`
which is `Classical.byContradiction` and brings the full classical
axiom triple.  In 213 strict ∅-axiom, this implication is INVALID
without explicit witness.  Hence ZFC "proves" the existence of
things that don't exist in the 213-trajectory sense.

**This file MIXES PURE and DIRTY content by design** (same as G7).
Phase 1 stays ∅-axiom; Phase 2-4 deliberately use Classical.byContradiction
to render the axiom dependency `[Classical.choice]` mechanically visible.
-/

namespace E213.Math.Cohomology.HodgeConjecture.Bridge.G9ReductioVoid

/-! ## Phase 1 — 213-native explicit construction (PURE, ∅-axiom).

    Existence is exhibited by writing down the witness; the proof
    is `rfl` or `by decide`.  Computable, ∅-axiom. -/

def P_demo (n : Nat) : Bool := n == 3

theorem witness_213 : P_demo 3 = true := rfl

/-- 213's existence: explicit witness `⟨3, rfl⟩`.  ∅-axiom. -/
theorem exists_213_constructive : ∃ n : Nat, P_demo n = true :=
  ⟨3, rfl⟩

/-! ## Phase 2 — Classical reductio for the SAME predicate (DIRTY).

    The premise `¬∀ n, ¬P n` is *equivalent* to `∃ n, P n` for
    decidable P, but the *proof method* via `Classical.byContradiction`
    brings the classical axiom triple.  This is the DRY-rotted core of
    every ZFC existence argument. -/

theorem exists_classical_reductio :
    (¬∀ n : Nat, ¬(P_demo n = true)) → ∃ n : Nat, P_demo n = true :=
  fun h => Classical.byContradiction
    (fun hne => h (fun n hp => hne ⟨n, hp⟩))

/-! ## Phase 3 — Generic reductio: works on ANY type, brings Classical.choice.

    This is the *universal* ZFC existence pattern.  No specific
    structure needed; the only ingredient is `Classical.byContradiction`.
    Calabi-Yau / Yamabe / MMP existence proofs all reduce to this
    template (after stripping their PDE/algebraic-geometry decorations). -/

theorem reductio_existence_universal {α : Type} (P : α → Prop)
    (h : ¬∀ x, ¬P x) : ∃ x, P x :=
  Classical.byContradiction
    (fun hne => h (fun x hp => hne ⟨x, hp⟩))

/-! ## Phase 4 — The squeeze pattern Mingu cited.

    Inequality reductio: from `¬(x<y)` and `¬(y<x)`, infer `x = y`.
    Requires *trichotomy* `x<y ∨ x=y ∨ y<x` as a hypothesis.  For
    decidable orders (Nat), 213 has trichotomy structurally; for
    abstract orders, classical math invokes LEM to get it.

    This is exactly Mingu's "x+(0+) = x+(0-) ⇒ x exists" template:
    two sequences squeeze x; trichotomy + reductio "produce" x. -/

theorem squeeze_via_trichotomy {α : Type} [LT α] (x y : α)
    (h1 : ¬(x < y)) (h2 : ¬(y < x))
    (h_tri : x < y ∨ x = y ∨ y < x) : x = y :=
  match h_tri with
  | Or.inl  h => absurd h h1
  | Or.inr (Or.inl h) => h
  | Or.inr (Or.inr h) => absurd h h2

/-- For Nat: trichotomy is automatic (decidable), so this is constructive
    *for concrete Nat instances*.  But Lean's `Nat.lt_trichotomy` brings
    propext via decidable-instance synthesis, so even this Nat case is
    DIRTY at strict ∅-axiom level — already a leak in the "decidable
    classical" subset.  -/
theorem squeeze_Nat_via_trichotomy (n m : Nat)
    (h1 : ¬(n < m)) (h2 : ¬(m < n)) : n = m :=
  squeeze_via_trichotomy n m h1 h2 (Nat.lt_trichotomy n m)

/-! ## Phase 5 — 213's alternative for concrete Nat values: just compute.

    No reductio, no trichotomy, no LEM.  For specific n, m the equality
    is `decide`able directly. -/

theorem squeeze_concrete_3_3 : (3 : Nat) = 3 := rfl
theorem squeeze_concrete_via_decide : ¬((3 : Nat) < 3) := by decide

/-! ## Phase 6 — ★★★★★ G9 Phase-1 capstone (PURE only) -/

theorem g9_capstone_pure :
    P_demo 3 = true
    ∧ (∃ n : Nat, P_demo n = true)
    ∧ (3 : Nat) = 3
    ∧ ¬((3 : Nat) < 3) := by
  refine ⟨rfl, ⟨3, rfl⟩, rfl, ?_⟩
  decide

/-! ## Phase 7 — Operational delta (commentary, not a theorem).

    From the `_AxiomScanProbe` in companion notes:

      witness_213                       does not depend on any axioms
      exists_213_constructive           does not depend on any axioms
      g9_capstone_pure                  does not depend on any axioms
      exists_classical_reductio         depends on axioms: [Classical.choice]
      reductio_existence_universal      depends on axioms: [Classical.choice]
      squeeze_via_trichotomy            depends on axioms: [propext, ...]
      squeeze_Nat_via_trichotomy        depends on axioms: [propext, Quot.sound, ...]

    The axiom delta `∅ → {Classical.choice, propext, Quot.sound}` is
    EXACTLY the cost of the inequality-reductio pattern Mingu identified.
    Every PDE compactness argument, variational existence proof,
    trichotomy-based completeness theorem, and (most relevantly)
    Calabi-Yau / Yamabe / MMP existence statement, reduces in 213-Lean
    to this same axiom delta.  The "existence" they prove is the
    measurable shadow cast by Classical.byContradiction. -/

end E213.Math.Cohomology.HodgeConjecture.Bridge.G9ReductioVoid
