import E213.Lens.FlatOntologyClosure
import E213.Lib.Math.Cauchy.DepthCeilingResidue
import E213.Lib.Math.Cauchy.ThueMorseRingEscape
import E213.Lib.Math.Cauchy.DepthMonotoneSynthesis

/-!
# The ceiling is one phenomenon: non-surjectivity of a finite-stage map

An adversarial audit catalogued the residue "ceilings" by **proof tactic** — Cantor diagonal
(`object1_not_surjective`), finite-tree leaf-path (`CoResidue.spineL_escapes`), eventual-monotonicity
(`s2Z_not_polyDepthZ`), finite-window pigeonhole (`aperiodic_not_autoRec`) — and called them
"separate engines / separate domains".  That is a taxonomy of *tactics*, not of *content*.  At the
level of what is asserted, every escape has the **same shape**:

> `∀ stage, gen stage ≠ target`   —   i.e. `target ∉ range gen`   —   i.e. **`gen` is not surjective.**

So they are not separate phenomena; they are one — *the finite-stage map misses the target* — the
residue **outside every view's image** (`object1_not_surjective`, the framework's own reading of the
residue).  This file makes that a theorem, not a theme: the schema `ReachedByNoStage`, the lemma that
it *is* non-surjectivity, and the named escapes exhibited as instances — `diag` (the universal
constructive diagonal, the Cantor archetype), `s2Z` (polynomials↦sequences, the non-holonomicity
ceiling), and `Object1` (the foundational pointing residue).  All share the archetype
`Cardinality.cantor_general`; the structural escape (trees↦traces, `CoResidue.spineL_escapes`) is the
same shape, already tied to the residue via `cantor_general` in
`DepthCeilingResidue.ceiling_residue_is_pointing_residue`.

**Why it nonetheless looks like separate domains** — the honest, sharp point.  *Classically* one
Cantor/cardinality argument settles every ceiling at once (countably many finite descriptions,
"uncountably" many objects).  The ∅-axiom / constructive discipline **forbids that shortcut** (no
`Classical`, no completed uncountable carrier).  So each ceiling must be witnessed by a **named,
constructed** escapee whose escape-proof is domain-specific — the leaf-path, `s2Z`'s
non-monotonicity, the `diag` formula.  The "different engines" are these *constructive realizers* of
the one non-surjection; the domains are the Lens-carvings.  One residue, many constructive witnesses,
forced apart by the refusal of the cardinality shortcut.

**The honest residue of the distinction** (kept, not erased).  The universal Cantor
`cantor_general` ("*no* `gen` of the self-cover shape is surjective") is strictly stronger than a
pointwise `ReachedByNoStage gen target` ("*this* `gen` misses *this* `target`").  The named escapes
are the pointwise constructive form; `cantor_general` is the universal archetype they realise.  The
ℝ side (`CauchyLensFounding`) genuinely sits apart: it is a *positive convergence* statement, not an
escape, until paired with a separate `∀ i, convergentᵢ ≠ phiCut` — so ℝ joins this schema only once
such a witness is supplied.
-/

namespace E213.Lib.Math.CeilingSchema

open E213.Lib.Math.Cauchy.DepthCeilingResidue (diag diag_not_in_seq)
open E213.Lib.Math.Cauchy.ThueMorseRingEscape (s2Z)
open E213.Lib.Math.Cauchy.DepthMonotoneSynthesis (s2Z_not_polynomial)
open E213.Lib.Math.Cauchy.NewtonGregory (newtonZ)

/-- **The ceiling schema.**  A target is reached by no stage of an enumeration: `∀ s, gen s ≠
    target`.  This is exactly `target ∉ range gen`. -/
def ReachedByNoStage {S T : Type} (gen : S → T) (target : T) : Prop := ∀ s, gen s ≠ target

/-- ★★★ **The schema IS non-surjectivity.**  `ReachedByNoStage gen target ⟹ gen` is not surjective.
    Every named escape, recast in this schema, says precisely "the finite-stage map misses the
    target" — one phenomenon, not many engines. -/
theorem not_surjective_of_reachedByNoStage {S T : Type} {gen : S → T} {target : T}
    (h : ReachedByNoStage gen target) : ¬ Function.Surjective gen := by
  intro hsurj
  obtain ⟨s, hs⟩ := hsurj target
  exact h s hs

/-! ## The named escapes are instances -/

/-- The universal constructive diagonal (the Cantor archetype, realised): for *every* level-map
    `f : Nat → (Nat → Nat)`, the diagonal `diag f` is reached by no level. -/
theorem diag_reached (f : Nat → Nat → Nat) : ReachedByNoStage f (diag f) :=
  fun i => (diag_not_in_seq f i).symm

/-- Polynomials ↦ sequences (the non-holonomicity ceiling): the popcount counter `s2Z` is reached
    by no Newton polynomial `newtonZ c d` — `s2Z_not_polynomial`, recast as non-membership. -/
theorem s2Z_poly_reached :
    ReachedByNoStage (fun dc : Nat × (Nat → Int) => fun n => newtonZ dc.2 dc.1 n) s2Z := by
  intro dc h
  exact s2Z_not_polynomial ⟨dc.1, dc.2, fun n => (congrFun h n).symm⟩

/-- ★★★★ **One phenomenon.**  The universal diagonal (the Cantor archetype), the non-holonomicity
    escape (polynomials↦sequences), and the foundational residue (`Object1`) are all **the same
    statement**: a finite-stage map is not surjective; the target is in the residue surplus, outside
    every view's image.  The proofs are domain-specific *constructive realizers* of the one
    non-surjection (`cantor_general` the universal archetype), forced apart only because the ∅-axiom
    discipline refuses the cardinality shortcut. -/
theorem ceilings_are_nonsurjectivity :
    (∀ f : Nat → Nat → Nat, ¬ Function.Surjective f)
    ∧ (¬ Function.Surjective (fun dc : Nat × (Nat → Int) => fun n => newtonZ dc.2 dc.1 n))
    ∧ (¬ Function.Surjective E213.Lens.FlatOntology.Object1) :=
  ⟨fun f => not_surjective_of_reachedByNoStage (diag_reached f),
   not_surjective_of_reachedByNoStage s2Z_poly_reached,
   E213.Lens.FlatOntologyClosure.object1_not_surjective⟩

end E213.Lib.Math.CeilingSchema
