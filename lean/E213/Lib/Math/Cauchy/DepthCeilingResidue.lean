import E213.Lens
import E213.Lens.FlatOntologyClosure

/-!
# DepthCeilingResidue — naming the ceiling-raising is a diagonalisation; the act leaves a residue

The depth arc found an open-ended hierarchy of axes: each named ceiling (`ω²`,
`ω^ω`, `ε₀`, …) is where one iteration of "resolve the infinite by a finite
reference" closes, and the *next* axis raises it.  The question this file answers:
**what happens when you make "the act of raising the ceiling" itself a reference —
a single object?**

The answer closes the whole development back onto its own starting point (the
*residue*, `Lens/FlatOntologyClosure`).  To name "the ceiling-raising" is to take
the sequence of all the reference-levels you have built — a function `f : ℕ → (the
level's growth)` — and form one object that dominates them all.  That object is the
**diagonal** `diag f n = f n n + 1`, and the diagonal argument shows it is *not in
the sequence*: it escapes every level it was built to summarise (`diag_not_in_seq`).
So the act of referencing the whole tower **produces a new object outside the
tower** — a fresh ceiling, which can again be named, and again.

This is not a coincidence of ordinals; it is the *same* structure as the residue
itself.  `FlatOntologyClosure.object1_not_surjective` (Cantor) says the pointing map
`Object1 : Raw → (Raw → Bool)` covers `Raw` *faithfully* yet *never totally* — the
predicates outside its image are the residue surplus.  The ceiling-diagonalisation
here is that same Cantor map in temporal guise: **every attempt to point at "the
whole act of pointing" leaves a surplus outside what was pointed at**
(`ceiling_reference_leaves_residue` reuses `cantor_general` directly).

So "make the ceiling-raising a reference" does not terminate the hierarchy and does
not escape it either — it reproduces the residue one level up.  The ordinal tower
(`ε₀`, Veblen, …) and the foundational residue are the *same* self-covering closure
read at two scales: the act of comprehension always lands inside the thing it tried
to exceed, leaving exactly the gap that forces the next step.  The hierarchy has no
top because *pointing has no exterior* (`seed/AXIOM/05_no_exterior.md`).

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthCeilingResidue

open E213.Theory (Raw)

/-! ## §1 — naming the ceiling-raising is a diagonalisation -/

/-- The **diagonal** of a sequence of growth-functions: `diag f n = f n n + 1`.
    Reading `f i` as "the `i`-th reference level / ceiling", `diag f` is the single
    object that names *all* of them at once — built to dominate the whole tower. -/
def diag (f : Nat → Nat → Nat) : Nat → Nat := fun n => f n n + 1

/-- ★ The named ceiling strictly exceeds each level at its own diagonal point:
    `f i i < diag f i`. -/
theorem diag_exceeds (f : Nat → Nat → Nat) (i : Nat) : f i i < diag f i :=
  Nat.lt_succ_self (f i i)

/-- ★ The named ceiling differs from each level at the diagonal point. -/
theorem diag_escapes (f : Nat → Nat → Nat) (i : Nat) : diag f i ≠ f i i :=
  Nat.succ_ne_self (f i i)

/-- ★★★ **Naming the ceiling-raising escapes the sequence.**  The diagonal object
    `diag f` is **not** any level `f i` of the tower it summarises — referencing
    "all the ceilings at once" produces a new ceiling outside them all.  So the act
    of naming the hierarchy never closes it; it makes the next rung. -/
theorem diag_not_in_seq (f : Nat → Nat → Nat) : ∀ i, diag f ≠ f i :=
  fun i hi => diag_escapes f i (congrFun hi i)

/-! ## §2 — this is the residue: Cantor self-covering, one scale up -/

/-- ★★★ **Referencing the whole act leaves a residue (Cantor).**  Any attempt to
    *enumerate* the comprehension of a type `X` — a map `X → (X → Bool)` — fails to
    be surjective: there is always a predicate (a "ceiling") outside its image.
    This is `cantor_general`, the same engine behind
    `FlatOntologyClosure.object1_not_surjective`: pointing at "everything pointable"
    leaves an un-pointed surplus.  The depth-ceiling diagonal of §1 is one instance;
    the residue and the unbounded ordinal tower are the *same* self-covering
    closure. -/
theorem ceiling_reference_leaves_residue {X : Type} :
    ¬ ∃ g : X → (X → Bool), Function.Surjective g :=
  E213.Lens.Cardinality.cantor_general

/-- ★★ **Tie to the foundational residue.**  The pointing self-cover `Object1 : Raw
    → (Raw → Bool)` is faithful but never total (`self_covering_closure`).  The same
    non-surjectivity that makes the residue is what makes every named ceiling
    incomplete — both are `cantor_general`.  Naming the ceiling-raising *is* a
    pointing act, and like every pointing act it leaves the residue outside its
    image. -/
theorem ceiling_residue_is_pointing_residue :
    (Function.Injective E213.Lens.FlatOntology.Object1
      ∧ ¬ Function.Surjective E213.Lens.FlatOntology.Object1)
    ∧ (¬ ∃ g : Raw → (Raw → Bool), Function.Surjective g) :=
  ⟨E213.Lens.FlatOntologyClosure.self_covering_closure,
   E213.Lens.Cardinality.cantor_general⟩

end E213.Lib.Math.Cauchy.DepthCeilingResidue
