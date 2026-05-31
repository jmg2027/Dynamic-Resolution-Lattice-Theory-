import E213.Theory.Raw.API
import E213.Lens.LensCore

/-!
# Lens.FlatOntology — §9.3 flat-ontology realisation

Formalisation of the flat-ontology table in
`seed/AXIOM/06_lens_readings.md` §6.3 under the strict ∅-axiom
reading (decidable `Rawⁿ → Bool` predicates rather than
`Prop`-valued).

The table:

| Unit                   | Element                | Predicate form  |
|------------------------|------------------------|-----------------|
| object (1st-order)     | r ∈ Raw                | Raw → Bool      |
| object (n-th order)    | (r₁,…,rₙ) ∈ Rawⁿ        | Rawⁿ → Bool     |
| type                   | a subset of Rawⁿ        | predicate       |
| relation               | a subset of Raw²        | predicate       |
| function               | functional subset of Raw² | predicate + uniqueness |
| Lens                   | (labelled) predicate    | (Raw → α)       |

One universe — no separate sorts for types, objects, relations,
Lens.  All live in the predicate algebra on Raw^n.

This file records the alignment as concrete Lean definitions
(stub level: definitions + their basic interconnections; the
full Gödel-encoding self-closure is deferred — predicates can in
principle be encoded back to Raw via truth-table numerals, but
that closure is a separate continuation).
-/

namespace E213.Lens.FlatOntology

open E213.Theory (Raw)
open E213.Lens (Lens)

/-! ## §9.3 row 1 — object (1st-order) -/

/-- A Raw element viewed as the *minimal* unary predicate: the
    indicator function `· = r`.  Every Raw is itself a predicate
    in this flat reading (the predicate "equal to this Raw"). -/
def Object1 (r : Raw) : Raw → Bool := fun s => decide (s = r)

/-- Object1 is true exactly at its argument. -/
theorem Object1_self (r : Raw) : Object1 r r = true := by
  unfold Object1; exact decide_eq_true rfl

/-! ## §9.3 row 1 — n-th order objects -/

/-- An n-tuple of Raws, encoded as a function `Fin n → Raw`.  An
    n-th order object IS its indicator function. -/
def Object (n : Nat) (rs : Fin n → Raw) : (Fin n → Raw) → Bool :=
  fun ss => decide (∀ i : Fin n, ss i = rs i)

/-! ## §9.3 row 2 — types as predicates -/

/-- A *type* in the flat ontology is exactly a decidable predicate
    on Raw^n — i.e., a function from `Fin n → Raw` to `Bool`. -/
abbrev Type213 (n : Nat) : Type := (Fin n → Raw) → Bool

/-- Unary types — predicates on a single Raw. -/
abbrev UnaryType : Type := Raw → Bool

/-- Every Raw inhabits the indicator type for itself. -/
def singleton_type (r : Raw) : UnaryType := fun s => decide (s = r)

theorem singleton_type_witnessed (r : Raw) :
    singleton_type r r = true := by
  unfold singleton_type; exact decide_eq_true rfl

/-! ## §9.3 row 4 — relations as binary predicates -/

/-- A relation is a binary predicate. -/
abbrev Relation : Type := Raw → Raw → Bool

/-- Equality on Raw is itself a Relation in the flat ontology. -/
def eqRelation : Relation := fun r s => decide (r = s)

/-- `eqRelation` is reflexive. -/
theorem eqRelation_refl (r : Raw) : eqRelation r r = true := by
  unfold eqRelation; exact decide_eq_true rfl

/-- `eqRelation` is symmetric (as Bool). -/
theorem eqRelation_symm (r s : Raw) :
    eqRelation r s = eqRelation s r := by
  unfold eqRelation
  by_cases h : r = s
  · rw [h]
  · have h' : s ≠ r := fun e => h e.symm
    rw [decide_eq_false h, decide_eq_false h']

/-! ## §9.3 row 5 — functions as functional relations -/

/-- A function `Raw → Raw` is the relation `R(x, y) ↔ f(x) = y`,
    which is automatically functional (∀ x, unique y).  This is
    the flat-ontology embedding of any Raw-endofunction. -/
def functionAsRelation (f : Raw → Raw) : Relation :=
  fun x y => decide (f x = y)

theorem functionAsRelation_functional (f : Raw → Raw) (x : Raw) :
    functionAsRelation f x (f x) = true := by
  unfold functionAsRelation; exact decide_eq_true rfl

/-! ## §9.3 row 6 — Lens as the labelled-predicate special case -/

/-- A Lens with codomain `Bool` IS a unary predicate in the flat
    ontology — the catamorphism `Raw.fold L.base_a L.base_b L.combine`
    instantiates `view : Raw → Bool` which is a `UnaryType`. -/
def lensBoolAsType (L : Lens Bool) : UnaryType := L.view

/-- Lens with any decidable-equality codomain `α` recovers a
    family of unary types via fibre indicators. -/
def lensFibreType {α : Type} [DecidableEq α] (L : Lens α) (a : α) :
    UnaryType :=
  fun r => decide (L.view r = a)

/-! ## §9.3 unity statement

All six rows of the table are realised by the single primitive
"decidable predicate on Raw^n".  Lens is then the labelled
catamorphism specialisation.

The closure direction (a predicate encoded back as a Raw) has two halves:
  * `Lens/PredicateSelfEncoding.lean` — *positive*: every finite-prefix /
    definable predicate DOES encode back to a Raw (`predicateToRaw`).
  * `Lens/FlatOntologyClosure.lean` — *limit*: the self-cover
    `Object1 : Raw → (Raw → Bool)` is faithful (injective) but not total
    (not surjective, by Cantor) — it "closes exactly up to the residue,"
    the Cantor-unpointable surplus, whose named lead member is the
    undifferentiated predicate `fun _ => true`.
See also `Lens/Cardinality/Godel.lean` for the Raw → ℕ injection and
`research-notes/G29_residue.md` "자기-덮음" for the loop,
`research-notes/G152_residue_self_covering.md` for the synthesis.
-/

end E213.Lens.FlatOntology
