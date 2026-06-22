import E213.Lens.LensCore
import E213.Lens.Foundations.SemanticAtom
import E213.Lens.Cardinality
import E213.Lens.Lattice
import E213.Lens.Foundations.NoExteriorClosure
import E213.Theory.Raw.API

/-!
# The proof-ISA — mathematics as compilation from the pointing/residue instruction set

213 is a compiler stack for mathematics:

    L0  atoms `a, b` + distinguishing `/`            (Raw)        — the "gates"
    L1  the primitive proof-operations               (this file)  — the **ISA**
    L2  number towers (ℕ ℤ ℚ ℝ as Lens bundlings), structures      — "languages"
    L3  theorems / open problems                                   — "applications"

The point of "the residue is the *most primitive* of proof techniques for the infinite/abstract" is
**operational, not rhetorical**: open problems are *compiled down* through the layers to the instruction
set below — found by systematic exploration of the operation space shared across all infinite-abstract
reasoning, not by problem-specific insight.  Every instruction is already built and `∅`-axiom; this file
gathers them as the named instruction set, each pointing at its witness.

Honest status (Church–Turing-flavoured thesis): each instruction is a *theorem* witness; "every proof
compiles to these" is a *thesis*, whose deepest instance — the infinite, via `DIAGONALIZE` = the residue
(Cantor) — is itself a theorem (`isa_diagonalize`).  The ISA does not auto-solve (locating the proof-
residue stays work, `05_no_exterior.md` §5.3); it changes the *character* of that work from per-problem
invention to systematic compilation on a shared instruction set.
-/

namespace E213.Lens.ProofISA

open E213.Theory E213.Lens

/-- **DISTINGUISH** — produce the residue of two somethings (`x ≠ y ↦ x/y`). -/
abbrev isa_distinguish := @E213.Theory.Raw.slash

/-- **READ / FOLD** — interpret a residue in a codomain via a Lens (the catamorphism `Raw → α`). -/
abbrev isa_read := @E213.Lens.Lens.view

/-- **DIAGONALIZE** — the something distinguishable from *everything pointed at* is forced to exist; the
    primitive of every infinity-proof (Cantor / Russell / Gödel / Turing).  The diagonal *is* the
    residue. -/
abbrev isa_diagonalize := @E213.Lens.Cardinality.cantor_general

/-- **GAP** — a reading does not cover its codomain; the un-covered surplus is the residue (not every
    function is a fold). -/
abbrev isa_gap := @E213.Lens.Foundations.SemanticAtom.exists_non_lens_expressible

/-- **SEPARATE** — two distinct objects are separated by an injective reading (a reading refines the
    identity Lens iff it distinguishes every pair). -/
abbrev isa_separate := @E213.Lens.Lattice.Lattice.refines_idLens_iff_injective

/-- **COMPILE-DOWN** — any framework that distinguishes at all receives the *unique* morphism from `Raw`
    (initiality): everything compiles from the residue. -/
abbrev isa_compile_down := @E213.Lens.Foundations.SemanticAtom.universalMorphism_unique

/-- **REFLECT** — predicates / proofs are themselves `Raw` (the naming of any candidate lands inside). -/
abbrev isa_reflect := @E213.Lens.Foundations.NoExteriorClosure.naming_is_internal

/-- **LOOP (µ/ν)** — finite-path induction certifies the unique fixed point of a residue recursion (no
    coinduction needed). -/
abbrev isa_loop := @E213.Theory.Raw.CoResidue.slashNu_final

end E213.Lens.ProofISA
