# The proof-ISA — mathematics as compilation from the pointing/residue instruction set

Operating principle, not metaphor.  "The residue is the *most primitive* of proof techniques for the
infinite/abstract" means: mathematics can be built in layers the way a computing stack is built from
binary up — and **open problems are compiled down to a shared instruction set, not cracked by
problem-specific insight.**  The instruction set is already built and `∅`-axiom; the canonical index is
`lean/E213/Lens/ProofISA.lean`.

## The stack

| Layer | 213 | Computing analogue |
|---|---|---|
| **L0** | atoms `a, b` + distinguishing `/` (`Raw`) | gates / binary |
| **L1 — ISA** | the primitive proof-operations (below) | the instruction set |
| **L2** | number towers `ℕ ℤ ℚ ℝ` as Lens bundlings (§6.7); structures (Markov tree, continuants, …) | languages / runtimes |
| **L3** | theorems / open problems | applications |

You do not re-derive the ISA per application; you **compile** the application down to it.

## L1 — the instruction set (each already a theorem witness, `∅`-axiom)

| Instruction | Meaning | Witness (`ProofISA.lean`) |
|---|---|---|
| **DISTINGUISH** | produce the residue of two somethings (`x ≠ y ↦ x/y`) | `Raw.slash` |
| **READ / FOLD** | interpret a residue in a codomain via a Lens (catamorphism `Raw → α`) | `Lens.view` |
| **DIAGONALIZE** | the something distinguishable from *everything pointed at* is forced to exist — the primitive of every infinity-proof (Cantor / Russell / Gödel / Turing); the diagonal **is** the residue | `cantor_general` |
| **GAP** | a reading does not cover its codomain; the un-covered surplus is the residue (not every function is a fold) | `exists_non_lens_expressible` |
| **SEPARATE** | two distinct objects are separated by an injective reading | `refines_idLens_iff_injective` |
| **COMPILE-DOWN** | any framework that distinguishes at all receives the *unique* morphism from `Raw` (initiality) | `universalMorphism_unique` |
| **REFLECT** | predicates / proofs are themselves `Raw` (naming a candidate lands inside) | `naming_is_internal` (`NoExteriorClosure`) |
| **LOOP (µ/ν)** | finite-path induction certifies the unique fixed point of a residue recursion | `slashNu_final` (`CoResidue`) |

This is the "most primitive atomic element, all already built."  Earlier scattered foundational
theorems, seen as *one instruction set*.

## Methodology — compile, do not crack

Research an open problem by **compiling it down the layers** (`L3 → L2 → L1`) and locating the right
*composition of ISA operations* — the proof-residue — by systematic exploration of the operation space
that is **shared across all infinite-abstract reasoning**, not by problem-specific genius.

The Markov marathon was already this, implicitly:

  - Markov numbers = **READ** (count-Lens, `value`); `markovNum = continuant` bridge = **FOLD / COMPILE**.
  - `slope_path_inj` = **SEPARATE** (non-constructive separation, the `DIAGONALIZE` family).
  - continuant monotonicity / reversal = **LOOP** (induction) + **FOLD**.
  - the open kernel `H` = **GAP / realizability** — *which residue is realized*, a Lens-image question.

Making the ISA explicit turns the next attack on `H` from "await a genius insight" into "which
composition of `GAP ∘ SEPARATE ∘ LOOP` realizes the residue" — systematic, on a shared instruction set.

## Honest status (so it is a programme, not a shield)

Church–Turing-flavoured.  Each instruction is a **theorem** witness.  "Every proof compiles to these"
is a **thesis**, whose *deepest instance* — the infinite, via `DIAGONALIZE` = the residue (Cantor) — is
itself a theorem (`isa_diagonalize`).  The ISA does **not** auto-solve: locating the proof-residue stays
work (`05_no_exterior.md` §5.3 — solving = pointing at the proof-residue, hard to locate).  What changes
is the *character* of that work — from per-problem invention to systematic compilation on a shared
instruction set.  That change is the substance behind "this is not wordplay."

## Pointers

  - instruction index: `lean/E213/Lens/ProofISA.lean`
  - closure (nothing exhibitable as outside): `seed/AXIOM/01_residue.md` §1.0, `Lens/NoExteriorClosure.lean`
  - solving = pointing at the proof-residue: `seed/AXIOM/05_no_exterior.md` §5.3
  - the residue as Cantor's diagonal: `Lens/FlatOntologyClosure.lean` (`object1_not_surjective`), `Lens/Cardinality/Cantor.lean`
  - number towers as Lens bundlings: `seed/AXIOM/06_lens_readings.md` §6.7
