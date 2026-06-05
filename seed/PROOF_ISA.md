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

### GAP sub-mode — COUNT (quantitative `GAP`: deficit ⟹ existence)

`GAP` above is *qualitative* (a structural reason a reading misses its codomain — "not every function is
a fold").  Compiling the **probabilistic method** (Erdős 1947, `R(k,k) > 2^{k/2}`) down the ISA surfaced
its *quantitative* witness: when the bad readings are provably **fewer** than the codomain
(`Σ|badᵢ| < |codomain|`), the un-covered surplus is forced, and — the carrier being a finite residue — it
is *found* by search, no `Classical`.  This is one `GAP`-arrow read by **cardinality**, not a ninth
instruction (registering it as such would be the "view promoted to identity" failure).  Its decisive tell:
the repo already used it across ≈25 Lean files as `pigeonhole` (the `N+1 → N` qualitative face) without naming it.

  · witness: `CountExistence.count_existence` / `erdos_schema` (∅-axiom)
  · the lift (why the per-event count holds): `RamseyLowerBound.{count_factor, matchesC_count}` — each
    free distinguishing **doubles** the count, so existence-counting *factors* because distinguishings
    multiply (catalogued, Archetype 4, `ProofISALifts.lean`).
  · the "why" in full: `theory/essays/proof_isa/probabilistic_method.md`.

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

## Usage — the compilation workflow

Worked walkthrough (the demonstration `lean/E213/Lens/ProofISADemo.lean`, `∅`-axiom):

  1. **State the problem at L3** and name the infinite/abstract object it concerns.
     *Example*: "the count of a `Raw` is unbounded" — the `ℕ`-infinite, via the count-Lens.
  2. **Compile to L2** — express the objects as Lens readings (the number tower, §6.7).
     count = **READ** (`value = Lens.leaves.view`).
  3. **Compile to L1** — express the *proof* as a composition of ISA instructions.
     "no largest" = **DISTINGUISH** (form the residue `r / x`) ∘ **READ** (its count grows) — the
     forcing of a residue larger than anything pointed at is the `DIAGONALIZE` family.
  4. **Discharge `∅`-axiom** — each instruction is a built witness; the proof is their composition
     (`value_slash` = READ over DISTINGUISH; `count_unbounded` = the composition).

For an **open** problem the workflow is identical, with step 3 the search: *which composition of
instructions realizes the proof-residue*.  For Markov `H`: step 2/3 already identify `H` = `GAP` /
realizability ("which windowed residue is realized"); the remaining search is which `SEPARATE`/`LOOP`
composition *forces* the realized residue.  The framework supplies the instruction set and the
compilation target; the search for the composition is the work (`05_no_exterior.md` §5.3).

## The lift catalog — compilation as a cumulative instrument

An open problem's difficulty, once compiled to L1, is a **missing finite→uniform lift**: the residue
instruction (e.g. `SEPARATE`) holds on every finite sample, and pointing at the *uniform* version is the
open content.  So the standing method is not only "compile this one problem" but **catalogue the lifts of
problems already solved** — each solved lift is a reusable template, and a problem missing the *same* lift
as an open one gives a transfer.  The catalog (`lean/E213/Lib/Math/Foundations/ProofISALifts.lean`, all
`∅`-axiom) records six structurally distinct archetypes:

  - **DIAGONAL / direct** (`lift_diagonal`, Cantor) — the `DIAGONALIZE` instruction self-supplies the
    uniform witness; **lift cost zero**.
  - **INDUCTIVE / LOOP** (`lift_loop`, Fermat `a^p ≡ a`) — a finite per-step identity (`COMPILE-DOWN` of
    the binomial mod `p`) lifted by induction; **cost one induction**.
  - **ORBIT / free-action** (`lift_orbit`, composite Markov uniqueness) — a free group action collapses a
    finite window onto orbit representatives; **cost: free-action collapse + a realizability residue**.
  - **REFRAME / presentation-transport** (`lift_reframe`, CRT `2·pᵏ`; `lift_reframe_modulus`, the `3c±2`
    modulus shift) — the meta-lift: when `SEPARATE` fails under one reading, factor a shared invariant
    (modulus / discriminant) and re-`READ` through the prime-power factor where a solved `SEPARATE` fires
    (`REFLECT → READ → SEPARATE`); **cost: a good factor of the invariant**.  Conditional (needs a
    prime-power factor) and the dual of in-place monovariant exhaustion — transport the problem rather than
    improve the reading.
  - **COUNT / cardinality-doubling** (`lift_count`, the probabilistic method / Erdős `R(k,k) > 2^{k/2}`) —
    on a finite residue, `Σ|badᵢ| < |codomain|` forces a good element; the lift is multiplicativity of
    counting (each free distinguishing doubles the count); **cost: a counting bound**.  The quantitative
    face of `GAP` (`pigeonhole` is its qualitative face).
  - **FLOW / monovariant normal-form** (`lift_flow`, `flow_reaches`; instance `lift_flow_gcd`, the
    Euclidean GCD flow) — the well-founded sibling of LOOP: a self-map with a `Nat`-monovariant that
    strictly descends off fixed points converges to a normal form (`(a,b) ↦ (b%a,a)` reaches
    `(0, gcd a b)`, the gcd the invariant the descent preserves); **cost: a monovariant strictly
    descending off fixed points**.  The discrete realization of the Ricci-flow shape
    (`GeometrizationConjecture/Ricci.lean`'s open functional, monovariant in place of Perelman's
    entropy) and the other completion of in-place monovariant exhaustion REFRAME is the dual of.

Markov `H` matches none cleanly — closest is **ORBIT**, which is *in `H`'s own family* (the same
free-unit-root action already lifts a finite root-window to uniform composite uniqueness, leaving a per-`c`
realizability residue).  The catalog is the instrument that says so: the direction is to probe the
orbit / µ-ν lift of the trace-`SEPARATE`, the one archetype with a realized same-family precedent.
Compiling each new solved theorem into the catalog is the cumulative half of the workflow.

## Honest status (so it is a programme, not a shield)

Church–Turing-flavoured.  Each instruction is a **theorem** witness.  "Every proof compiles to these"
is a **thesis**, whose *deepest instance* — the infinite, via `DIAGONALIZE` = the residue (Cantor) — is
itself a theorem (`isa_diagonalize`).  The ISA does **not** auto-solve: locating the proof-residue stays
work (`05_no_exterior.md` §5.3 — solving = pointing at the proof-residue, hard to locate).  What changes
is the *character* of that work — from per-problem invention to systematic compilation on a shared
instruction set.  That change is the substance behind "this is not wordplay."

## Pointers

  - instruction index: `lean/E213/Lens/ProofISA.lean`
  - lift catalog (solved finite→uniform lift archetypes): `lean/E213/Lib/Math/Foundations/ProofISALifts.lean`
  - closure (nothing exhibitable as outside): `seed/AXIOM/01_residue.md` §1.0, `Lens/NoExteriorClosure.lean`
  - solving = pointing at the proof-residue: `seed/AXIOM/05_no_exterior.md` §5.3
  - the residue as Cantor's diagonal: `Lens/FlatOntologyClosure.lean` (`object1_not_surjective`), `Lens/Cardinality/Cantor.lean`
  - number towers as Lens bundlings: `seed/AXIOM/06_lens_readings.md` §6.7
