# G203 — the modulus shift compiled to all four layers: the REFRAME archetype

The `3c±2` modulus shift (`G202`, `markov_max_unique_via_3c_minus_2`) closed composite Markov numbers by
moving the problem from a 4-root reading (`mod c`) to a 2-root reading (`mod M = 3c−2`).  Compiling that
move to the 213 stack — Raw / Lens / proof-ISA / residue — makes a **single pattern** visible and adds a
**fourth lift archetype** to the catalog (`G199`: DIAGONAL/LOOP/ORBIT → +REFRAME).

Hard facts: the Lean theorems (`markov_max_unique_via_3c_minus_2`, `two_roots_of_two_prime_pow`,
`sq_eq_collapse_pp`, all ∅-axiom).  The rest is the *compilation* (interpretation), per discipline.

**The move, one line.**  Re-express a problem about residues `mod c` (over-counting reading, `SEPARATE`
fails) as one about residues `mod M = 3c±2` (prime-power reading, `SEPARATE` succeeds).  Same object,
different resolution; bridged by `9c²−4 = (3c−2)(3c+2)`.

## Four-layer compilation

### Raw type (most basal)
A Markov triple is a Raw distinguishing-structure.  `c`, `u mod c`, `w mod M` are all **count-Lens /
difference-Lens readouts of the same Raw object** — the *modulus is itself a Lens output* (a count
parameter), not a Raw primitive: "the modulus" does not exist pre-Lens.  The discriminant `9c²−4 =
tr²−4·det` is a **difference-Lens readout** (`06_lens_readings §6.7`, ℤ = difference-Lens).  The move =
read the *same* Raw structure through a different count-modulus.  Raw invariant; reading parameter changes.

### Lens design
`mod c` and `mod M` are two Lens arrows out of the triple.  `Lattice.refines_idLens_iff_injective`
(= `SEPARATE`): a reading refines the identity Lens ⟺ injective.  `mod c` does **not** refine id (4-root
fiber, non-injective); `mod M` (prime-power) **does** (2 roots + parity ⟹ injective).  Both factor through
the **discriminant-Lens `Δ = 9c²−4`** (one coarse Lens, two refinements).  Per `unified_equivalence`, they
are not two concepts but **decompositions of one Lens-arrow**; per failure-mode "View promoted to
identity", neither `mod c` nor `mod M` is *what the object is* — both are facets.  The question is which
refinement attains injectivity (`SEPARATE`).

### proof-ISA
The c-side `SEPARATE` instruction fails.  The move is the composition
`REFLECT → READ → SEPARATE`:
  - **REFLECT** (`naming_is_internal`): the discriminant is derived *internally* and **factors**
    `9c²−4 = (3c−2)(3c+2)`, naming the alternate moduli from within.
  - **READ** (`Lens.view`): re-fold the residue through the factor modulus.
  - **SEPARATE** (`sq_eq_collapse_pp`): under the prime-power factor, the reading separates.

### residue / 213
`c` and `M` are two **Lens-presentations of one residue** (the Markov configuration).  Uniqueness is
**presentation-invariant** but becomes *readable* in the prime-power presentation (the one where the
reading is injective).  Exactly failure-mode "External-ruler smuggling": a presentation is a
residue-*internal* pointing; separability/depth is a property of the *pointing* (which modulus), not of the
residue.  No exterior — both readings internal; the residue does not change, only the resolution.

## The pattern

> **Factor the shared invariant (modulus / discriminant); READ/SEPARATE through the factor whose fiber is
> smallest (prime-power → few roots).  Object invariant, reading resolution changed.**

**Unification (the payoff).**  This is *the same move* as the CRT used in the even `2·pᵏ` family
(`G201`), one layer down:

  - `2·pᵏ`: factor the **modulus** `2·pᵏ = 2 × pᵏ`, read mod 2 + mod `pᵏ`, recombine (CRT).
  - `3c±2`: factor the **discriminant** `9c²−4 = (3c−2)(3c+2)`, read mod the prime-power factor.

Both: *factor an invariant, read through the prime-power factor where the fiber collapses to ≤ 2 roots.*
CRT and the modulus shift are one archetype at two layers (modulus-factoring vs discriminant-factoring).

## The fourth lift archetype: REFRAME / presentation-transport

`G199` catalogued DIAGONAL (cost 0), LOOP (one induction), ORBIT (free-action collapse).  REFRAME is the
**meta-lift**: *transport the problem to a reading where a solved `SEPARATE`-archetype applies.*  It does
not solve the residue in place — it changes the presentation so that an already-solved archetype (here the
prime-power 2-root `SEPARATE`) fires.

  - **Lift cost**: a good factor of the shared invariant.
  - **Conditional**: works only when the invariant has a prime-power factor.  Fails at `1325` (both
    `3c±2` composite) — no presentation has a small fiber, and the residue is the class-number-hard kernel
    (Frobenius, `G202`).
  - **Dual to `§36`** (`markovNum_subtree_size_interleaves`, the order-monovariant exhaustion): `§36`
    proved a reading *cannot be improved in place* (size interleaves across the fork); REFRAME is the
    complement — *transport to a reading where it can*.

Answer-refinement to "do we need a new ISA instruction?" (`G200`): still **no instruction** — the residue
is ORBIT/realizability — but REFRAME earns a place beside DIAGONAL/LOOP/ORBIT as a fourth **meta-strategy
for lifting**, the one that says: before attacking the residue, check whether a presentation-transport
sends it to a solved archetype.

## Anchors (all ∅-axiom, `Lib/Math/Foundations/ProofISALifts.lean`)
- `lift_reframe` = `MarkovPrimeFactor.two_roots_of_two_prime_pow` (CRT form)
- `lift_reframe_modulus` = `MarkovUniqueness.markov_max_unique_via_3c_minus_2` (discriminant form)
- `lift_reframe_collapse` = `MarkovPrimeFactor.sq_eq_collapse_pp` (the fiber collapse `SEPARATE`)
- dual: `SternBrocotMarkov.markovNum_subtree_size_interleaves` (`§36`, in-place exhaustion)
- ISA: `seed/PROOF_ISA.md`, `Lens/ProofISA.lean`; catalog: `G199`, `G201`, `G202`
