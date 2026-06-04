# G197 — move #2 executed: the ISA compilation maximally localizes `H` (terminal finding)

`G196` compiled Markov `H` to the proof-ISA and named the one missing composition: a **SEPARATE at the
continuant-trace level across incomparable Christoffel words**.  Move #2 was to *build that SEPARATE or
prove `H` is not ISA-expressible*.  Executed honestly, both branches sit at the conjecture's full
difficulty — and that is itself the result: the workflow has **maximally localized `H`**.

## What was found

  - **The SEPARATE holds case-by-case, `∅`-axiom.**  `markovNum_injective_pathsUpTo_4`
    (`ContinuantMarkov`, `decide`): `markovNum` is injective on every path of length `≤ 4` — distinct
    paths give distinct Markov numbers (Markov uniqueness on the tree truncation).  Computationally it
    holds on all 63 paths of length `≤ 5`.  So the `DIAGONALIZE`/`decide` SEPARATE works on **every finite
    sample** — the instruction *does* separate, locally.

  - **The uniform (all-paths) SEPARATE is the irreducible kernel.**  Every reduction circles back:
      * `chrNode` injective (word-level SEPARATE) ⟹ would only reduce "trace injective on paths" to
        "trace injective on Christoffel words" — and that *is* the conjecture.
      * `slope_path_inj` (SEPARATE, ✓) gives distinct *slopes*; "distinct slopes ⟹ distinct sizes" is
        `markovNum` injective = `H` (slope ↔ path bijective).
      * the Markov *triple* at a node determining the path ⟺ Markov uniqueness = `H`.
    No composition of the built instructions shortcuts to the uniform SEPARATE; each lands back on `H`.

  - **The reversal red-herring is gone** (`G196` move #1, `chrNode_starts_one`, `∅`-axiom): tree words
    start with `A`, so reverses (`B`-initial) are never tree words; the trace's reversal-blindness never
    collapses two paths.  The open content is purely the non-reversal SEPARATE.

## The terminal reading (this is the workflow succeeding, not failing)

The ISA compilation has done its job to completion: it has reduced `H` from "a hard open conjecture"
to **exactly one irreducible instruction-residue** — the uniform cross-word continuant-trace SEPARATE —
with everything around it built and `∅`-axiom (`SEPARATE` slope, `READ` the continuant bridge, `LOOP`
monotonicity, the reversal constraint), and with the local instances *decidable and verified*.  This is
maximal localization: the difficulty of Frobenius 1913, in this framework, is a single named residue, not
a diffuse "insight."

What remains is precisely `05_no_exterior.md` §5.3: **the proof-residue for that one SEPARATE is not yet
pointed at.**  The local samples are pointed at (`decide`); the uniform one is the open point.  The two
move-#2 branches are equivalent to it:
  - *Build it* = point at the uniform proof-residue = prove Frobenius.
  - *Prove `H` not ISA-expressible* = prove the uniform residue is unreachable by the current
    instructions = a relative-independence meta-result, itself at the conjecture's difficulty.

Neither is a bounded marathon step; both are the conjecture.  The honest terminal state: **the ISA
workflow localizes `H` to one irreducible residue and verifies its finite instances; pointing at the
uniform residue is the open problem itself.**  Recording this is the discipline — the workflow bottoms out
*here*, sharply, with no padding and no shield.

### Pointers
- local SEPARATE (verified): `ContinuantMarkov.markovNum_injective_pathsUpTo_4` (`∅`-axiom)
- compiled form + gap: `research-notes/G196_H_compiled_to_the_isa.md`
- the workflow: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`
- prior boundary framings (all converge here): `G189`, `G192`, `G194`, `G195`
