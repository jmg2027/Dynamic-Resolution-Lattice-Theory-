# G196 — Markov `H`, compiled to the proof-ISA (the workflow applied to the open kernel)

The `seed/PROOF_ISA.md` workflow, run on the hardest target: compile the open Markov kernel `H` down to
the instruction set, locate the precise missing instruction-composition, and connect every piece the
marathon built into one compiled statement.  This does not solve `H` (nothing does); it produces `H`'s
*compiled form* and names the exact gap — which is what the methodology promises (systematic compilation,
not problem-specific insight).

## L3 — the problem

`H` = `OrbitRealizabilityH c` = Markov uniqueness at a composite `c` (`ω ≥ 2`): among the `2^(ω−1)`
windowed `√(−1)` roots mod `c`, exactly one `±`-suborbit is realized by a Markov triple.  Equivalently
(`markovMaxUnique_iff_markovNum_injective`, §34): `Function.Injective markovNum`.

## L2 — the objects as Lens readings

| object | reading | built |
|---|---|---|
| slope `p/q` | `mediantLens.view` (the genuine Raw-Lens, the geodesic) | `slope_path_inj` (injective) |
| Christoffel word | `chrNode p` (word-mediant tree) | `chrNode`, `markovNum_eq_chrNode_trace` |
| size `markovNum` | `(mNode).c` = `tr(contMatProd (chrNode p))/3` | the bridge |
| residue mod `c` | `markovRes` = difference-Lens shadow | window/orbit tower |

## L1 — the proof as an instruction composition

`H = Injective markovNum`.  Through L2, `markovNum p = tr(contMatProd (chrNode p))/3` — so

> **`H` ⟺ the continuant-trace of the Christoffel word `chrNode` is injective on tree paths.**

Decomposed into instructions:
  * **SEPARATE** — `slope_path_inj`: distinct paths have distinct slopes.  *This is LOOP-invariant* (it
    holds across the whole tree / all `c`, not at fixed `c`) — the genuine Raw-Lens, direction-free.  ✓ built.
  * **READ / FOLD** — `markovNum_eq_chrNode_trace`: size = continuant-trace of the Christoffel word.  The
    slope → size bridge.  ✓ built.
  * **LOOP** — continuant monotonicity in every position (`continuant_*_strict_mono`, via reversal); the
    Vieta descent / tree induction.  ✓ built.

So everything composes *except one step*: from SEPARATE (slopes distinct) + READ (size = continuant-trace)
to **size distinct** — i.e. `continuant-trace injective across incomparable Christoffel words`.  The LOOP
(monotonicity) gives only the *ordering* (Aigner, necessary-not-sufficient).  **The missing instruction is
a SEPARATE at the continuant-trace level across incomparable words** — the one composition no built
instruction supplies.  This is the same wall five prior analyses hit, now located as a precise
instruction-gap rather than a vague "hard step."

## The compilation's new constraint — the trace is reversal-invariant

A genuinely new fact the compilation exposes, using a theorem the marathon built
(`continuant_reverse : K[w] = K[w.reverse]`): the continuant-trace `tr(contMatProd w) = K[w] + K[middle w]`
is **reversal-invariant** (reversal fixes `K[w]` and maps `middle w` to its reverse, fixing `K[middle w]`
too).  So the trace *alone* cannot distinguish a Christoffel word from its reverse.

Consequence for `H`: the missing SEPARATE must hold **modulo reversal** — `H` requires that the Christoffel
tree never produces a word and its reverse as *distinct* paths with the *same* trace.  (Christoffel words
are near-palindromes — central word a palindrome — and the reverse encodes the *same* Markov number, the
trace being conjugation-invariant.)  So the precise open content is: **distinct tree paths give distinct
continuant-traces, even though the trace is reversal-blind** — the tree structure must carry the
distinction the trace drops.  This is `H` sharpened to a statement about the interaction of the
reversal-symmetry (`continuant_reverse`, ✓) and the tree's path-structure (`slope_path_inj`, ✓).

## The systematic next search (what the workflow hands the next session)

Not "await insight," but: **find or rule out the cross-word continuant-trace SEPARATE.**  Concretely:
  1. ✅ **RESOLVED — reverse-pairs do not occur.**  `chrNode_starts_one` (∅-axiom): every Christoffel
     tree word starts with `1` (=`A`) — the seed `[1,1]` head, preserved by the mediant.  Computationally,
     every tree word also ends with `2` (=`B`).  So a word's *reverse* starts with `2` and is **never**
     itself a tree word: no two distinct paths are reverses, so the trace's reversal-blindness never
     collapses two paths.  The reversal red-herring is removed; the missing SEPARATE is purely the
     non-reversal case (distinct `A`-initial words with equal trace).
  2. Is there an ISA instruction that SEPARATEs continuant-traces across incomparable words, beyond the
     monotonicity ordering?  If not (the trace is genuinely the only invariant and it is reversal-blind),
     that is a *structural* result: `H` is not ISA-expressible by the current instruction set — which
     would itself be a sharp, recordable finding (the instruction set is incomplete *for this problem*,
     per the `05_no_exterior.md` §5.3 "the proof-residue is not yet pointed at").

## Honest verdict

The compilation is precise and connects every built piece (`slope_path_inj` = SEPARATE, the continuant
bridge = READ, monotonicity = LOOP, `continuant_reverse` = the reversal constraint), and names the exact
missing composition (the cross-word continuant-trace SEPARATE, modulo reversal).  It does not cross the
wall — consistent with all prior analyses — but it converts "the hard step" into a *located instruction
gap* with two concrete next moves (1, 2 above).  That is the workflow doing its job: the framework
supplies the instruction set and the compiled target; the search for the one missing composition is the
work.

### Pointers
- compiled target: `Real213/SternBrocotMarkov` §34 (`markovMaxUnique_iff_markovNum_injective`), `Real213/ContinuantMarkov` (`markovNum_eq_chrNode_trace`, `chrNode`)
- instructions: SEPARATE `slope_path_inj`; READ `markovNum_eq_chrNode_trace`; LOOP `Continuant.continuant_*_strict_mono`; reversal `Continuant.continuant_reverse`
- ISA + workflow: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`
- the gap, prior framings: `G189` (Casoratian), `G192` (geodesic boundary), `G194` (locality), `G195` (cohomology)
