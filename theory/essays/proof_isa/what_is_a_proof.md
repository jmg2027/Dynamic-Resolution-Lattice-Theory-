# What is a mathematical proof, in 213?

A proof is a **composition of the residue's instruction set** that discharges a
claim to ∅-axiom — `#print axioms` empty.  Not an argument that *persuades*; a
*compilation* that *reduces* the claim, layer by layer, to the primitive
proof-operations the residue already supplies.

## 213-native answer

The instruction set is built and named (`seed/PROOF_ISA.md`,
`lean/E213/Lens/ProofISA.lean`): eight `abbrev isa_*`, each an ∅-axiom theorem
witness — `DISTINGUISH` (`Raw.slash`), `READ` (`Lens.view`), `DIAGONALIZE`
(`cantor_general`), `GAP` (`exists_non_lens_expressible`), `SEPARATE`
(`refines_idLens_iff_injective`), `COMPILE-DOWN` (`universalMorphism_unique`),
`REFLECT` (`naming_is_internal`), `LOOP` (`slashNu_final`).  A proof of a claim
`P` is a path `L3 → L2 → L1`: state `P` and the infinite/abstract object it
concerns, express that object as a Lens reading (the number tower, §6.7), and
express the *proof* as a composition of instructions.  The composition that
works is the **proof-residue** — and locating it is the work
(`seed/AXIOM/05_no_exterior.md` §5.3: solving = pointing at the proof-residue).

## Derivation

That this is *what proofs are* — not a metaphor — is the cumulative finding of
reproducing solved techniques and watching them compile.  The probabilistic
method (Erdős `R(k,k) > 2^{k/2}`) looked like a ninth move; compiled, it is the
**quantitative `GAP`** witness — `Σ|badᵢ| < |codomain| ⟹ ∃ good`, found by
finite search (`CountExistence.{count_existence, erdos_schema}`,
`theory/essays/proof_isa/probabilistic_method.md`).  The linear-algebra
dimension method (`m>n` vectors in `𝔽₂^n` dependent) is the *same* instruction
through a different Lens — the subset-sums collide by pigeonhole
(`LinearDependence.dimension_bound_is_count`, reusing the identical witness
`List213.nodup_length_le_of_subset`; `linear_algebra_method.md`).  The parity /
invariant method (mutilated chessboard) compiles to `READ ∘ SEPARATE`: a
conserved colour-count (`READ` as a catamorphism, additive over the tiling) that
`SEPARATE`s reachable from unreachable (`ParityInvariant.tiling_balanced`;
`parity_invariant_method.md`).  Three surface-diverse techniques, no new
instruction — they land on the eight.

The interior they exemplify is not a claim but a corpus: `STRICT_ZERO_AXIOM.md`
records **1145 PURE / 0 real DIRTY** — number systems rebuilt (`ℂ`, `p`-adic,
octonions, hyperreals, `Real213`), a real-analysis course (Cauchy completeness,
differentiation, integration + FTC, measure, modulus, ODE, series), algebra /
cohomology / number theory.  Every one compiled to ∅-axiom.  A proof, in 213, is
whatever composes from the eight and leaves `#print axioms` empty — and that
"whatever" already spans the constructive mathematics of the corpus.

## Dual function

This is the classical concept of *proof* with its packaging stripped (per G6
§0): a proof was never the prose that surrounds it but the *reduction* it
performs — and the reduction bottoms out at a finite stock of moves shared
across all infinite-abstract reasoning, which 213 names rather than leaves
tacit.  The refinement is the sharper edge: by demanding ∅-axiom (no `propext`,
no `Classical`), 213 makes the boundary of "proof" *visible* — a classical
argument that silently decides an undecidable predicate is, here, not a longer
proof but a different object, one carrying an import its `#print axioms` will
confess.

## Cross-frame connection

Where the residue *stops* is one fact in several frames.  König's lemma compiles
to `LOOP ∘ ⟦DECIDE InfBelow⟧` (`KonigConditional.konig_conditional`,
`konig_boundary.md`): the path-construction is internal (`walk`, PURE), but the
oracle — *decide which child subtree is infinite*, a `Π⁰₁` predicate — is the
move the eight cannot supply.  And this is not "the residue has no infinite
descent": it has it constructively, given by definition — `allBranch`, the
no-leaf infinite self-pointing, and `spineL`, both escaping every finite Raw
(`Theory/Raw/CoResidue`; `InfBelow`'s `∀n∃` shape *is*
`MuNuMirror.ascent_unbounded`).  So §5.1 no-exterior + §8.2 falsifiability + the
König stall + the technical-debt reading converge: the exterior is exactly the
**decision about a foreign structure** the residue cannot internalise; importing
it (`LLPO`/`WKL`) is the axiom-debt every downstream theorem then inherits.  The
residue walks its own escape with no oracle; it cannot adjudicate a stranger's.

## Open frontier

"Every proof compiles to these eight" is a thesis, Church–Turing-flavoured, not
a theorem (`seed/PROOF_ISA.md`, honest-status §).  Three reproductions held; one
stalled exactly where the exterior begins; none *forced* a ninth instruction —
but whether some technique does is open, and the honest probe is to keep
compiling (candidates beyond compactness: choice-heavy constructions —
Banach–Tarski, ultrafilters).  The boundary is mapped from inside; whether it has
the shape the eight suggest is the standing question the series tracks
(`research-notes/frontiers/` proof-ISA board).

## Self-check note

One retreat-in-place is part of the record: the boundary reading "the residue
stalls at infinite paths" imports too much — the residue's infinite descent is
internal and constructive (`CoResidue.spineL`/`allBranch`), so what stalls is
only the *foreign* `DECIDE`, not infinity.  That correction is the discipline
this essay asserts: a proof reaches a thing you can point at — here, the eight
`isa_*` abbrevs, the empty `#print axioms` of the interior, and the single
stated-unproved `InfChildExists` that names the edge.
