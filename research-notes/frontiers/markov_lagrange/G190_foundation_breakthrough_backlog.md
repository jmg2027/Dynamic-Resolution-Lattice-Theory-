# G190 — The foundation's breakthrough backlog, and where Markov `H` sits in it

Tier-1 synthesis (a map and a naming, not new theorems).  A deep sweep of the Raw/Lens Lean code
(`Theory/Raw/`, `Lens/`) and the seed corpus (`seed/AXIOM/*`) turned up two distinct kinds of
"breakthrough" — *proven-but-underexploited tools* and *stated-but-unformalized targets* — and a clean
placement of the open Markov kernel `H` as a concrete instance of one of the seed's own open targets.
Discipline carried throughout: reframing ≠ proof; "latent" = candidate, not done.

## A. Proven-but-underexploited tools (Raw/Lens code, already `∅`-axiom)

These are built and verified, but applied narrowly — candidate engines for new theory work:

- **`Lens.equivG` / `Lens.refinesG`** (`Lens/ReadingEquiv.lean`).  Codomain-polymorphic
  reading-sameness: reduces *definitionally* to `=` (default instance) and to pointwise `↔`
  (`Raw → Prop` instance).  The whole refinement lattice (preorder, meet `prodLens`, join `joinLens`,
  bounds `idLens`/`constLens`) stated once with `refinesG` is `∅`-axiom across *every* codomain.  Most
  lattice lemmas are still in `=`-form — migrating them to `refinesG` inherits the `↔`-instance free.
- **`slashNu_final` + `lAna_unique`** (`Theory/Raw/CoResidue.lean`).  Finality of the exact slash-νF
  (the `Consistent ∧ AntiRefl` subtype) proved by *finite-path induction*, no coinduction.  Every
  recursive definition over the residue is the unique fixed-point solution, certifiable without
  bisimulation.
- **`traceEq_iff_not_distinct` + `mu_carrier_reachable_reduced_machine`** (`Theory/Raw/StateMachine.lean`).
  FSM minimality without Myhill–Nerode bisimulation: equality is the *complement of a positive witness
  path*.  An automata-theoretic toolkit for the residue, unused so far.
- **`kernel_correspondence`** (`Lens/Algebra/Corresp.lean`).  Bijection {Lens kernels} ↔
  {slash-congruences}, reading-native, no `Quot.sound` — the door to a dual-category development.
- **`spine_family_populates_nu`** (`CoResidue.lean`).  A `Tree`-indexed family of escaping νF
  inhabitants faithfully injecting the finite µF — a structure no Lens yet reads.

## B. Stated-but-unformalized targets (seed's own backlog)

The seed corpus states these as *doctrine* and flags them open — the framework's own breakthrough
backlog (per `seed/AXIOM/06_lens_readings.md` §6.7–6.8, `05_no_exterior.md` §5.2/§5.4, `08`):

1. **Lens injectivity hierarchy** — "which Lenses are injective?" is decided case-by-case; no unified
   `IsInjectiveLens` predicate + decision theorems (§6.1/§6.4/§6.7).
2. **No-incomparability theorem** — "any two objects admit *some* Lens making them comparable; true
   incomparability is impossible inside 213" — stated implicitly (§4.2 sideways-uniqueness + §5.1), not
   a theorem.
3. **Two-readings-constrain principle** — count-Lens vs difference-Lens, frozen vs dynamic, Bool-liar
   vs Nat-Lambek: "two structurally distinct readings of one residue, neither more fundamental"
   (§6.7, §5.2, §5.7) — co-presence stated, no formal Lens-level theorem.
4. **Cofactor-unification metatheorem** — "if two Lenses from distinct codomains produce the same
   cofactor from `(NS,NT,d)`, that cofactor is structural in Raw, not in either Lens" (§6.8) — the
   operational signature of no-exterior, doctrinal only.
5. **φ-unification** — every domain appearance of φ factors through `Mobius213`'s fixed-point theorem
   (§3.5, §5.6) — formalized per-domain, not bundled.

## C. Where Markov `H` sits — a concrete instance of (B.1)–(B.3)

The slope-vs-size wall is exactly the seed's open "two readings, one injective, is the other?" question
(B.1–B.3), in concrete number-theoretic form, and the Lens code already supplies its abstract frame:

- `Lens/Lattice/Lattice.lean` `refines_idLens_iff_injective` : `L.refines idLens ↔ L.view` injective.
  So **"a reading is injective" = "it refines the identity Lens."**
- The **slope** reading is injective (`slope_path_inj`) — slope refines `idLens`, closed.
- The **size** reading injective is exactly `H` (`markovMaxUnique_iff_orbitRealizabilityH`): two
  distinct nodes with the same Markov number coincide.  In Lens-native words, **`H` = "the size
  reading refines `idLens`"** — the open half of an injectivity-hierarchy question (B.1).
- The repo's lattice already contains *incomparable* Lens pairs whose disagreement is measured by their
  join (`Lattice/Join.lean`, the parity/depth incomparable instances) — the abstract shape of "two
  readings disagree, the join measures it," which is the slope/size relation (B.3).

So `H` is *analogous to* the seed's open injectivity-hierarchy question — the framework asking, in a
case where one reading is injective, whether the other is.  **Caveat (load-bearing).**  This is an
analogy, not an identification: the size reading is provably **not** a Raw-`Lens` (§D.2–3 below,
`markovGen_noncommutative`), so it does not literally live in the `IsInjectiveLens` lattice; and the
path-level `Function.Injective markovNum` is *not* formally tied to `MarkovMaxUnique` (that needs
`reverse_bridge`, unformalized here).  So "`H` = an injective coarsening" is a named analogy, and the
order calculus below neither proves nor bounds `H`.

## D. Landed this round — the foundation made concrete (in the right order)

Two `∅`-axiom installments, foundation first:

1. **The `IsInjectiveLens` calculus** (`Lens/Lattice/Injectivity.lean`, 6 PURE) — the metatheorem
   skeleton above `H`, the `∅`-axiom core of seed target (B.1).  `IsInjectiveLens L := Injective L.view`;
   `isInjectiveLens_iff_refines_idLens` (injective = refines the bottom `idLens`); `isInjectiveLens_idLens`
   (the identity is injective); **`isInjectiveLens_of_refines`** (monotone *down* the order — refining an
   injective Lens is injective); **`isInjectiveLens_prodLens_left`** (the meet inherits injectivity from
   a factor); `not_isInjectiveLens_constLens` (the top is maximally lossy).  So injectivity is a
   *downward-closed* sub-order of the refinement lattice, with `idLens` its least element — the formal
   home of "which readings are injective."

2. **Why the size reading is not residue-native** (`SternBrocotMarkov` §31, `markovGen_noncommutative`,
   PURE) — reaching the fundamental.  The Farey/slope combine (mediant) is *commutative* (`mediant_sym`),
   so the slope reading is a genuine Raw-`Lens`, honouring Raw's `a/b = b/a` (axiom clause 3).  The Markov
   *size* combine is the matrix product, and **`genL · genR ≠ genR · genL`** — non-commutative, hence not
   a `Raw.fold` (`fold_slash` needs symmetry).  So the size reading is **not** a residue-`Lens`: it lives
   on the *oriented* `List Bool` tree (the free monoid on two letters), one structural level above the
   direction-free residue.  This is the foundation-level root of the slope/size asymmetry, and it places
   the split in the seed's own §6.7 terms: **slope = count-style** (direction-free, residue-native, its
   injectivity provable), **size = difference-style** (orientation-breaking, the difference-Lens that
   breaks clause 3).  `H` is hard because its reading is not foldable over the residue — it needs exactly
   the orientation Raw discards.

3. **The principle behind (2), as a theorem** (`Lens/DirectionFree.lean`, PURE) — not just a witness.
   `combine_sym_on_image_of_homomorphism`: *any* Lens whose view is a slash homomorphism
   (`view (x/y) = combine (view x) (view y)`) has a `combine` **symmetric on its image**, forced by
   `Raw.slash_comm` (`x/y = y/x`).  Contrapositive: a non-symmetric combine cannot give a homomorphic
   Raw-`Lens`.  So "residue-native readings are direction-free" is now a proved foundation theorem
   (seed target B.3, the clause-3 / count-vs-difference principle), and `markovGen_noncommutative` is
   its concrete Markov instance: the size combine is non-symmetric, so the size reading provably escapes
   the residue.

4. **Slope determines size; the converse is `markovNum` injectivity** (`SternBrocotMarkov` §32, PURE —
   real Markov objects).  `slope_determines_size` (equal slope ⟹ equal Markov number, via the *real*
   `slope_path_inj`; `markovNum = (mNode).c`, the integer node max) — a genuine theorem about the tree.
   `sizeDeterminesSlope_iff_markovNum_injective` — the converse is exactly `Function.Injective markovNum`.
   **Honest scope**: this iff is a *light restatement* (immediate from `slope_path_inj`).  The link to
   the actual conjecture is now a **full equivalence** (§33 `→` + §34 `←`,
   `markovMaxUnique_iff_markovNum_injective`, PURE): `Function.Injective markovNum ↔ ∀ c ≥ 5,
   MarkovMaxUnique c`.  Both directions are theorems: §33 `markov_max_unique_of_markovNum_injective`
   (`→`), and §34 `markovNum_injective_of_markovMaxUnique` (`←`, proved with *no new number theory* by
   routing through the §28 window equivalence — `MarkovMaxUnique c → WindowRealizedUnique c` collapses
   the two nodes' realized windowed `√(−1)` residues, hence equal `markovRes`, hence equal slope, hence
   `slope_path_inj`).  So "size-injective `= H`" is now **literal**, not an analogy.  Honest scope: this
   is a *formulation-equivalence* between two statements of the open Frobenius conjecture (perimeter), not
   a proof of either, and it does not touch the cross-node `mod c ↔ ℤ` kernel.

5. **Injectivity is not upward-closed — an order analogue, not a Markov theorem**
   (`Lens/Lattice/Injectivity.lean`, `injectivity_not_upward_closed`, PURE).  Injectivity is inherited
   *down* the refinement order (`isInjectiveLens_of_refines`) but *not up*: `idLens` refines `constLens`.
   So the injective Lenses form a proper *down-set*, least element `idLens`.  **Honest scope**: this is
   the order-theoretic *analogue* of the slope/size situation, **not** a statement about `H`.  The size
   reading is provably **not** a Raw-`Lens` (item 3), so it does not literally live in this lattice;
   `H` is *analogous to* "an injective coarsening", and this lemma neither proves nor bounds it.  The
   chain ①–⑥ thus builds a real abstract injectivity calculus and two real Markov restatements (§31–§32)
   whose *connection* to the conjecture is a named analogy — it does not explain why `H` is hard.

## Honest verdict

Nothing here proves `H`, bounds it, or explains why it is hard.  What is real: (i) an `∅`-axiom abstract
injectivity calculus in the Lens lattice (§D.1, ⑥) — genuine order theory; (ii) the `∅`-axiom theorem
that residue-native readings are direction-free (§D.3, `DirectionFree`) and its concrete Markov instance
(`markovGen_noncommutative`); (iii) two real Markov restatements (§D.4, slope→size and the `markovNum`
injectivity iff, via the real `slope_path_inj`).  The slope/size joint is now **fully closed as an
equivalence**: `Function.Injective markovNum ↔ ∀ c ≥ 5, MarkovMaxUnique c`
(`markovMaxUnique_iff_markovNum_injective`, PURE — §33 `→` + §34 `←`).  So "size-injective `= H`" is
**literal**, not an analogy: the size-reading-injective formulation and the triple-uniqueness
formulation are *the same* open statement.  Still analogy-only: the size reading living in the
Raw-`Lens` lattice (false — provably not a Raw-`Lens`, so `⑥`'s order facts apply only by analogy).  So
the accurate headline is **"an abstract injectivity calculus, plus a closed formulation-equivalence
(size-injective ⟺ conjecture) and real Markov restatements"** — *not* "`H`'s position characterised /
why-it's-hard explained."  Crucially the equivalence is **perimeter**: it shows two statements of the
open Frobenius conjecture coincide, it does not prove either, and it does not touch the cross-node
`mod c ↔ ℤ` kernel (the only direction toward which — genuine incomparable-node comparison — remains
unbuilt, with no ready tool, per `G189`).

### Pointers
- frontier: `research-notes/G189_geodesic_lens_markov_frontier.md`, `§30` of `Real213/Markov/SternBrocotMarkov`
- Lens lattice: `Lens/Lattice/{Preorder,Meet,Join,Lattice}.lean`, `Lens/ReadingEquiv.lean`
- νF / FSM: `Theory/Raw/{CoResidue,StateMachine,Lambek,MuNuMirror}.lean`
- kernel ↔ congruence: `Lens/Algebra/Corresp.lean`
- seed targets: `seed/AXIOM/06_lens_readings.md` §6.7–6.8, `05_no_exterior.md` §5.2/§5.4/§5.7
