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

So `H` is not an isolated number-theory accident: it is the **first concrete, fully-stated instance of
the seed's open injectivity-hierarchy / no-incomparability metatheorem** — the framework asking, in a
case where one reading is provably injective, whether the other is.  Closing `H` would be one data
point for (B.1)–(B.2); a general `IsInjectiveLens` calculus would be the metatheorem above it.

## Honest verdict

Nothing here proves `H` or closes a frontier — it is a *map*.  Its value: (i) it surfaces a stack of
already-`∅`-axiom tools (`equivG`, `slashNu_final`, `kernel_correspondence`, FSM-minimality) waiting for
a problem; (ii) it transcribes the seed's own doctrinal backlog into a list of formalizable metatheorem
targets; and (iii) it places `H` precisely inside that backlog (the injectivity-hierarchy question),
giving any future session a foundation-level reason the Markov wall is hard, not just a local one.  The
reframing is a naming, recorded at that status.

### Pointers
- frontier: `research-notes/G189_geodesic_lens_markov_frontier.md`, `§30` of `Real213/SternBrocotMarkov`
- Lens lattice: `Lens/Lattice/{Preorder,Meet,Join,Lattice}.lean`, `Lens/ReadingEquiv.lean`
- νF / FSM: `Theory/Raw/{CoResidue,StateMachine,Lambek,MuNuMirror}.lean`
- kernel ↔ congruence: `Lens/Algebra/Corresp.lean`
- seed targets: `seed/AXIOM/06_lens_readings.md` §6.7–6.8, `05_no_exterior.md` §5.2/§5.4/§5.7
