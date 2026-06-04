# Research-grade closure gate — candidate criteria (open meta-frontier)

**Status:** candidates only — recorded for later decision, NOT yet adopted.
Originator prompt (Mingu Jeong, 2026-06-04): "단순 0 공리가 닫힘 조건이
아니라 뭔가 좀 진짜 진지한 수학 연구스러운 게이트가 있으면 좋겠다."

## The gap

The current closure bar is `∅`-axiom + build-green + the
`theory/PROMOTION_CRITERIA.md` gate (H1–H4 hard, S1–S3 soft).  Read them
honestly: **every one is a hygiene/bookkeeping check** — the proof is
axiom-clean (H1), it compiles (H2), it is filed in a ring (H3), it is
cataloged (H4), its meanings are co-located (S1), it is citable (S2), its
scratch notes are archived (S3).

None of these ask the question a working mathematician asks: *is this
result actually worth anything?*  A `by decide` over a 5-element finite
check passes all of H1–S3 and is mathematically empty.  `∅`-axiom is a
**necessary** integrity condition, not a **sufficient** seriousness
condition.  This note curates candidate sufficiency gates.

## Candidate gates (the seriousness dimension)

Grouped; each tagged `[new]` (absent from PROMOTION_CRITERIA) or
`[implicit]` (partially present).  `★` = strongest candidates.

### A. Non-triviality / depth
- **G-depth ★ [new]** — the proof composes ≥ N non-trivial lemmas, or
  discharges a *stated obstruction*, rather than reducing to a single
  `decide`/`rfl`/`simp` over a finite case.  Operational proxy: proof term
  size, or "remove the key lemma → ≥ K downstream proofs break."
- **Decide-ban for headlines [new]** — a *headline* theorem may not be
  `by decide`-only; finite checks are evidence, not the result.  (Finite
  witnesses are fine as corollaries / sanity instances.)
- **Irredundancy [new]** — the statement is not derivable in one step from
  an existing theorem.  Proxy: it is cited by, or unblocks, work that the
  existing corpus could not reach.

### B. Completeness of the claim
- **Iff / both-directions ★ [implicit]** — a characterization is closed
  only when *both* directions are proved.  The Markov work is the live
  example: §33 (forward) was an analogy until §34 (converse) made it an
  iff (`markovMaxUnique_iff_markovNum_injective`).  A one-directional
  bridge is **open**, not closed.
- **Honest-status ★ [implicit]** — the headline's claimed status
  (theorem / analogy / conjecture / numerical) matches what the Lean
  actually proves.  No "located/explained H" when only an analogy exists.
  (Repo has corrected this exact slip repeatedly — promote it to a gate.)
- **Residual-frontier stated [implicit]** — closing names what stays open
  (the chapter "Open frontier" + a `frontiers/` note), so closure is not
  false finality.  (Now backed by the PROCESS.md frontier-recording rule.)

### C. Significance / connection
- **Reproduction-or-novelty ★ [new]** — the result either (i) reproduces a
  *named* classical theorem (with the classical statement cited), or
  (ii) states a genuinely new equivalence/characterization.  Forces the
  question "what known mathematics does this correspond to, and at what
  axiom cost?"
- **Axiom-cost ledger ★ [new]** — for a reproduction, name the classical
  axioms the standard proof needs (Choice, LEM, completeness, …) and show
  213 pays strictly less.  The *interest* of an `∅`-axiom proof of a
  classically-Choice result IS the reduction; make it explicit.
- **Cross-cluster load-bearing [new]** — bonus weight if the result bridges
  ≥ 2 previously separate sub-trees (matches `07_primacy.md` §7.1:
  primacy = breadth).  A bridge theorem outranks an isolated one.

### D. Canonicality / generality
- **Forced-not-chosen ★ [implicit]** — the construction is shown canonical
  (no exterior dialer; unique up to the Lens-arrow), not one arbitrary
  choice among many.  Matches `05_no_exterior.md` §5.1.
- **Right generality [implicit]** — stated as one structural/parametric
  theorem, not layer-by-layer instance spam (`_at_level_5`, `_layer0..N`).
  Already a CLAUDE.md "smell"; could become a hard gate.
- **Re-derivability [new]** — another agent could re-derive it from
  `seed/` + the stated lemmas; proof obligations are self-contained, no
  appeal to deleted scratch.

## How they might compose (for later)

Sketch, not a proposal: keep H1–H4 + S1–S3 as the **integrity** gate; add
a **seriousness** gate that requires, say, *all of* {honest-status,
iff-completeness-where-applicable, decide-ban-for-headlines} (hard) plus
*at least one of* {reproduction-or-novelty, axiom-cost ledger, G-depth,
cross-cluster} (the "why it matters" clause).  A result that is clean but
trivial passes integrity and fails seriousness → stays a research note,
not a chapter.

## Open questions for the originator
1. Should seriousness be a **hard gate** (blocks promotion) or a **scored
   tag** (recorded, not blocking)?  Hard risks over-gating honest small
   results; scored risks being ignored.
2. Is reproduction-of-classical enough on its own, or must every chapter
   carry a novelty or an axiom-cost claim?
3. Where does the physics DRLT Validation Standard (precision/falsifier)
   sit relative to these — one instance of "reproduction-or-novelty +
   axiom-cost", or its own track?

## If adopted
The decided subset moves into `theory/PROMOTION_CRITERIA.md` as a new
"Seriousness criteria" block (and the physics gate cross-links to it).
Until then this note is the scratchpad; nothing here is binding.
