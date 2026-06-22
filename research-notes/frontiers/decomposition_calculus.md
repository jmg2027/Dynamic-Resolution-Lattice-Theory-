# Frontier: the 213 Decomposition Calculus

**Status**: open, active — the originator's recalibrated central program (2026-06-22). The body of the
repository is *this* (a human-facing technique for *seeing* mathematics cleanly via the single act of
distinguishing), not the Lean re-derivation corpus (scaffolding). Spec + practice live in
`research-notes/decomposition/` (`README.md` = the technique; `practice/` = worked decompositions).
Lean is the faithfulness-check only.

## State (11 worked decompositions, all Lean-cited)

Crystallized-from-repo: `parity`, `integers`, `equivalence`. Fresh batch 1: `prime_factorization`,
`cardinality`, `dimension`, `derivative`. Fresh batch 2: `determinant`, `golden_ratio`, `exponential`,
`continuity`. The practice has refined the model twice (see `README.md` "Refinements"):
`C` = distinguishing + {direction, fold-height, atom-distinguishability}; `L` = a reading +
{resolution (→ a discipline when made a condition), bidirectional character-mode}; `Residue` = `L`'s
self-application surplus, tagged `q = ±1` (escape/oscillate vs converge/fixed-point).

## Open directions

### Next fresh decompositions (the practice is the research)
DONE (batch 3, both EXTEND, no break): **groups** (a group = `⟨C | Aut C closed under composition⟩`,
axioms forced — readings form a composition-closed family); **probability** (`P = ratio∘count`, first
*composite* reading; `L` gains a `weight` parameter; independence = ×-character, expectation = its
additive twin). Lesson: **readings form a category.** Remaining targets (chosen to *break/extend*):
- **homology / the boundary operator** — `∂² = 0` as a residue/character fact? (repo `Cohomology/*`.)
- **the Galois correspondence** — two readings whose fibres mirror (a `LensIso` of two `Aut`-families)?
  (now sharper post-`groups.md`: Galois = an iso of two composition-closed reading-families.)
- **ordinals / well-ordering** — fold-height pushed transfinite; where does the finite-signature bite?
- **information / entropy** — a weighted count-reading's *residue* (probability.md's `weight` × log-character)?

### Open Lean faithfulness-targets (would certify a current prose-only collapse)
- `continuous_iff_preimage_dyadicopen` (`continuity.md` flags the open-set/preimage leg as prose).
- a formal **`q = ±1` residue tag** uniting `object1_not_surjective` (escape, `q=−1`) and the φ Cassini
  law `cassini_law_one_at_two_multipliers` (converge, `q=+1`) — the calculus's deepest collapse, not
  yet one theorem.
- `exp/log` continuous inverse `cutExp ∘ cutLog = id` (`exponential.md` flags it open; discrete side
  certified via `vp_self_pow`/`pow_eq_pow_iff_vp`).

### Technique-spec questions still live
- Does "character" deserve a formal definition object (a reading whose readout is a number-construction
  with `C`'s direction+height)? Candidate to crystallize once 2–3 more character instances land.
- Is `resolution` better modeled as a single dial or a poset of resolutions (discrete < dyadic <
  Cauchy < …)? `continuity.md` + `ResolutionShift.lean` (graded monoid) suggest a poset.

### The standing guard (re-skin test)
Every decomposition must end in a **Revelation** (collapse / forcing / residue-surfaced); a
decomposition that only re-describes is dropped. This is the same bar that separated category theory
from "abstract nonsense" — the technique must *pay*, eventually as a tool or a result, not just a
re-seeing. Tracked against CLAUDE.md's failure-mode catalog (the negative of this technique).
