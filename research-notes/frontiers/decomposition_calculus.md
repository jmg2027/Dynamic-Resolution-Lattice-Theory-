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
Targets chosen to *break/extend* the model, not confirm it:
- **groups / symmetry** — is a group "the construction-preserving readings (automorphisms) of a
  construction"? (tests character-mode as a *family*, not one reading.)
- **probability / measure** — the count-reading *normalized*; does it need a new axis or fit
  `⟨count | resolution⟩`? (a likely model-breaker — good.)
- **homology / the boundary operator** — `∂² = 0` as a residue/character fact? (the repo has cohomology
  Lean: `Cohomology/*`.)
- **the Galois correspondence** — two readings whose fibres mirror (a `LensIso` of two
  construction-families)?
- **ordinals / well-ordering** — fold-height pushed transfinite; where does the finite-signature rule bite?

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
