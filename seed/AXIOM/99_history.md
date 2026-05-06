# §99. Deprecated R-frame + change history

## §99.A R1-R5 motivation (deprecated, retained for reference)

(Originally AXIOM.md §9 — the naturalness-of-Lens motivation.
Status: **conjecture** at best; the R1-R5 → ℂ derivation chain
has not been re-built post Paper 1 deletion.)

### §99.A.1 The physical question

If the universe is a space where somethings are something among
somethings, and we and the objects of the universe are these
somethings:

> Why do we see the world as **4d spacetime + complex-number
> wave functions**?

Candidate answer: the Lens that most naturally 213-izes the
somethings here to each other is the one that naturally applies.
Then what is that "naturalness"?

### §99.A.2 The principle of naturalness (heuristic)

Candidate definition: **every something being able to have the
same Lens with respect to the axiom**.  That is, the condition
that whichever something is placed as "observer," the way of
seeing the rest must be compatible.

R1–R5 are the **first attempt** to formalize this compatibility
(self-recognising codomain):

- Each Ri captures a necessary condition for "the same Lens
  working regardless of which something is the observer."
- Details in Paper "R1–R5 + ℂ derivation" (after splitting
  Paper 1).

### §99.A.3 Heuristic for 2, 3, d=5

Looking informally at the generation pattern of Raw:

- Start: 2 (a, b).
- Next: from 2 add 1 → 3 (a, b, a/b).
- After that: select from existing N and pair → more somethings.

The **"2 → 1 + previous N"** pattern is observed as the path that
structurally first produces the numbers 2, 3.  d = 2 + 3 = 5
connects to this path.  Rigorization is handled by Paper 1 §5
(atomicity, non-decomposable sizes).

### §99.A.4 Status of this section

R1–R5 records the **motivation/intuition**; it is not a rigorous
derivation.  Current state:

- Paper 1 (`213/PAPER.md`) is **deleted** (see
  `06_formalization.md` §7.2).  R1–R5 motivation no longer has
  an external prose source; the only authoritative formal
  remnant is `lean/E213/Meta/SelfRecognising.lean` (R1–R4
  hierarchy + Bool/ℕ-mod/parity instances).  R5 has not been
  re-formalized in the current Lean tree.
- R1–R5 → ℂ derivation chain has **not** been re-built
  post-deletion.  The current uniqueness story has shifted:
  rather than claiming "R1–R5 uniquely select ℂ," the Lean tree
  now provides the orthogonal Universal-Lens claim
  (`00_nature.md` §1.2: any distinguishability framework factors
  through Raw) and the Atomicity claim (`00_nature.md` §1.3:
  Raw's shape is forced to d=5, (3,2)).  ℂ enters downstream as
  a Lens construction, not as a consequence of an R1–R5 axiom
  set.
- That R1–R5 (or its successor in `Meta/SelfRecognising`) is
  the unique formalization of "naturalness" remains a
  **conjecture**.

If this conjecture is falsified, R1–R5 / `SelfRecognising`
becomes subject to revision.  The Universal-Lens / Atomicity
story does not depend on it.

---

## §99.B Change history (consolidated)

### From AXIOM.md (the corpus)

- **2026-04-24**: Initial writing.  Reflects axiom framing from
  session "claude/lean-infinity-explanation-QqnSp."
- **2026-04-24 (2nd)**: §7.1 reinforced.  Applied
  Recommendations 1, 2 from `AUDIT_Lean.md`.
- **2026-04-24 (3rd)**: Added §8 (self-reference) + §9
  (naturalness, R1–R5 motivation).  Recorded that dichotomies
  like "is Lens inside or outside the axiom?" are mistaken.
- **2026-05-XX**: Major theory-development pass.
  - Added §1.3 "Forced shape uniqueness" —
    `Firmware/Atomicity/*` proofs formalize the third pillar of
    axiom uniqueness (above), alongside §1.1 (below) and §1.2
    (sideways).  Closes the three-direction uniqueness story.
  - §1.1 reinforced with cross-reference to
    `Meta/UniversalLens/` family.
  - §1.2 path corrections: `Research/NoDepthParity.lean` →
    `Hypervisor/Lens/Morphism/{NoDepthParity,DepthParityNotFold}.lean`.
  - §7.1 updated: Lens-layer bleed migration is deprioritized.
  - §7.3, §7.4 obsoleted: `book/chapters/ch22_213.tex` and
    `book/AUDIT.md` no longer exist.
  - §9.4 updated: Paper 1 deletion noted.
  - Companion architectural reference:
    `lean/E213/ARCHITECTURE.md`.

### From IMPLEMENTATION.md

- **2026-04-24**: Initial draft.  Session
  `claude/lean-infinity-explanation-QqnSp`.
- **2026-05-XX**: Path correction (`Math/Hyper/Padic.lean` after
  the Math/Hyper/ sub-cluster split).  No content changes —
  implementation classification (α/β/γ/δ) is unaffected by
  sub-cluster reorganization.

### From AUDIT_Lean.md

- **2026-04-24**: Initial audit.  Session
  `claude/lean-infinity-explanation-QqnSp`.
- **2026-05-XX**: Stale-reference cleanup.  PAPER.md →
  PAPER1.md (archival);
  `Infinity/notes/17_existence_mode_lens.md` →
  `research-notes/17_existence_mode_lens.md`; §3 Steps 3/4
  deprecated (book/, papers/ deleted; superseded by AXIOM corpus
  + guide/ + ARCHITECTURE.md).  Audit verdict (faithful, no
  structural revision) is unchanged.

### From PHILOSOPHY.md / FALSIFIABILITY.md

- Initial drafts written alongside AXIOM.md (2026-04-24).
- **2026-XX-XX**: Both absorbed into the AXIOM corpus
  (`00_nature.md` and `04_falsifiability.md` respectively).
  Original files deleted; content preserved here in the
  chapter structure.

### Corpus-level

- **2026-XX-XX**: 5 seed/ files (`AXIOM.md`, `PHILOSOPHY.md`,
  `FALSIFIABILITY.md`, `IMPLEMENTATION.md`, `AUDIT_Lean.md`)
  integrated into `seed/AXIOM/` chapter sub-directory.
  Authority documents (`ORIGIN.md`, `PAPER1.md`, `NOTATION.md`)
  remain at `seed/` root.  `seed/INDEX.md` rewritten as
  standalone entry point.

## Author & licence

- Author: **Mingu Jeong only**.  Claude in Acknowledgments.
- 0 sorry, 0 external axioms.  Mathlib-free.
