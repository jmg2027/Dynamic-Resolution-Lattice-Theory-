# §99. Deprecated R-frame + change history

## §99.A Naturalness of Lens choice (deprecated R1–R5 frame)

### §99.A.0 Status (post-cleanup)

This section originally introduced the **R1–R5 judgment-game
frame** as a "naturalness" criterion for Lens choice.  That frame
has been **stepped back from** (per
`research-notes/archive/30_bool_is_liar_paradox.md`: R1–R5 was
revealed to be a self-reference loop on Bool, so the frame itself
fell).

The current uniqueness story does NOT route through R1–R5:

  - **Universal-Lens claim** (`00_nature.md` §1.2): any
    distinguishability framework factors through Raw.  No R-game
    required.
  - **Atomicity claim** (`00_nature.md` §1.3): Raw's shape is
    forced to d=5, (3,2) structurally — see
    `Theory/Atomicity/Five.lean` and the related Atomicity
    cluster.
  - **Resolution-limit family readout**
    (`seed/RESOLUTION_LIMIT_SPEC.md` §2 — G120 Round 3 rewrite):
    `configCount 2 = 5²⁵` as one value of the parametric Lens-output
    family `configCount : Nat → Nat`.  Historical "4-way convergent
    invariant" framing was retracted (only 2 of 4 readings had
    real Lean derivations).

ℂ enters downstream as a Lens construction
(`Lib/Math/CayleyDickson/`), NOT as a consequence of any R1–R5
axiom set.

### §99.A.1 Lean remnant — renamed (2026-05-05 audit pass)

The typeclass hierarchy in
`lean/E213/Meta/SelfRecognising.lean` was renamed to drop the
historical R-prefix while preserving semantics:

| Before (historical R-frame) | After (descriptive)        |
| ---                          | ---                        |
| `R12Codomain`                | `CommBinaryCodomain`       |
| `R3Codomain`                 | `NonVanishingCodomain`     |
| `R4Codomain`                 | `ConjugationCodomain`      |

Companion macros and tactics renamed in lockstep:

| Before                       | After                         |
| ---                          | ---                           |
| `derive_r4_codomain`         | `derive_conjugation_codomain` |
| `#verify_r4`                 | `#verify_conjugation`         |
| `Meta/Tactic/DeriveR4Codomain.lean` | `DeriveConjugationCodomain.lean` |
| `Meta/Tactic/VerifyR4.lean`  | `VerifyConjugation.lean`      |
| `Meta/Tactic/Test/VerifyR4Test.lean` | `VerifyConjugationTest.lean` |
| `r4_conj_*` (CUniquenessBridge) | `conjugation_*`            |
| `ZSqrt.R4_of_pos`            | `ZSqrt.conjugation_of_pos`    |

The *content* (commutative combine, no-zero-divisors, swap-matching
involution) is independent of the deprecated R1–R5 frame and is
used as a generic codomain spec.  Five files consume it
(CayleyDickson Z2/ZOmega/ZI/ZSqrt instances + CUniquenessBridge);
all updated.  Build clean, axiom scan unchanged.

### §99.A.2 Removed content

Earlier subsections ("physical question", "principle of
naturalness", "heuristic for 2,3,d=5", "status") have been
removed.  The motivation they expressed is preserved in the
archive note `research-notes/archive/30_bool_is_liar_paradox.md`
(historical record only).

The Universal-Lens + Atomicity + Resolution-limit triad replaces
R1–R5 as the canonical uniqueness story.

---

## §99.B Change history (consolidated)

### From AXIOM.md (the corpus)

- **2026-04-24**: Initial writing.  Reflects axiom framing from
  session "claude/lean-infinity-explanation-QqnSp."
- **2026-04-24 (2nd)**: §7.1 reinforced.  Applied
  Recommendations 1, 2 from `AUDIT_Lean.md`.
- **2026-04-24 (3rd)**: Added §8 (self-reference) + §9
  (naturalness, R1–R5 motivation; later deprecated — see
  2026-05-XX).  Recorded that dichotomies like "is Lens inside or
  outside the axiom?" are mistaken.
- **2026-05-XX**: Major theory-development pass.
  - Added §1.3 "Forced shape uniqueness" —
    `Theory/Atomicity/*` proofs formalize the third pillar of
    axiom uniqueness (above), alongside §1.1 (below) and §1.2
    (sideways).  Closes the three-direction uniqueness story.
  - §1.1 reinforced with cross-reference to
    `Meta/UniversalLens/` family.
  - §1.2 path corrections: `Research/NoDepthParity.lean` →
    `Lens/Morphism/{NoDepthParity,DepthParityNotFold}.lean`.
  - §7.1 updated: Lens-layer bleed migration is deprioritized.
  - §7.3, §7.4 obsoleted: legacy `book/chapters/ch22_213.tex` and
    `book/AUDIT.md` no longer exist.
  - §9 substantially rewritten as "deprecated R1–R5 frame": the
    R-game judgment frame is stepped back from.  The current
    uniqueness story is Universal-Lens + Atomicity +
    Resolution-limit (`configCount` parametric family; G120 Round 3
    retracted "4-way invariant N_U" framing).
- **2026-05-05**: §9.1 typeclass rename executed.
  `Meta/SelfRecognising.lean`'s `R12Codomain` / `R3Codomain` /
  `R4Codomain` → `CommBinaryCodomain` / `NonVanishingCodomain` /
  `ConjugationCodomain`.  Companion macros, tactics, filenames,
  theorem prefixes (`r4_conj_*` → `conjugation_*`) renamed in
  lockstep across 16 files.  Build clean, axiom scan unchanged.
  - Companion architectural reference:
    `lean/E213/ARCHITECTURE.md`.

### From IMPLEMENTATION.md

- **2026-04-24**: Initial draft.  Session
  `claude/lean-infinity-explanation-QqnSp`.
- **2026-05-XX**: Path corrections (`Lib/Math/Hyper/Padic.lean`
  after the Math/Hyper/ sub-cluster split).  No content
  changes — implementation classification (α/β/γ/δ) is
  unaffected by sub-cluster reorganization.

### From AUDIT_Lean.md

- **2026-04-24**: Initial audit.  Session
  `claude/lean-infinity-explanation-QqnSp`.
- **2026-05-XX**: Stale-reference cleanup.  PAPER.md →
  PAPER1.md (later deleted 2026-05-12);
  `Infinity/notes/17_existence_mode_lens.md` →
  `research-notes/archive/17_existence_mode_lens.md`; §3 Steps
  3/4 deprecated (book/, papers/ deleted; superseded by AXIOM
  corpus + guide/ + ARCHITECTURE.md).  Audit verdict (faithful,
  no structural revision) is unchanged.

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
  Authority documents (`ORIGIN.md`, `RESOLUTION_LIMIT_SPEC.md`,
  `NOTATION.md`) remain at `seed/` root.  (`PAPER1.md` later
  deleted 2026-05-12.)  `seed/INDEX.md` rewritten as standalone entry point
  (4-clause axiom + key concepts + falsifiability rule visible
  in one screen).

## Author & licence

- Author: **Mingu Jeong only**.  Claude in Acknowledgments.
- 0 sorry, 0 external axioms.  Mathlib-free.
