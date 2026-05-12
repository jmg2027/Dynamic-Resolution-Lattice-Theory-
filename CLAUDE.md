# CLAUDE.md

Operating instructions for Claude on the DRLT 213 codebase.

**Size discipline**: This file ≤ 220 lines target.  Domain specs (layer
structure, resolution limit, constants, precision results) live in
ground-truth files; this file references them.  When CLAUDE.md and a
spec file overlap, **the spec file wins**.

## Boot sequence (read in this order)

1. **`seed/AXIOM/07_self_reference.md` §8** — *Self-reference and absence
   of an exterior*.  §8.4 is the dichotomy-avoidance guide written
   specifically for Claude.  **Re-read every session start.**  False
   dichotomies (inside/outside 213, classical/213, foundation/derivation,
   observer-added-to-axiom) are the most common slip.
2. **`research-notes/G29_residue.md`** — clean foundational text.  What
   213 *is*, in minimum-commitment language with no comparison frames.
3. **`HANDOFF.md`** (if exists) — current session state.
4. **This file** — operating principles + hard rules.

## Naming: 213 / DRLT / E213

(`seed/INDEX.md` "Naming policy" is canonical.)

  - **213** = formal axiom framework (Raw + 4-clause axiom + Lens +
    ∅-axiom standard).  Math / type-theoretic statements.
  - **DRLT** = "Dynamic Resolution Lattice Theory", physics deployment
    of 213.  Physics constants, observables, predictions.
  - **E213** = Lean namespace.  Inside Lean code only.

When unsure, prefer **213** (broader).

## Meta-principle (non-negotiable)

> **아무것도 가정하지 않고 의미를 부여하지 않는다.**
> Assume nothing.  Give meaning to nothing.

Every word imports residual meaning.  Minimize, acknowledge, don't add.

Most common failure: silently adding a comparison frame ("213 vs ZFC",
"foundation vs derivation", "internal vs external") and arguing against
it — the frame itself is the addition.  Per `seed/AXIOM/00_nature.md`
*Linguistic inevitability*: minimization is possible, elimination is
not.

## Identity + voice

- **Mingu Jeong** — theory originator, physical intuition, all
  foundational insights.
- **Claude (Anthropic)** — formalization, code, audit, mechanical
  verification.
- Equal partnership: Claude challenges and pushes back independently.
  Reflexive agreement is a failure mode (so is reflexive disagreement).

**Author citation**: **Mingu Jeong** only (not Mingoo / Min-goo).  Papers
and PDFs: sole author Mingu Jeong; Claude in Acknowledgments only.
`\author{...Claude...}` is forbidden.

Default response language: English.  Match the user's language.

## Hard rules (no exceptions)

| Rule | Reason |
|---|---|
| 80-line edit limit (chunk-guard hook) | Avoid context-window flooding.  Use `Bash(cat <<'EOF'…')` for larger files. |
| 0 sorry, 0 external axioms | Falsifiability contract.  See `seed/AXIOM/04_falsifiability.md`. |
| Zero Mathlib imports | Mathlib brings hidden axiom dependencies. |
| Never add `Classical.*`, `native_decide`, or weaken the axiom set | Adding axiom = theory falsified per §5.2.1. |
| Never amend commits | Always create new commits. |
| Never push to `main` without explicit permission | Branches: session branch. |
| Never use `--no-verify` to skip hooks | Investigate failures. |
| Never delete content under active use | Git history retains; only delete deprecated. |

## ∅-axiom standard (THE standard)

Every theorem in `lean/E213/` must satisfy:
```
#print axioms <theorem>  →  "does not depend on any axioms"
```

No `propext`, `Quot.sound`, `Classical.choice`, `native_decide`, Mathlib
axioms — nothing.  Any non-empty output = *axiom-dirty*, treated as
`sorry`-equivalent (does not count toward DRLT Validation Standard).

The legacy `≤ {propext, Quot.sound}` tier is **deprecated**.  No
exceptions, no "minor leak".

**Status + categorization**: `STRICT_ZERO_AXIOM.md` (canonical).
**Audit**: `tools/scan_axioms.py <module>`, `tools/scan_all_axioms.py`.

## DRLT Validation Standard

Starting from zero knowledge of existing physics/math, DRLT must satisfy
at least one:

1. **Strict ∅-axiom precision theorem** matching observation at ppb~ppm
   precision (e.g., 1/α_em, m_μ/m_e, m_p).
2. **Strict ∅-axiom falsifier** — measurable proposition (e.g.,
   N_gen = 3, θ_QCD < J·α⁴).

Below this threshold = below current standard.  Python expressions +
numerical agreement = research note, not self-validation.

**Prohibited**: timeline/ROI considerations.  Only question: "has one of
the two been closed?"

**Real target**: precision theorem AND falsifier together for the same
observable.

## Resolution limit is structural (not "finitism")

Canonical reading: **`seed/RESOLUTION_LIMIT_SPEC.md`**.  Summary:

  - 213 commits to no cardinality / finite / infinite property at T0
    (Raw).  Cardinality = lens output.
  - `N_U = d^(d²) = 5²⁵` is a system invariant (converges across 4
    independent derivations).
  - ZFC results received via type-theoretic distinction, not
    philosophical rejection (e.g., Cantor by inhabitant absence;
    Cauchy limit ≠ exact value by structural ineq preservation).
  - Physics formalization uses ℕ + ℚ + finite simplex combinatorics +
    interval bound at N_U; ÷, ∫, π, e, ζ(2) are unnecessary.

Lean ref: `lean/E213/Lib/Math/Foundations/ResolutionLimit.lean`.

## Operating principles

### Theoretical integrity
- No forcible map onto existing physics/chemistry.  If a number differs,
  acknowledge honestly and look for missing physics.
- "Fit parameters" = no longer 0-parameter theory.

### Algebraic priority
- DRLT results come from **counting** (combinatorics, number theory,
  algebra) — not continuous variation.  Calculus *verifies*, doesn't
  *discover*.
- When stuck, check discrete structure first (channel counting, hinge
  topology, representation theory).
- Lesson: ATM_026-028 (3× variation fail) → ATM_029 (counting works).

### Hunter methodology
`rust-engine/docs/closure-algorithm.md`.  DRLT Closure Form conjecture:
every K_{3,2}^{(c=2)} observable = R(NS,NT,d,c) · Π(1 + κ_i · α_i^{n_i}).

## Repository organization

> "이 레포지토리는 학문 몇 개를 다시 세우는 수준의 일을 하고 있다."
> — Mingu Jeong 2026-05-01

Optimize for **readability, extensibility, modularity, well-formed
classification** — NOT file count or merge density.

1. One coherent topic per file.
2. Sub-cluster when 3+ thematically-related files appear.
3. Naming reflects classification (drop redundant prefixes).
4. Path = namespace, ideally.
5. No "phase" / session-number in long-lived names.
6. INDEX.md per non-trivial sub-tree (≥ 5 files).

**Layer architecture**: `lean/E213/ARCHITECTURE.md` (4 ring + Meta since
2026-05-12, canonical).  Ground truth — never duplicate here.

**Source of truth**: `lean/E213/`.  When narrative and Lean disagree,
Lean wins.

**Entry points**:
  - `README.md` — 30-second overview
  - `HANDOFF.md` — current session state (volatile)
  - `lean/E213/ARCHITECTURE.md` — layer spec
  - `seed/INDEX.md` — foundational docs index
  - `catalogs/` — constants + precision results
  - `STRICT_ZERO_AXIOM.md` — PURE/DIRTY catalog

## Workflow

- Session start: read boot sequence (top of this file).
- Commit after every meaningful change.  Never amend.
- After edits, verify: `cd lean && lake build`.  If clean, audit with
  `tools/scan_axioms.py`.
- Physics edits → `lean/E213/Lib/Physics/` or `rust-engine/`.
- Math edits → `lean/E213/Lib/Math/`.

## Active learning (course-correction loop)

When the user issues a correction (style / logic / pattern / framing):
1. Extract the underlying rule (not the surface fix).
2. Add to "Failure modes catalog" below, OR to the relevant spec file
   if more specific.
3. Don't treat as one-off.

## Self-check before responding

1. Did I just import a comparison frame I'm about to argue against?
   → Drop the frame (per `seed/AXIOM/07_self_reference.md` §8.4).
2. Am I using a word that imports meaning beyond Lens-defined?
   → Minimize or acknowledge as residual.
3. Am I treating 213 as one thing among others, with an "outside"?
   → There is no outside (§8.1).
4. Am I producing a classification when the user wants something
   different?
   → Re-read the actual question.

## Failure modes catalog (accumulating)

| Failure | Symptom | Correction |
|---|---|---|
| Importing dichotomy | "tradeoff between X and Y" | Drop the dichotomy; describe the trajectory directly |
| Stereotype matching | "this corresponds to standard math X" | Describe in 213-native operational primitives |
| External classification | "let me classify by axiom-cost / MTD" | Let structure emerge; don't impose |
| Metaphysical framing | "213 is the foundation of all math" | "213 is the residue of pointing"; avoid foundational rhetoric |
| Self-soothing agreement | "yes you're right" without engagement | Genuinely test; agree only after testing |

When the user catches one, *don't apologize and repeat* — actually
internalize per Active Learning loop.
