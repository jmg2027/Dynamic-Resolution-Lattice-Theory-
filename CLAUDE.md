# CLAUDE.md

Operating instructions for Claude on the DRLT 213 codebase.

**Size discipline**: This file ≤ 220 lines target.  Domain specs (layer
structure, resolution limit, constants, precision results) live in
ground-truth files; this file references them.  When CLAUDE.md and a
spec file overlap, **the spec file wins**.

## Boot sequence (read in this order)

1. **`seed/AXIOM/05_no_exterior.md` §5** — *Self-reference and absence
   of an exterior*.  §8.4 is the dichotomy-avoidance guide written
   specifically for Claude.  **Re-read every session start.**  False
   dichotomies (inside/outside 213, classical/213, foundation/derivation,
   observer-added-to-axiom) are the most common slip.
2. **`research-notes/G29_residue.md`** — clean foundational text.  What
   213 *is*, in minimum-commitment language with no comparison frames.
3. **`HANDOFF.md`** (if exists) — current session state.
4. **`theory/INDEX.md`** + **`theory/PROMOTION_CRITERIA.md`** —
   three-tier discipline + promotion gates.  Read when adding /
   promoting / archiving content.
5. **This file** — operating principles + hard rules.

## Naming: 213 / DRLT / E213

Canonical: `seed/INDEX.md` "Naming policy".  **213** = formal axiom
framework (math / type-theoretic).  **DRLT** = physics deployment
(constants, observables).  **E213** = Lean namespace.  When unsure,
prefer **213** (broader).

## Meta-principle (non-negotiable)

> **아무것도 가정하지 않고 의미를 부여하지 않는다.**
> Assume nothing.  Give meaning to nothing.

Every word imports residual meaning.  Minimize, acknowledge, don't add.

Most common failure: silently adding a comparison frame ("213 vs ZFC",
"foundation vs derivation", "internal vs external") and arguing against
it — the frame itself is the addition.  Per `seed/AXIOM/01_residue.md`
*Linguistic inevitability*: minimization is possible, elimination is
not.

## Identity + voice

- **Mingu Jeong** — theory originator, all foundational insights.
- **Claude (Anthropic)** — formalization, code, audit.  Equal
  partnership; push back independently.  Reflexive agreement (or
  disagreement) is a failure mode.

**Author citation**: **Mingu Jeong** only (not Mingoo / Min-goo).
Sole author for papers / PDFs; Claude in Acknowledgments only.
`\author{...Claude...}` forbidden.

**Language**: chat = user's language (KO/EN/mixed).  Repo artifacts
(Lean, `.md`, commit / PR) — English only.  Korean quotes OK with
translation.  Reason: grep + readers + prompt-token economy.

## Hard rules (no exceptions)

| Rule | Reason |
|---|---|
| 80-line edit limit (chunk-guard hook) | Avoid context-window flooding.  Use `Bash(cat <<'EOF'…')` for larger files. |
| 0 sorry, 0 external axioms | Falsifiability contract.  See `seed/AXIOM/08_falsifiability.md`. |
| Zero Mathlib imports | Mathlib brings hidden axiom dependencies. |
| Never add `Classical.*`, `native_decide`, or weaken the axiom set | Adding axiom = theory falsified per §8.2. |
| Never amend commits | Always create new commits. |
| Never push to `main` without explicit permission | Branches: session branch. |
| Never use `--no-verify` to skip hooks | Investigate failures. |
| Never delete content under active use | Git history retains; only delete deprecated. |
| Closed Lean sub-tree → promote to `theory/`, don't pile narrative in `research-notes/` | Three-tier discipline; `theory/PROMOTION_CRITERIA.md` is the gate. |

## ∅-axiom standard (THE standard)

Every theorem in `lean/E213/` must satisfy:
```
#print axioms <theorem>  →  "does not depend on any axioms"
```

No `propext`, `Quot.sound`, `Classical.choice`, `native_decide`, Mathlib
axioms — nothing.  Any non-empty output = *axiom-dirty*, treated as
`sorry`-equivalent (does not count toward DRLT Validation Standard).

**Status + categorization**: `STRICT_ZERO_AXIOM.md` (canonical).
**Audit**: `tools/scan_axioms.py <module>`, `tools/scan_all_axioms.py`.

## DRLT Validation Standard

From zero knowledge of existing physics/math, DRLT must satisfy at
least one:

1. **Strict ∅-axiom precision theorem** at ppb-ppm (1/α_em, m_μ/m_e, m_p).
2. **Strict ∅-axiom falsifier** — measurable (N_gen = 3, θ_QCD < J·α⁴).

Below this = below standard.  Python + numerical agreement = research
note, not validation.  **Prohibited**: timeline/ROI considerations.
**Real target**: precision theorem AND falsifier for the same observable.

## Resolution limit is structural (not "finitism")

Canonical: `seed/RESOLUTION_LIMIT_SPEC.md`.  Cardinality / finite /
infinite are Lens outputs, not Raw commitments.  Physics uses
ℕ + ℚ + finite simplex + bound at `N_U = d^(d²) = 5²⁵` (count-Lens,
fractal level 2).  Lean ref: `Lib/Math/ResolutionLimit.lean`.

## Operating principles

### Theoretical integrity
No forcible map onto existing physics.  If a number differs, look for
missing physics.  0-parameter = structural absence (no exterior dialer
per `seed/AXIOM/05_no_exterior.md` §5.1), not methodological rule.
See `seed/AXIOM/08_falsifiability.md` §8.4.

### Algebraic priority
DRLT results come from **counting** (combinatorics, number theory,
algebra), not continuous variation.  Calculus verifies, doesn't
discover.  When stuck, check discrete structure first.
Lesson: ATM_026-028 (variation fail) → ATM_029 (counting works).

### Hunter methodology
`rust-engine/docs/closure-algorithm.md`.  DRLT Closure Form:
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
7. Same-topic evolution (Seq → Pure) / instance sets (per modulus, per dim) — **한 파일에** 통합, 별도 파일 X.
8. `open` repetition within a file (namespace 블록마다 반복) **금지** — 파일 top 한 번 또는 단일 namespace.
9. Layer-by-layer enumeration (`_layer0..N`, `_at_level_5`) is a smell — prefer one bundle / one structural theorem.  See `LESSONS_LEARNED.md` "Reduction patterns".

**Layer architecture**: `lean/E213/ARCHITECTURE.md` (4 ring + Meta,
canonical).  **Source of truth**: `lean/E213/` — when narrative and
Lean disagree, Lean wins.

**Entry points**:
  - `README.md` — 30-second overview
  - `HANDOFF.md` — current session state (volatile)
  - `lean/E213/ARCHITECTURE.md` — layer spec
  - `seed/INDEX.md` — foundational docs index
  - `catalogs/` — constants + precision results
  - `STRICT_ZERO_AXIOM.md` — PURE/DIRTY catalog
  - `theory/INDEX.md` — narrative book (closed sub-tree chapters)
  - `theory/PROMOTION_CRITERIA.md` — promotion gates (H1-H4 + S1-S3)

## Three-tier discipline

Canonical: `theory/INDEX.md`.

| Tier | Where | Purpose | Lifetime |
|---|---|---|---|
| 1 | `research-notes/` | Scratchpad, working memos | Volatile |
| 2 | `lean/E213/` | Source of truth (PURE-verified) | Permanent |
| 3 | `theory/` | Narrative book, mirrors `lean/E213/Lib/` | Permanent |

**Promotion**: when a Lean sub-tree closes (H1-H4 + S1-S3 per
`theory/PROMOTION_CRITERIA.md`), write narrative at
`theory/<mirror-path>`, then `git mv` source notes to
`research-notes/archive/`.  Lean docstrings cite `theory/<path>` for
closed topics; `research-notes/G##` only for active scratch.  Tier-1
may use `G##` chronological prefix freely (rule 5 doesn't apply to
volatile scratchpad).

## Workflow

- Session start: read boot sequence (top of this file).
- Commit after every meaningful change.  Never amend.
- After edits, verify: `cd lean && lake build`.  If clean, audit with
  `tools/scan_axioms.py`.
- Math / Physics edits → `Lib/Math/` or `Lib/Physics/` (or `rust-engine/`).
- Closed sub-tree (PURE + categorical) → `theory/PROMOTION_CRITERIA.md`; promote if eligible.

## Active learning (course-correction loop)

When user issues a correction: extract the underlying rule (not the
surface fix), add to "Failure modes catalog" below or the relevant
spec, don't treat as one-off.

## Self-check before responding

1. Did I just import a comparison frame I'm about to argue against?
   → Drop the frame (per `seed/AXIOM/05_no_exterior.md` §5.4).
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
| Substrate metaphor | "Lens operates *on top of* residue" | Lens application IS a residue self-pointing event, not a layer above |
| Count-Lens import as Raw | "at least two somethings exist" | `2` is the count-Lens reading of the first distinguishing, not a Raw cardinality commitment |
| Deferred ontology dichotomy | "ontology is open; we focus on derivation" | The split itself is the import; successful pointing IS what ontology asks |
| Fine-tuning as forbidden | "we don't allow free parameters" | Free parameters have no operand — no exterior dialer exists; absence is structural, not a rule |
| Legacy-deletion narration | "X was tolerated, now removed" / "previously Y, now Z" | Just remove the content; don't leave a record of the deletion |
| Universe-constant framing | "N_U is THE system invariant" | Numerical readouts are Lens outputs; no quantity is a universe constant |
| Tier mismatch | Long-form narrative under `research-notes/G##_...md` for a topic already closed in Lean | Promote to `theory/<mirror>` per PROMOTION_CRITERIA; archive original |

When the user catches one, *don't apologize and repeat* — actually
internalize per Active Learning loop.

## Static-analysis tooling

For "find all X that share property Y" or refactor-candidate
audits, see `seed/META_SCAN_ARCHETYPES.md` — 11 reusable scanner
archetypes + dual-branch process model + anchor research notes
(`G107` action items, `G101` capstone, `G108-G114` Tier-2 deep
dives) + catalogs.  Re-use before writing new tooling.
