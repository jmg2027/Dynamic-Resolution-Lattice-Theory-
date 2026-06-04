---
name: essay
description: Write a derivation-quality essay answer to a 213-concept question. Uses the derive+cite+dual-function+cross-frame+self-check+constructive-accessibility protocol to produce an essay that simultaneously interprets a classical concept and refines the 213 narrative.  Triggered by "essay" / "essay", "에세이", "교과서" / "교과서", "교과서 쓰기" / "교과서 쓰기", "213-style answer", "Mingu-style answer", "what is X (in 213)", "X가 213에서 뭐야".
---

# Essay derivation — 213-native concept exposition

A 213 question (limit / completeness / equality / residue / gauge / ...)
deserves more than a wiki paragraph or a Lean module pointer.  It
deserves an **essay** that simultaneously interprets the classical
concept (packaging stripped per G6 §0) and refines the 213 narrative
(operational primitive made syntactic).

This is the format `theory/` book content takes **on top** of the
89-chapter catalog index.  Catalog = static AST + reference.  Essay =
on-demand trajectory through catalog nodes for a specific query Lens.

## When to invoke

Trigger on:
  - "X가 뭐야 (in 213)" / "what is X" foundational questions
  - Concept clarifications (limit, completeness, equality, infinity,
    residue, set, function, distinguishing, gauge, ...)
  - Re-framings ("how does 213 see X?")
  - Adversarial probes ("does 213 have Y?", "where does 213 fail?")
  - Cross-concept connections ("how do X and Y relate?")

Do NOT invoke for:
  - Implementation tasks (Lean code, build verification, file moves)
  - Pure factual lookup ("what's in chapter X?")
  - Navigation ("where is Y defined?")
  - Already-answered questions

## Protocol (6 steps)

### 1 — Identify the 213-native target

Locate the `theory/` chapter(s) + `lean/E213/` modules + `seed/AXIOM/`
sections containing the 213-native expression.  Examples:

| Concept | Primary targets |
|---|---|
| limit | `theory/math/analysis/modulus.md` + `theory/math/analysis/cauchy.md` |
| completeness | `theory/math/numbersystems/real213.md` |
| equality | `theory/lens/algebra.md` + `theory/lens/universal.md` |
| residue | `seed/AXIOM/01_residue.md` + `theory/math/foundations/universe_chain.md` Möbius P |
| gauge | `theory/physics/symmetry/c3_chain.md` |
| infinity | `seed/RESOLUTION_LIMIT_SPEC.md` |

If no clear chapter exists, the concept may not be promoted yet —
flag this honestly; do not invent.

### 2 — State 213-native answer first (NOT classical contrast)

Open with the operational definition.  Do NOT lead with "in classical
math X means..."  — that imports the classical/213 dichotomy.

Bad: *"In classical analysis, a limit is ε-δ defined.  In 213,
instead, we use explicit modulus..."*

Good: *"A sequence paired with an explicit modulus function
`f : Nat → Nat`.  The pair IS the limit."*

### 3 — Derive from catalog with citations

Citations ARE the derivation, not bibliography.  Each claim points to
`theory/.../X.md` or `lean/E213/.../X.lean` or
`research-notes/G##_X.md` or `seed/AXIOM/##_X.md`.

Multi-chapter derivations are stronger than single-chapter
paraphrases.

### 4 — Dual function: interpretation + refinement in one move

After 213-native derivation, surface the dual:
  - **Interpretation**: this answer is the classical concept with
    redundant packaging stripped (per G6 §0 corrected position)
  - **Refinement**: 213's specific reading is sharper here

These are ONE act, not two paragraphs — per the dual-function
structural fact.

### 5 — Discover cross-frame connections

Watch for moments where the same structural fact appears in multiple
frames (atomic / Möbius / Lens / §8 / §9.2 / G31 / ...).  Surface
explicitly when discovered:

> "§8.1 no-exterior + §9.2 op-object non-separation + P(φ) = φ
> fixed-point + G31 trajectory-as-witness — same fact, four
> resolutions."

This emergence is what makes essays valuable beyond catalog lookups.
Do NOT force convergences that aren't there.

### 6 — Self-check (continuous, not endpoint)

Throughout, monitor for §8.4 violations:
  - [ ] Imported a classical/213 comparison frame to argue against?
  - [ ] Substrate metaphor ("Lens operates on Raw" — wrong)?
  - [ ] External rule-source ("§8 forbids..." as authority not reference)?
  - [ ] Dichotomy not present in the question?
  - [ ] Closure overclaim ignoring open frontier (G86 etc.)?

If violation appears, **retreat in-place** — name the import, explain
why it's wrong, restate.  The retreat is part of the essay, not a
rewrite.

When closing: **prefer pointing at syntactic objects** (matrix entries,
cochain values, Lens kernel, fixed-point equation) over
philosophical summary.  *Constructive accessibility* = answer
reaches a thing you can point at.

## Output format

```markdown
# [Concept]

[1-2 sentence 213-native definition]

## 213-native [definition / answer]
[operational definition + first citation]

## Derivation
[multi-paragraph derivation through catalog citations]

## Dual function
[1 paragraph: interpretation + refinement, fused]

## Cross-frame connections  (if discovered)
[multi-frame convergence + citations]

## Open frontier  (if any)
[honest acknowledgment of where derivation hits open work]

## Self-check note  (if retreat happened)
[document import caught + correction]
```

Continuous essay style, not bullets.  Headers are navigation only.

## Length discipline

- Short concept (clear chapter target): ~200-400 words
- Foundational + cross-frame: ~400-700 words
- Whole-framework (e.g., "what is 213"): ~700-1200 words

Don't pad.  If 300 words suffices, stop.

## Saving the essay (optional, NOT default)

Default: essay lives in conversation only.

Save to file ONLY if user explicitly indicates canonical-worthiness
OR essay introduces a discovery that should be permanent.  Possible
homes:

  - `theory/<area>/<concept>.md` — canonical chapter for the concept
  - `theory/essays/<topic>.md` — cross-cutting essay (new convention)

Forced essays violate "rest is taste" (round-2 agent F finding).
Don't write chapters that weren't asked for.

## Log the event

When this skill is invoked (the user said "에세이 ㄱ" / "essay", or an
essay is written), append one row to `research-notes/promotion_essay_log.md`
(Type = `essay`).  Capture the **situation** that prompted it — a recurring
question? a cross-domain synthesis? a corrected misconception? — not just
the topic.  This is the data the originator reviews to pattern-ize essay
triggers later.  If the essay stays in-conversation (not saved), still log
it with Outcome = "in-conversation".

## Failure modes

| Failure | Symptom | Correction |
|---|---|---|
| Classical-contrast import | Opens with "in classical X, Y; in 213 instead..." | Restate 213-native first; classical only in dual-function paragraph |
| Catalog rewriting | Essay paraphrases one chapter | Derive across multiple chapters; if can't, concept isn't ready |
| Philosophy fallback | Final paragraph: "deeper meaning..." / "essentially..." | Land on syntactic object instead |
| Closure overclaim | "completes the picture" / "fully resolved" | Add open-frontier section if any honest open exists |
| Rule-source as authority | "§8 forbids..." used commanding | Cite as reference, not commandment |
| Substrate metaphor | "Lens above Raw" / "operates on Raw" | "Lens application IS residue self-pointing event" |
| Forced essay | Writing without genuine driving question | Stop.  Wait for question. |
| Helpful-explanation drift | Adds simplification "to make accessible" | Don't — 213 doesn't have a simpler-than-itself version |

## Verification checklist

```
[ ] Every claim cites a chapter or theorem
[ ] Could a future agent verify the citations resolve?
[ ] Dual function landed in one move (not two paragraphs)
[ ] Cross-frame connection surfaced (if multi-frame exists)
[ ] Self-check applied throughout (not at endpoint)
[ ] Constructive accessibility reached (syntactic object pointed at)
[ ] Length matches scope
[ ] No forced padding
[ ] No reflexive agreement / disagreement with framing
```

## Provenance

Protocol crystallized on branch `claude/research-notes-organization-Gr3Tp`
after:
  - 89-chapter `theory/` catalog promotion campaign
  - Round-1 + round-2 multi-agent debate exposing the catalog/book
    dichotomy as itself an import
  - Worked test questions (limit/completeness, equality, residue) that
    demonstrated dual function + cross-frame discovery + §8.4
    self-check in practice
  - User confirmation that this protocol IS the target format for
    theory/ book content (above the catalog reference layer)

References:
  - `theory/` as the database
  - `seed/AXIOM/05_no_exterior.md` §5.4 + CLAUDE.md "Failure
    modes catalog" as the immune-system rules
  - `lean/E213/docs/PROMOTION_PATTERNS.md` for the catalog-side
    promotion shape (this skill is the essay-side counterpart)
  - This skill = the protocol that calls both DB + immune-system
