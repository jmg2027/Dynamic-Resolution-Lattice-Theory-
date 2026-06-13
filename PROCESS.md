# PROCESS.md — directory roles + the dependency discipline

This file codifies what each part of the repository **is for** and the one
rule that keeps the corpus coherent as research turns into permanent record.
It is the canonical statement of the research process; `CLAUDE.md` is the
operating manual that runs it.

## The tiers and their roles

| Directory | Role | Lifetime |
|---|---|---|
| `seed/` | **Canonical foundation** — the axioms (`AXIOM/`), specs, notation, the meta-principle.  The text every other tier presupposes. | Permanent |
| `lean/E213/` | **Formal source of truth** — the ∅-axiom Lean library.  When narrative and Lean disagree, Lean wins. | Permanent |
| `theory/` | **Narrative book** — human-readable exposition, mirrors `lean/E213/Lib/` by path.  One chapter per closed Lean sub-tree. | Permanent |
| `theory/essays/` | **Cross-cutting insight** — derivation-quality answers to 213-concept questions, spanning chapters. | Permanent |
| `catalogs/` | **Derived indices** — constants, precision results, falsifiers, hubs, recursor inventory.  Distilled from the permanent tiers. | Permanent (regenerated) |
| `book/`, `books/` | **Standalone treatises** — long-form readings assembled from the permanent tiers for a specific audience. | Permanent |
| `rust-engine/` | **Numerical companion** — the calculator/search engine; every result points back to a Lean theorem. | Permanent |
| `blueprints/` | **Marathon plans** — forward-looking field plans that seed new work. | Permanent (plan), consumed by frontiers |
| `research-notes/` | **Volatile scratchpad** — the working memory of the research.  `frontiers/` = the live open agenda; `archive/` = record of the path. | **Volatile** |

## The one rule: `research-notes/` is a sink

> **No permanent tier cites a `research-notes/` file.**
> `research-notes/` may cite anything; nothing canonical cites into it.

Rationale: research notes are *volatile* — they get archived, renamed,
consolidated, or deleted as the work matures.  A permanent document
(`seed/`, `lean/`, `theory/`, `catalogs/`, `book/`) that depends on a
scratch file inverts the dependency: the stable thing now rests on the
unstable thing.  The moment a research note carries content a permanent
tier needs, that content must be **promoted** into the permanent tier; the
note then records only the *path*, cited by nothing.

Two things are **not** violations of this rule, because they are not
content-dependencies:

- **Role statements.**  A permanent doc may *describe* `research-notes/`'s
  role ("derivation scratch lives in `research-notes/`", the tier table).
  That names the directory, it does not depend on a file in it.
- **Process tooling.**  The `.claude/skills/` that *operate on*
  `research-notes/` (autonomous-research writes `frontiers/`, handoff reads
  session state) are the machinery of the cycle, not canonical content.

## The companion rule: every open frontier is recorded in `frontiers/`

> **No open frontier lives only in chat, a commit message, or a chapter
> tail.**  Every open problem / conjecture / deferred direction has a note
> under `research-notes/frontiers/<topic>/`, registered in
> `research-notes/frontiers/INDEX.md`.

This is the **opening** side of the cycle; the sink rule is the **closing**
side.  Together they make `research-notes/` the single home of work in
motion: a frontier *enters* as a note here, and the cycle below carries its
content into the permanent tiers once it closes.

Concretely, the instant an open direction is identified — while proving,
auditing, writing a handoff, or thinking out loud — it is recorded as a
frontier note (a new note, or a section under the right topic's note) and
listed in `frontiers/INDEX.md`.  A `theory/` chapter's "Open frontier"
section may *name* the residual work, but the frontier itself **lives** in
`research-notes/frontiers/` where it is tracked and worked — the chapter
section points at the topic group, it does not stand in for it.

Rationale: open frontiers are the research agenda.  Scattered across commit
messages and chat, they cannot be resumed next session; the agenda needs
one durable, discoverable home.  `frontiers/INDEX.md` is that home — the
live board (read it for the current topics).

## The research cycle

```
  blueprints/ (plan)  ─▶  research-notes/frontiers/<topic>/   ── work ──▶  lean/E213/  (∅-axiom closure)
                                                                                │
                                                                                ▼  promote (PROMOTION_CRITERIA.md)
                                                              theory/<mirror> + theory/essays/  +  catalogs/ update
                                                                                │
                          research-notes/archive/<topic>/  ◀───────────────────┘  (source note moves here; cited by nothing)
```

1. A frontier opens as a note under `research-notes/frontiers/<topic>/`
   (see `research-notes/frontiers/INDEX.md`).
2. It closes in `lean/E213/` (∅-axiom, build-green).
3. On closure it is **promoted**: a `theory/` chapter (and/or essay) is
   written, `catalogs/` are updated, and any quantitative result lands in
   `STRICT_ZERO_AXIOM.md` / `catalogs/`.  **All content the permanent tiers
   need now lives in the permanent tiers.**
4. The source note `git mv`s to `research-notes/archive/<topic>/` — kept as
   record of the path, depended on by nothing.

## Promotion = the decoupling step

Promotion (`theory/PROMOTION_CRITERIA.md`, `lean/E213/docs/PROMOTION_PATTERNS.md`)
is precisely the act that satisfies the sink rule: it moves content out of
the volatile tier into a permanent one, so the permanent corpus cites only
permanent tiers.  A promotion is not complete while a permanent document
still points at the research note for content.

## Anchors

Foundational material that the boot sequence and specs rely on (the residue
thesis, the trajectory/lens principles, the semantic atom) lives in `seed/`
and `theory/` — the permanent tiers — never sourced from `research-notes/`.
