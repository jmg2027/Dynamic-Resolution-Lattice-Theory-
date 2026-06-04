# Promotion / Essay event log

Append-only ledger of **promotion-ㄱ** and **essay-ㄱ** triggers, so the
originator can review *when* and *why* these happen across sessions and
later decide whether the situations pattern-ize (→ a heuristic, a gate, or
an automated trigger).

This is a volatile process ledger (tier-1).  No permanent tier cites it.
It is reviewed by a human, not consumed by the build.

## How to append (for every future session)

When the originator says **"프로모션 ㄱ"** (promote) or **"에세이 ㄱ"**
(essay) — or the `process` / `essay` skill runs a promotion/essay — add one
row.  Capture the *situation*, not just the artifact: what had just
happened that made promotion/essay feel right at that moment.  Newest at
the bottom.

| # | Date | Type | Topic / target | Situation (what prompted it — the pattern-able signal) | Outcome (path) |
|---|------|------|----------------|--------------------------------------------------------|----------------|

Columns:
- **Type** — `promotion` (Lean sub-tree → `theory/` chapter) or `essay`
  (cross-cutting question → `theory/essays/`).
- **Situation** — the trigger context: a sub-tree just closed `∅`-axiom?
  an iff finally completed both directions?  a question kept recurring in
  chat?  a cross-domain pattern became visible?  This column is the point
  of the log.
- **Outcome** — the chapter/essay path written (or "deferred — reason").

## Log

| # | Date | Type | Topic / target | Situation (what prompted it) | Outcome (path) |
|---|------|------|----------------|------------------------------|----------------|
| 1 | 2026-06-04 | essay | The counting bound behind two representation theorems (disc−3 `a²−ab+b²` + disc−4 `a²+b²`) | Two representation iffs closed ∅-axiom in one session by the *same* field-agnostic engine (`RootBound.eval_zero` + `centered_div`); the cross-domain reuse (one Lagrange bound, two exponents/radii) was the synthesis worth naming. `/essay` invoked at session end. | in-conversation |

## Reading the log later (pattern analysis)

Once there are ~10+ rows, look for:
- **Recurring situations** → a candidate *promotion trigger* (e.g. "every
  time an iff closes both directions, promotion follows" → make iff-closure
  the trigger).
- **Essay triggers** → which kinds of questions become essays (recurring
  chat question?  cross-domain synthesis?  a corrected misconception?).
- **Lag** → how long a sub-tree stays closed-but-unpromoted; a long lag
  suggests the promotion gate or the prompt is the bottleneck.
- Feed findings into `frontiers/research_grade_closure_gate.md` and, if
  stable, into `theory/PROMOTION_CRITERIA.md` / the `process` skill.
