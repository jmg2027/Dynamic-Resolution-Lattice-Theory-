---
name: prompt-log
description: Clean the current session's verbatim prompt log (prompt-log/<date>_<session8>.md) — prune true noise and blocks that read as pasted-not-typed, keep the originator's own typed directives, then commit. The log is written automatically by the UserPromptSubmit hook; this skill is the human-triggered cleanup. Triggered by "프롬프트 정리", "프롬프트 로그 정리", "prompt log clean", "clean prompt log", "정리 프롬프트".
---

# prompt-log — session prompt-log cleanup

The `UserPromptSubmit` hook (`.claude/hooks/log-prompt.sh`) records every
submitted prompt verbatim into `prompt-log/<date>_<session8>.md`.  This skill
is the cleanup the originator triggers at session end.

**Honest limit:** the hook cannot tell typed from pasted — it logs the final
text only.  So "pasted-not-typed" is a *heuristic judgement made here*, not a
tag.  When unsure, keep + flag rather than delete silently.

## Procedure

### 1 — Find the session's log file
```bash
ls -t prompt-log/*.md | grep -v '/INDEX.md' | head -1   # most-recent session file
```
Confirm it is this session's (date + session-id prefix).  If none exists, the
hook has not fired yet this session (it applies from the session after it was
installed / on reload) — say so and stop.

### 2 — Classify each `### N` entry
- **Keep** — the originator's own typed directives, questions, decisions
  (including terse ones like "ㄱㄱ" / "푸시" — those are real instructions).
- **Prune — noise** — accidental fragments, dead typos, exact duplicates,
  empty-ish entries with no directive content.
- **Prune — pasted (non-typed)** — long formatted blocks that read as copied
  in rather than typed: code dumps, stack traces / error logs, quoted
  external text, tables, multi-paragraph specs.  Heuristics (length, code
  fences, log/JSON shape, quoting).  Ambiguous → keep and mark with a
  trailing `<!-- review: pasted? -->` rather than delete.

### 3 — Prune + renumber
Edit the file: remove the pruned entries, renumber the survivors `### 1..k`
so the cleaned log reads cleanly.  Preserve each kept entry verbatim.

### 4 — Report + commit
Report counts: kept / noise-pruned / paste-pruned / flagged-uncertain.
```bash
git add prompt-log/ && git commit -m "prompt-log: clean session <session8> (<k> kept, <n> pruned)

https://claude.ai/code/<session-url>"
```
(Do not push to `main` without explicit permission — push the session branch.)

## Pattern-ize later
Once several cleaned logs accumulate, scan for recurring directive shapes
(what the originator asks for repeatedly, what gets corrected) and feed
findings into CLAUDE.md / the relevant skill — the same review loop as
`research-notes/promotion_essay_log.md`.
