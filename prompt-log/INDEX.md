# prompt-log/ — verbatim per-session prompt logs

One file per session, `<date>_<session8>.md`, created on the session's first
prompt by the `UserPromptSubmit` hook (`.claude/hooks/log-prompt.sh`).  Each
file is the verbatim record of the prompts the originator submitted that
session, one numbered entry each.

Purpose: a corpus of the originator's own prompting, kept to review later and
pattern-ize — what kinds of directives recur, what is noise, how the work
gets steered.  Companion to `research-notes/promotion_essay_log.md`.

## Lifecycle

1. **Auto-logged** — the hook appends every submitted prompt, verbatim.  It
   records everything; it cannot tell typed from pasted (the hook API has no
   such signal), so that judgement is deferred to cleanup.
2. **Cleanup on request** — when the originator asks ("프롬프트 정리" / "prompt
   log clean"), the `prompt-log` skill prunes the session file: drop true
   noise and blocks that read as pasted-not-typed (long formatted dumps,
   code/error logs, quoted external text), keep the originator's own typed
   directives.
3. **Commit** — the cleaned file is committed.  Until committed it lives only
   in the ephemeral container, so cleanup + commit happen before session end.

## Not a research tier

These are personal process logs, not `research-notes/` content and not a
permanent tier.  Nothing canonical cites them.
