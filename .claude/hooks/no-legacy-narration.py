#!/usr/bin/env python3
"""PreToolUse hook — block legacy-deletion narration and G## session-tags
in promoted body content of .md / .lean files.

CLAUDE.md failure-modes catalog ("Legacy-deletion narration") and the
"No phase/session-number in long-lived names" rule forbid:

  1. Change narration in body prose — "archived", "promoted", "previously",
     "was renamed", "formerly", "no longer needed", "moved to `...`",
     "deprecated".  Just present the current state, do not record the
     transition.

  2. G## (session-number) tags in promoted-theory contexts — theory/*,
     seed/*, and lean/E213/*.lean docstrings.  If the narrative reads
     incomplete without the G## tag, that signals genuine narrative
     deficiency: write proper exposition instead of pointer-style refs.

Exempt files (historical / index / volatile scratch — these need the
transition vocabulary):

  · research-notes/**           (volatile scratchpad)
  · HANDOFF.md                  (session state)
  · CAPSTONE_INDEX.md           (capstone history)
  · STRICT_ZERO_AXIOM.md        (PURE/DIRTY history table)
  · LESSONS_LEARNED.md          (patterns / antipatterns)
  · LEAN_FILE_SUMMARY.md        (audit log)
  · BRANCH_MERGE_GUIDE.md       (merge protocol)
  · README.md                   (top-level overview)
  · CLAUDE.md                   (operating doc — explains the rules)
  · theory/INDEX.md             (promotion log)
  · seed/INDEX.md, seed/AXIOM/INDEX.md
  · lean/E213/ARCHITECTURE.md   (architecture log mentions G105)
  · lean/E213/AUDIT.md
  · .claude/**                  (hook scripts, settings)
"""

import json
import os
import re
import sys

NARRATION_PATTERNS = [
    (re.compile(r"\(\s*archived\b", re.IGNORECASE),    "(archived)"),
    (re.compile(r"\(\s*promoted\b", re.IGNORECASE),    "(promoted)"),
    (re.compile(r"\(\s*deprecated\b", re.IGNORECASE),  "(deprecated)"),
    (re.compile(
        r"\b(was|were|has been|have been|is now|are now)\s+"
        r"(archived|promoted|removed|renamed|moved|deprecated|"
        r"superseded|absorbed)\b", re.IGNORECASE),
     "was/were/has been + archived/promoted/removed/etc."),
    (re.compile(r"\bpreviously\s+(was|named|called|located|known|defined|used)\b",
                re.IGNORECASE),
     "previously was/named/called/located"),
    (re.compile(r"\bformerly\b", re.IGNORECASE),       "formerly"),
    (re.compile(r"\bno longer\s+(needed|required|used|exists|valid|relevant|present|available)\b",
                re.IGNORECASE),
     "no longer needed/required/used/etc."),
    (re.compile(r"\bnow removed\b", re.IGNORECASE),    "now removed"),
    (re.compile(r"\bdeprecated\b", re.IGNORECASE),     "deprecated"),
    (re.compile(r"\bmoved to\s+`", re.IGNORECASE),     "moved to `path`"),
    (re.compile(r"\b(was|were)\s+renamed\b", re.IGNORECASE),
     "was/were renamed"),
    (re.compile(r"\b(was|were)\s+merged\s+(into|from|with)\b", re.IGNORECASE),
     "was/were merged into/from/with"),
]

GTAG_RE = re.compile(r"\bG\d{2,3}\b")

EXEMPT_EXACT = {
    "HANDOFF.md",
    "CAPSTONE_INDEX.md",
    "STRICT_ZERO_AXIOM.md",
    "LESSONS_LEARNED.md",
    "LEAN_FILE_SUMMARY.md",
    "BRANCH_MERGE_GUIDE.md",
    "README.md",
    "CLAUDE.md",
    "theory/INDEX.md",
    "seed/INDEX.md",
    "seed/AXIOM/INDEX.md",
    "seed/AXIOM/99_history.md",
    "lean/E213/ARCHITECTURE.md",
    "lean/E213/AUDIT.md",
}

EXEMPT_PREFIX = (
    "research-notes/",
    ".claude/",
    "tools/",  # audit / scan scripts
    ".github/",
    "prompt-log/",  # verbatim user prompts — carry whatever the user typed
)


def _project_relative(path: str) -> str:
    """Return path relative to project root (best effort).

    The hook receives whatever path Claude used: absolute, relative, or
    relative-with-CLAUDE_PROJECT_DIR prefix.  We strip the project-root
    prefix when present so matching keys (e.g. "HANDOFF.md",
    "theory/INDEX.md") work uniformly.
    """
    root = os.environ.get("CLAUDE_PROJECT_DIR", os.getcwd())
    root = os.path.realpath(root)
    p = os.path.realpath(path) if path else ""
    if p.startswith(root + "/"):
        return p[len(root) + 1:]
    return path.lstrip("./")


def is_exempt(path: str) -> bool:
    rel = _project_relative(path)
    if rel in EXEMPT_EXACT:
        return True
    return any(rel.startswith(pfx) for pfx in EXEMPT_PREFIX)


def applies_narration(path: str) -> bool:
    return path.endswith(".md") or path.endswith(".lean")


def applies_gtag(path: str) -> bool:
    rel = _project_relative(path)
    in_theory = rel.startswith("theory/") and rel.endswith(".md")
    in_seed = rel.startswith("seed/") and rel.endswith(".md")
    in_lean = rel.startswith("lean/") and rel.endswith(".lean")
    return in_theory or in_seed or in_lean


def collect_new_content(tool_name: str, tool_input: dict) -> list:
    """Extract the additive content from the tool call."""
    if tool_name == "Write":
        return [tool_input.get("content", "") or ""]
    if tool_name == "Edit":
        return [tool_input.get("new_string", "") or ""]
    if tool_name == "MultiEdit":
        return [e.get("new_string", "") or "" for e in tool_input.get("edits", [])]
    if tool_name == "NotebookEdit":
        return [tool_input.get("new_source", "") or ""]
    return []


def _snippet(text: str, m: re.Match, pad: int = 24) -> str:
    s = max(0, m.start() - pad)
    e = min(len(text), m.end() + pad)
    return text[s:e].replace("\n", " ⏎ ").strip()


def scan(text: str, path: str) -> list:
    findings = []
    if applies_narration(path):
        for rx, label in NARRATION_PATTERNS:
            m = rx.search(text)
            if m:
                findings.append((label, _snippet(text, m)))
    if applies_gtag(path):
        for m in GTAG_RE.finditer(text):
            findings.append(("G## session-tag", _snippet(text, m)))
    return findings


def deny(reason: str) -> None:
    out = {
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        }
    }
    sys.stdout.write(json.dumps(out))
    sys.stdout.flush()
    sys.exit(0)


def main() -> None:
    try:
        payload = json.loads(sys.stdin.read())
    except Exception:
        sys.exit(0)

    tool_name = payload.get("tool_name", "")
    tool_input = payload.get("tool_input", {}) or {}

    if tool_name not in ("Write", "Edit", "MultiEdit", "NotebookEdit"):
        sys.exit(0)

    file_path = tool_input.get("file_path") or tool_input.get("notebook_path") or ""
    if not file_path:
        sys.exit(0)
    if not applies_narration(file_path):
        sys.exit(0)
    if is_exempt(file_path):
        sys.exit(0)

    findings = []
    for chunk in collect_new_content(tool_name, tool_input):
        if chunk:
            findings.extend(scan(chunk, file_path))

    if not findings:
        sys.exit(0)

    # Deduplicate by (label, snippet)
    seen = set()
    unique = []
    for f in findings:
        if f not in seen:
            seen.add(f)
            unique.append(f)

    lines = [
        "Blocked: legacy-deletion narration or G## session-tag in body content.",
        "",
        "Per CLAUDE.md failure-modes catalog ('Legacy-deletion narration')",
        "and Repository organization rule 5 ('No phase/session-number in",
        "long-lived names'):",
        "",
        "  · Do not write change vocabulary (archived, promoted, previously,",
        "    formerly, deprecated, moved, renamed, superseded) in .md/.lean",
        "    body content.  Just present the current state.",
        "",
        "  · Do not reference G## session tags in theory/*, seed/*, or",
        "    lean/**.lean.  If the narrative feels thin without the tag,",
        "    that is narrative deficiency — write proper exposition.",
        "",
        "Exempt files (allowed to carry transition vocabulary / G##):",
        "  research-notes/**, HANDOFF.md, CAPSTONE_INDEX.md,",
        "  STRICT_ZERO_AXIOM.md, LESSONS_LEARNED.md, LEAN_FILE_SUMMARY.md,",
        "  BRANCH_MERGE_GUIDE.md, README.md, CLAUDE.md, *INDEX.md,",
        "  lean/E213/ARCHITECTURE.md.",
        "",
        f"File: {_project_relative(file_path)}",
        "Hits:",
    ]
    for label, snippet in unique[:12]:
        lines.append(f"  · {label}  …{snippet}…")
    if len(unique) > 12:
        lines.append(f"  · … and {len(unique) - 12} more")

    deny("\n".join(lines))


if __name__ == "__main__":
    main()
