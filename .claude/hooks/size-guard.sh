#!/bin/bash
# size-guard: warn when a CLAUDE.md (root or nested) exceeds its size budget.
#
# Per CLAUDE.md "Size discipline" (Mingu Jeong directive 2026-05-12):
# "개별 CLAUDE.md 의 크기를 200줄 이상 하지 않게 하고, CLAUDE.md 에서
# 다른 문서들을 봐 라고 하던가 하이어라키를 알려주던가".
#
# Budgets:
#   - Root CLAUDE.md       ≤ 220 lines (broader scope)
#   - Nested CLAUDE.md     ≤ 200 lines (focused scope)
#
# Domain specs (layer structure, resolution limit, constants, precision
# results) belong in ground-truth files; CLAUDE.md should reference.

TMPFILE=$(mktemp)
cat > "$TMPFILE"
TOOL=$(jq -r '.tool_name // empty' < "$TMPFILE")
PATH_=$(jq -r '.tool_input.file_path // empty' < "$TMPFILE")
rm -f "$TMPFILE"

case "$TOOL" in Write|Edit|MultiEdit) ;; *) exit 0 ;; esac

# Only files named CLAUDE.md (any directory)
[ "$(basename "$PATH_")" = "CLAUDE.md" ] || exit 0
[ -f "$PATH_" ] || exit 0

SIZE=$(wc -l < "$PATH_")

# Budget: root CLAUDE.md = 220, nested CLAUDE.md = 200
REPO_ROOT="${CLAUDE_PROJECT_DIR:-$(git -C "$(dirname "$PATH_")" rev-parse --show-toplevel 2>/dev/null)}"
if [ "$PATH_" = "$REPO_ROOT/CLAUDE.md" ]; then
  BUDGET=220
  KIND="root"
else
  BUDGET=200
  KIND="nested"
fi

if [ "$SIZE" -gt "$BUDGET" ]; then
  REASON="size-guard: ${PATH_#$REPO_ROOT/} = ${SIZE} lines (> ${BUDGET} budget for ${KIND} CLAUDE.md). Delegate domain specs to ground-truth files (ARCHITECTURE.md, seed/*, catalogs/, STRICT_ZERO_AXIOM.md) and reference rather than duplicate. See CLAUDE.md 'Size discipline'."
  echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
fi

exit 0
