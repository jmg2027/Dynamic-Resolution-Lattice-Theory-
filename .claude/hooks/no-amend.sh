#!/bin/bash
# CLAUDE.md: "절대 amend 안 함" — block git commit --amend / push --force.

TMPFILE=$(mktemp)
cat > "$TMPFILE"
TOOL=$(jq -r '.tool_name // empty' < "$TMPFILE")
CMD=$(jq -r '.tool_input.command // empty' < "$TMPFILE")
rm -f "$TMPFILE"

[ "$TOOL" = "Bash" ] || exit 0

if echo "$CMD" | grep -qE 'git[[:space:]]+commit[[:space:]].*--amend'; then
  echo "{\"decision\":\"block\",\"reason\":\"CLAUDE.md: 절대 amend 안 함. 새 커밋 만드세요.\"}"
  exit 0
fi

if echo "$CMD" | grep -qE 'git[[:space:]]+push[[:space:]].*(--force|-f([[:space:]]|$))'; then
  echo "{\"decision\":\"block\",\"reason\":\"force push 차단. 정말 필요하면 사용자 명시 승인 후 hook 우회.\"}"
fi
