#!/bin/bash
# Enforce 80-line chunk limit on Write and Edit tools.
# Blocks any Write/Edit call where the content exceeds 80 lines.
# This prevents context-window death from massive single writes.

TMPFILE=$(mktemp)
cat > "$TMPFILE"
TOOL=$(jq -r '.tool_name // empty' < "$TMPFILE")

if [ "$TOOL" = "Write" ]; then
  LINES=$(jq -r '.tool_input.content // empty' < "$TMPFILE" | wc -l)
elif [ "$TOOL" = "Edit" ]; then
  LINES=$(jq -r '.tool_input.new_string // empty' < "$TMPFILE" | wc -l)
else
  rm -f "$TMPFILE"
  exit 0
fi
rm -f "$TMPFILE"

if [ "$LINES" -gt 80 ]; then
  echo "{\"decision\":\"block\",\"reason\":\"${LINES}줄 감지 (한도 80줄). 더 작은 청크로 나눠서 Write->Edit 반복하세요.\"}"
fi
