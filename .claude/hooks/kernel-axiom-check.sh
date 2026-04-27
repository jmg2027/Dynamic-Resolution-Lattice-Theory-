#!/bin/bash
# 213 Kernel axiom regression: PostToolUse 에 한정 실행.
#
# Kernel 파일이 변경되었을 때 lake build + #print axioms 검사.
# 어떤 kernel 정리가 axiom 을 의존하면 차단.

TMPFILE=$(mktemp)
cat > "$TMPFILE"
TOOL=$(jq -r '.tool_name // empty' < "$TMPFILE")
PATH_=$(jq -r '.tool_input.file_path // empty' < "$TMPFILE")
rm -f "$TMPFILE"

# Only Write/Edit
case "$TOOL" in Write|Edit) ;; *) exit 0 ;; esac

# Only kernel files
case "$PATH_" in
  */lean/E213/Kernel/*.lean) ;;
  *) exit 0 ;;
esac

# Run regression script (already exists)
REPO_ROOT="${CLAUDE_PROJECT_DIR:-$(git -C "$(dirname "$PATH_")" rev-parse --show-toplevel 2>/dev/null)}"
SCRIPT="$REPO_ROOT/tools/kernel_regress.sh"

if [ ! -x "$SCRIPT" ]; then
  exit 0
fi

OUT=$("$SCRIPT" 2>&1)
if echo "$OUT" | grep -q "REGRESSION"; then
  REASON="Kernel axiom regression: $(echo "$OUT" | grep -E 'depends on axioms' | head -3 | tr '\n' ' ')"
  echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
  exit 0
fi

# success — silent
exit 0
