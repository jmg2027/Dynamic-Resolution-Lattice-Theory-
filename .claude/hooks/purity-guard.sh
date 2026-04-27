#!/bin/bash
# DRLT 213 purity guard: block forbidden patterns in lean/E213/.
# CLAUDE.md: 0 sorry, 0 외부 axiom, 0 Mathlib, 0 Classical, 0 native_decide.
# 외부 axiom 추가 = 이론 폐기 trigger.

TMPFILE=$(mktemp)
cat > "$TMPFILE"
TOOL=$(jq -r '.tool_name // empty' < "$TMPFILE")

if [ "$TOOL" = "Write" ]; then
  PATH_=$(jq -r '.tool_input.file_path // empty' < "$TMPFILE")
  CONTENT=$(jq -r '.tool_input.content // empty' < "$TMPFILE")
elif [ "$TOOL" = "Edit" ]; then
  PATH_=$(jq -r '.tool_input.file_path // empty' < "$TMPFILE")
  CONTENT=$(jq -r '.tool_input.new_string // empty' < "$TMPFILE")
else
  rm -f "$TMPFILE"
  exit 0
fi
rm -f "$TMPFILE"

# Only check lean/E213/ .lean files
case "$PATH_" in
  */lean/E213/*.lean) ;;
  *) exit 0 ;;
esac

VIOLATIONS=""
echo "$CONTENT" | grep -qE '^[[:space:]]*sorry\b|:= sorry|by sorry' \
  && VIOLATIONS="${VIOLATIONS}sorry "
echo "$CONTENT" | grep -qE '^[[:space:]]*axiom[[:space:]]' \
  && VIOLATIONS="${VIOLATIONS}axiom "
echo "$CONTENT" | grep -q 'native_decide' \
  && VIOLATIONS="${VIOLATIONS}native_decide "
echo "$CONTENT" | grep -q 'import Mathlib' \
  && VIOLATIONS="${VIOLATIONS}Mathlib_import "
echo "$CONTENT" | grep -q 'open Classical' \
  && VIOLATIONS="${VIOLATIONS}Classical "

if [ -n "$VIOLATIONS" ]; then
  echo "{\"decision\":\"block\",\"reason\":\"DRLT 213 purity 위반: ${VIOLATIONS}— lean/E213/ 는 0 sorry, 0 외부 axiom, 0 Mathlib, 0 Classical, 0 native_decide 강제. 213-native 우회 작성 필요.\"}"
fi
