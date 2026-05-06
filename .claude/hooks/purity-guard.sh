#!/bin/bash
# DRLT 213 purity guard: 두 단계 강제.
#
#   Tier 1 (모든 lean/E213/*.lean):  CLAUDE.md 의 5 forbidden
#     - sorry, 외부 axiom, Mathlib, Classical, native_decide
#
#   Tier 2 (lean/E213/Term/**):  비전 강제 — *literally 0 axiom*
#     - 위 5개 +
#     - simp / rw / cases-on-Eq / Iff = / decide-tactic
#       (모두 propext 또는 Quot.sound 끌어올 수 있음)
#
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

case "$PATH_" in
  */lean/E213/*.lean) ;;
  *) exit 0 ;;
esac

VIOLATIONS=""

# Tier 1 — all of E213
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

# Tier 2 — Kernel strict
case "$PATH_" in
  */lean/E213/Term/*.lean)
    # 'decide' tactic (Decidable Eq Nat → Nat.beq_eq → propext)
    echo "$CONTENT" | grep -qE '(^|[^a-zA-Z_])by[[:space:]]+decide([^a-zA-Z_]|$)|:=[[:space:]]*by[[:space:]]+decide' \
      && VIOLATIONS="${VIOLATIONS}kernel:decide "
    # simp tactic (loves propext)
    echo "$CONTENT" | grep -qE '(^|[^a-zA-Z_])by[[:space:]]+simp([^a-zA-Z_]|$)|simp[[:space:]]+only' \
      && VIOLATIONS="${VIOLATIONS}kernel:simp "
    # rw tactic (Prop rewrite = propext)
    echo "$CONTENT" | grep -qE '(^|[^a-zA-Z_])rw[[:space:]]*\[' \
      && VIOLATIONS="${VIOLATIONS}kernel:rw "
    ;;
esac

if [ -n "$VIOLATIONS" ]; then
  REASON="DRLT 213 purity 위반: ${VIOLATIONS}"
  case "$PATH_" in
    */lean/E213/Term/*.lean)
      REASON="${REASON}— Kernel 은 *literally 0 axiom* 강제. propext/Quot.sound 도 안 됨. Eq.subst, Bool.cond, 구조귀납 으로 우회."
      ;;
    *)
      REASON="${REASON}— 213-native 우회 작성 필요 (CLAUDE.md falsifiability)."
      ;;
  esac
  echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
fi
