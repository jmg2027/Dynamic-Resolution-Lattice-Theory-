#!/bin/bash
# layer-import-guard: enforce ARCHITECTURE.md (2026-05-12) layer discipline.
#
# Each ring may import only from:
#   - itself (own ring)
#   - the immediately-below ring's public API
#   - Meta (ring-independent)
#
# This hook blocks Write|Edit that introduces an import of
# `E213.<lower-ring>.Internal.*` (a forbidden reach-in) in a file
# belonging to a higher ring.
#
# Allowed reach-ins (skipped):
#   - file is in the same ring as the Internal it imports
#   - file is in Meta (ring-independent)
#   - file is in Term (lowest ring; no lower ring exists)

TMPFILE=$(mktemp)
cat > "$TMPFILE"
TOOL=$(jq -r '.tool_name // empty' < "$TMPFILE")
PATH_=$(jq -r '.tool_input.file_path // empty' < "$TMPFILE")

if [ "$TOOL" = "Write" ]; then
  CONTENT=$(jq -r '.tool_input.content // empty' < "$TMPFILE")
elif [ "$TOOL" = "Edit" ]; then
  CONTENT=$(jq -r '.tool_input.new_string // empty' < "$TMPFILE")
else
  rm -f "$TMPFILE"
  exit 0
fi
rm -f "$TMPFILE"

# Determine the file's ring by path
case "$PATH_" in
  */lean/E213/Theory/*) RING=theory ;;
  */lean/E213/Lens/*)   RING=lens   ;;
  */lean/E213/Lib/*)    RING=lib    ;;
  *) exit 0 ;;  # Term, Meta, or non-Lean: no enforcement here
esac

# Forbidden Internal imports per ring (lower rings)
case "$RING" in
  theory) FORBIDDEN="E213\\.Term\\.Internal\\." ;;
  lens)   FORBIDDEN="E213\\.(Term|Theory)\\.Internal\\." ;;
  lib)    FORBIDDEN="E213\\.(Term|Theory|Lens)\\.Internal\\." ;;
esac

VIOL=$(printf '%s' "$CONTENT" | grep -E "^import ${FORBIDDEN}" | head -3)
if [ -n "$VIOL" ]; then
  VIOL_SUMMARY=$(printf '%s' "$VIOL" | tr '\n' ';' | sed 's/;$//')
  REASON="layer-import-guard: ${PATH_##*/} (${RING} ring) tried to import lower-ring Internal/* directly [${VIOL_SUMMARY}]. ARCHITECTURE.md (2026-05-12): each ring uses only the immediately-below ring's public API. Use the public surface (Term.Tree, Theory.Raw, Lens.API, ...) instead of reaching into Internal/*."
  echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
  exit 0
fi

# === Rule 2: Theory.Raw specific-submodule reach-in ===
# Theory/Raw/ exposes a single public surface via Theory.Raw.API
# (Theory.Raw alias too).  Outside the Raw cluster, code should not
# reach into specific submodules (Slash, Swap, Fold, Rec, ...).
#
# Exceptions:
#   - files in Theory/Raw/ itself (own cluster, OK)
#   - import of Theory.Raw.API or Theory.Raw (allowed)
#   - (no more Mobius exception — migrated to Lib/Math/Mobius213
#     in 2026-05-12 cleanup)
case "$PATH_" in
  */lean/E213/Theory/Raw/*) ;;  # own cluster — skip
  *)
    SPECIFIC=$(printf '%s' "$CONTENT" \
      | grep -E "^import E213\\.Theory\\.Raw\\.[A-Z][A-Za-z0-9]*$" \
      | grep -v "^import E213\\.Theory\\.Raw\\.API$" \
      | head -3)
    if [ -n "$SPECIFIC" ]; then
      SPECIFIC_SUMMARY=$(printf '%s' "$SPECIFIC" | tr '\n' ';' | sed 's/;$//')
      REASON="layer-import-guard: ${PATH_##*/} reaches into Theory.Raw specific submodules [${SPECIFIC_SUMMARY}]. Theory/Raw/ exposes a single explicit public surface — use 'import E213.Theory.Raw.API' (or 'import E213.Theory.Raw' alias). Reach-in to Theory.Raw.{Slash, Fold, Swap, SwapSlash, Rec, Levels, Hom, Signed, Core, Demo} is a discipline violation per ARCHITECTURE.md (2026-05-12)."
      echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
      exit 0
    fi
    ;;
esac

exit 0
