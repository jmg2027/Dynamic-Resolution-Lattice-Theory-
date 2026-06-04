#!/bin/bash
# UserPromptSubmit hook — log the user's submitted prompts, one file per session.
#
# Writes verbatim to  prompt-log/<date>_<session8>.md  (created on the first
# prompt of a session, so empty sessions leave no file).  Produces NO stdout —
# a UserPromptSubmit hook's stdout is injected into the model context, and this
# must never do that.  Always exits 0; it logs, it never blocks a prompt.
#
# Cleanup (prune noise / pasted-not-typed blocks) is the `prompt-log` skill,
# run when the user asks.  The hook cannot tell typed from pasted — it records
# everything; the judgement is made at cleanup time.

TMP=$(mktemp)
cat > "$TMP"
PROMPT=$(jq -r '.prompt // empty' < "$TMP")
SID=$(jq -r '.session_id // empty' < "$TMP")
rm -f "$TMP"

[ -z "$PROMPT" ] && exit 0

DIR="${CLAUDE_PROJECT_DIR:-.}/prompt-log"
mkdir -p "$DIR" 2>/dev/null || exit 0
SHORT=$(printf '%s' "$SID" | cut -c1-8)
[ -z "$SHORT" ] && SHORT="nosid"
FILE="$DIR/$(date +%F)_${SHORT}.md"

if [ ! -f "$FILE" ]; then
  {
    printf '# Prompt log — session %s\n\n' "$SHORT"
    printf 'Started %s.  Verbatim user prompts, one entry each.  At session end,\n' "$(date '+%F %T')"
    printf 'run the `prompt-log` skill to prune noise + pasted (non-typed) blocks,\n'
    printf 'then commit.  Uncommitted = lost when the container is reclaimed.\n'
  } > "$FILE"
fi

N=$(grep -c '^### ' "$FILE" 2>/dev/null)
case "$N" in ''|*[!0-9]*) N=0 ;; esac
N=$((N + 1))
{
  printf '\n### %d · %s\n' "$N" "$(date '+%T')"
  printf '%s\n' "$PROMPT"
} >> "$FILE"

exit 0
