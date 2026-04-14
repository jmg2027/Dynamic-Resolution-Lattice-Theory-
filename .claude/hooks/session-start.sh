#!/bin/bash
set -euo pipefail

# Only run in remote (web) sessions
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

# ── Install Python dependencies ──────────────────────────────
pip install --quiet numpy scipy matplotlib 2>/dev/null || true

# ── Set PYTHONPATH so lib/ is importable from anywhere ───────
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  echo "export PYTHONPATH=\"${CLAUDE_PROJECT_DIR}/lib:\${PYTHONPATH:-}\"" >> "$CLAUDE_ENV_FILE"
fi

# ── Notify about handoff document ────────────────────────────
HANDOFF="${CLAUDE_PROJECT_DIR}/HANDOFF.md"
if [ -f "$HANDOFF" ]; then
  echo ""
  echo "╔══════════════════════════════════════════════════╗"
  echo "║  HANDOFF.md found — read it to resume context   ║"
  echo "╚══════════════════════════════════════════════════╝"
  echo ""
fi
