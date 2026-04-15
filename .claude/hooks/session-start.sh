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

# ── Install Lean 4 (elan) if not present ─────────────────────
if [ ! -f "$HOME/.elan/bin/lean" ]; then
  echo "[setup] Installing elan + Lean 4..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none 2>/dev/null || true
  TOOLCHAIN=$(cat "${CLAUDE_PROJECT_DIR}/critical-line/lean/lean-toolchain" 2>/dev/null || echo "leanprover/lean4:v4.16.0")
  "$HOME/.elan/bin/elan" toolchain install "$TOOLCHAIN" 2>/dev/null || true
fi
if [ -n "${CLAUDE_ENV_FILE:-}" ] && [ -f "$HOME/.elan/bin/lean" ]; then
  echo "export PATH=\"\$HOME/.elan/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
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
