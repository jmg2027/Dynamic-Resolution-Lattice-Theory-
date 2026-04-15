#!/bin/bash
# Setup Lean 4 + Mathlib for DRLT critical-line proofs
# Run: bash scripts/setup-lean.sh

set -e

LEAN_DIR="critical-line/lean"

# 1. Install elan (Lean version manager)
if ! command -v elan &> /dev/null && [ ! -f "$HOME/.elan/bin/elan" ]; then
    echo "[setup-lean] Installing elan..."
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi

export PATH="$HOME/.elan/bin:$PATH"

# 2. Install Lean toolchain (reads lean-toolchain file)
TOOLCHAIN=$(cat "$LEAN_DIR/lean-toolchain" 2>/dev/null || echo "leanprover/lean4:v4.16.0")
if ! elan toolchain list | grep -q "${TOOLCHAIN##*/}"; then
    echo "[setup-lean] Installing toolchain: $TOOLCHAIN"
    elan toolchain install "$TOOLCHAIN"
fi

# 3. Fetch Mathlib cache
echo "[setup-lean] Fetching Mathlib cache..."
cd "$LEAN_DIR"
lake update 2>&1 | tail -5

# 4. Build
echo "[setup-lean] Building PmfRh..."
lake build 2>&1 | tail -10

echo "[setup-lean] Done. $(lake build 2>&1 | grep -c 'Built') modules built."
