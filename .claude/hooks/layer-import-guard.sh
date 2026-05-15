#!/bin/bash
# layer-import-guard: enforce ARCHITECTURE.md (2026-05-12) layer discipline
# + sub-cluster public-surface discipline (2026-05-15).
#
# Each ring may import only from:
#   - itself (own ring)
#   - the immediately-below ring's public API
#   - Meta (ring-independent)
#
# Each ring + sub-cluster exposes a single API.lean (or umbrella
# `.lean`).  Reach-in to specific implementation submodules from
# outside the cluster is a discipline violation.
#
# Rules (on Write|Edit only):
#   1. `import E213.<lower-ring>.Internal.*` from higher ring     — block
#   2. `import E213.Theory.Raw.<X>` (X ≠ API) from outside Raw/    — block
#   3. `import E213.Lens.AxiomLenses.Bridges*` from outside Bridges/ — block
#   4. `import E213.Term.<X>` (X ≠ API, Tree) from outside Term/    — block
#   5. `import E213.Lens.<X>.<Y>...` (3+ levels) from outside Lens/ — block
#   6. `import E213.Theory.(Atomicity|CDDouble).<X>` from outside
#      Theory/                                                    — block
#
# Note: Rule 1 covers cross-ring Internal reach-in (Term.Internal,
# Theory.Internal, Lens.Internal).  Rule 3 is the strict ∅-axiom
# isolation of DIRTY-by-design Lean kernel-axiom bridges.

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
  REASON="layer-import-guard: ${PATH_##*/} (${RING} ring) tried to import lower-ring Internal/* directly [${VIOL_SUMMARY}]. ARCHITECTURE.md (2026-05-12): each ring uses only the immediately-below ring's public API. Use the public surface (Term.Tree, Theory.Raw.API, Lens.API, ...) instead of reaching into Internal/*."
  echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
  exit 0
fi

# === Rule 2: Theory.Raw specific-submodule reach-in ===
# Theory/Raw/ exposes a single public surface via Theory.Raw.API.
# Outside the Raw cluster, code should not reach into specific
# submodules (Slash, Swap, Fold, Rec, ...).
#
# Exceptions:
#   - files in Theory/Raw/ itself (own cluster, OK)
#   - import of Theory.Raw.API (the sole canonical entry; the
#     Theory.Raw alias shim was removed 2026-05-15)
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
      REASON="layer-import-guard: ${PATH_##*/} reaches into Theory.Raw specific submodules [${SPECIFIC_SUMMARY}]. Theory/Raw/ exposes a single explicit public surface — use 'import E213.Theory.Raw.API'. Reach-in to Theory.Raw.{Slash, Fold, Swap, SwapSlash, Rec, Levels, Hom, Signed, Core, Demo, Endomorphic} is a discipline violation per ARCHITECTURE.md (2026-05-12)."
      echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
      exit 0
    fi
    ;;
esac

# === Rule 3: AxiomLenses Bridges (DIRTY-by-design) isolation ===
# Lens/AxiomLenses/Bridges/{Funext, QuotSound}.lean and the
# Bridges.lean aggregator are sealed: they inhabit lens witnesses
# using Lean kernel axioms (Quot.sound, funext) and are DIRTY by
# construction.  213 core must NOT transitively pull them via the
# Lens umbrella — strict ∅-axiom contract is import-level.
#
# Allowed importers:
#   - Files under Lens/AxiomLenses/Bridges/ itself
#   - Lens/AxiomLenses/Bridges.lean aggregator
#   - (Future) explicit demos that intentionally consume DIRTY
#     bridges must opt in by listing themselves here.
#
# Evaluated BEFORE Rule 5 so Bridges-specific message wins over
# generic Lens 3+-level reach-in message.
case "$PATH_" in
  */lean/E213/Lens/AxiomLenses/Bridges*) ;;  # within bridges cluster — skip
  *)
    BRIDGE_IMPORT=$(printf '%s' "$CONTENT" \
      | grep -E "^import E213\\.Lens\\.AxiomLenses\\.Bridges($|\\.[A-Z])" \
      | head -3)
    if [ -n "$BRIDGE_IMPORT" ]; then
      BRIDGE_SUMMARY=$(printf '%s' "$BRIDGE_IMPORT" | tr '\n' ';' | sed 's/;$//')
      REASON="layer-import-guard: ${PATH_##*/} imports DIRTY-by-design AxiomLenses.Bridges [${BRIDGE_SUMMARY}].  Bridges/{Funext, QuotSound} inhabit lens witnesses via Lean kernel axioms (Quot.sound, funext) — importing them taints the ∅-axiom contract.  Only files under Lens/AxiomLenses/Bridges/ may import these.  Did you mean 'import E213.Lens.AxiomLenses.Core.{Funext,Propext,QuotSound}' (PURE primitives)?"
      echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
      exit 0
    fi
    ;;
esac

# === Rule 4: Term cluster reach-in ===
# Outside Term/, only Term.API and Term.Tree are public entry
# points.  Specific implementation files (Term, Compare, Pair,
# Rat, Decide, Sound, MonomialAxioms, Demo) are not API.
case "$PATH_" in
  */lean/E213/Term/*) ;;
  *)
    TERM_SPECIFIC=$(printf '%s' "$CONTENT" \
      | grep -E "^import E213\\.Term\\.[A-Z][A-Za-z0-9]*$" \
      | grep -v "^import E213\\.Term\\.API$" \
      | grep -v "^import E213\\.Term\\.Tree$" \
      | head -3)
    if [ -n "$TERM_SPECIFIC" ]; then
      TERM_SUMMARY=$(printf '%s' "$TERM_SPECIFIC" | tr '\n' ';' | sed 's/;$//')
      REASON="layer-import-guard: ${PATH_##*/} reaches into Term specific submodules [${TERM_SUMMARY}].  Term/ exposes two public entry points only — 'import E213.Term.API' (K1–K4 bundle: Term, Compare, Pair, Rat, Decide, Sound, MonomialAxioms) or 'import E213.Term.Tree' (Tree re-export shim).  Reach-in is a discipline violation."
      echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
      exit 0
    fi
    ;;
esac

# === Rule 5: Lens sub-cluster reach-in ===
# Outside Lens/, code may import only:
#   - Lens.API
#   - Lens.<TopLevelFile> — 2-level paths to top-level Lens files
#     (LensCore, Initiality, SemanticAtom, …) or sub-cluster
#     umbrellas (Algebra, AxiomLenses, Cardinality, Compose,
#     Instances, Lattice, Number, Properties, Universal, …).
# A 3+-level import reaches into a sub-cluster's specific
# submodule — blocked.
case "$PATH_" in
  */lean/E213/Lens/*) ;;
  *)
    LENS_SPECIFIC=$(printf '%s' "$CONTENT" \
      | grep -E "^import E213\\.Lens\\.[A-Z][A-Za-z0-9]*\\..*$" \
      | head -3)
    if [ -n "$LENS_SPECIFIC" ]; then
      LENS_SUMMARY=$(printf '%s' "$LENS_SPECIFIC" | tr '\n' ';' | sed 's/;$//')
      REASON="layer-import-guard: ${PATH_##*/} reaches into Lens sub-cluster submodules [${LENS_SUMMARY}].  Outside Lens/, code must use Lens.API or a sub-cluster umbrella ('import E213.Lens.Instances', 'import E213.Lens.Cardinality', etc.).  3+-level reach-in is a discipline violation."
      echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
      exit 0
    fi
    ;;
esac

# === Rule 6: Theory.Atomicity / Theory.CDDouble reach-in ===
# Theory.Raw is handled by Rule 2 (above).  Atomicity and CDDouble
# sub-clusters expose their umbrella `.lean` files (Theory.Atomicity,
# Theory.CDDouble); specific submodule reach-in is blocked outside
# Theory/.
case "$PATH_" in
  */lean/E213/Theory/*) ;;
  *)
    THEORY_SPECIFIC=$(printf '%s' "$CONTENT" \
      | grep -E "^import E213\\.Theory\\.(Atomicity|CDDouble)\\.[A-Z]" \
      | head -3)
    if [ -n "$THEORY_SPECIFIC" ]; then
      THEORY_SUMMARY=$(printf '%s' "$THEORY_SPECIFIC" | tr '\n' ';' | sed 's/;$//')
      REASON="layer-import-guard: ${PATH_##*/} reaches into Theory sub-cluster submodules [${THEORY_SUMMARY}].  Outside Theory/, use the sub-cluster umbrella ('import E213.Theory.Atomicity', 'import E213.Theory.CDDouble') or 'import E213.Theory.API'."
      echo "{\"decision\":\"block\",\"reason\":\"${REASON}\"}"
      exit 0
    fi
    ;;
esac

exit 0
