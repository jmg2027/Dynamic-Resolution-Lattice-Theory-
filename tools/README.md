# tools/ — repo automation scripts

## Audit & verification

  - `kernel_regress.sh` — verify `E213.Term.*` theorems remain
    literally 0-axiom.  Hook-invoked on Term-ring edits.  (The
    script name predates the Term ring's current name.)
  - `full_build.sh` — `lake build E213` (framework rings, fast)
    followed by `lake build E213.Lib.Math E213.Lib.Physics`
    (content, slow).  Required check after any refactor touching
    Meta tactics / Real213 / List213 / etc. — the default `lake
    build E213` deliberately omits Lib content, so Lib regressions
    must be caught explicitly.
  - `scan_axioms.py <module>` — per-module `#print axioms` audit.
    Reports `[PURE]` (0 axioms) or `[DIRTY]` per top-level decl.
  - `scan_all_axioms.py` — tree-wide PURE / real-DIRTY / sealed
    classification with `SEALED_DIRTY_PREFIXES` for funext-by-design
    items.  Cited from CLAUDE.md as the canonical audit.
  - `audit_axioms.py [--filter K]` — older kernel-focused variant
    (hardcoded module list).  Superseded by `scan_axioms.py` for
    per-module work; kept for legacy invocation paths.
  - `sync_strict_zero_axiom.py [--csv FILE]` — diff
    `STRICT_ZERO_AXIOM.md` catalog vs reality (from
    `scan_all_axioms.py`).  Lists in-catalog-but-not-PURE and
    PURE-but-not-in-catalog candidates.

## Theorem inspection

  - `theorem_audit.py` — fingerprint extraction across the tree
    (combo signatures: tactic mix per theorem).  Output feeds the
    G17-G28 audit research notes.
  - `theorem_inspect.py` — pull individual theorem bodies + axiom
    status by name pattern.  Ad-hoc spelunking.

## Architecture audits

  - `layer_audit.py` — mechanical layer assignment (Term /
    Theory / Lens / Lib / Meta) for every Lean file based on
    import closure.  Produces canonical layer report cited from
    `lean/E213/ARCHITECTURE.md` + `INDEX.md`.

## Maintenance

  - `sync_namespaces.py [--apply] [--include-rust]` ★ — namespace ↔
    path alignment for E213.  Detects mismatches between a file's
    path and its `namespace ...` declaration; updates declarations
    + global references in a single sentinel-protected pass to
    avoid sed-cascade errors.

    Usage:
      python3 tools/sync_namespaces.py             # dry-run
      python3 tools/sync_namespaces.py --apply     # write changes
      python3 tools/sync_namespaces.py --apply --include-rust
      python3 tools/sync_namespaces.py --root lean/E213/Physics
      python3 tools/sync_namespaces.py --skip-list path1,path2

    Default skip list (vertical-layer umbrella sharing — leave alone):
      Theory/Raw, Theory/Raw.lean, Theory/Raw{Levels,Swap}.lean,
      Lens, Lens/Cardinality, Term, Prelude.lean.

    Exit codes: 0 OK, 1 unresolved mismatches, 2 build failed.

  - `port_candidates.py [--limit N]` — heuristic finder for
    short-proof theorems (`rfl`, `by decide`, etc.) suitable for
    porting to Lean kernel `Cap_*.lean` modules as deep-embedded
    Terms.

## Policy

  - `FORBIDDEN.md` — patterns blocked by hooks (sorry, axiom,
    Mathlib import, Classical, native_decide in Kernel).

## Sub-cluster reorg workflow

When introducing a sub-cluster reorg (move N files into a new dir):

  1. `git mv` the files into the new sub-dir.
  2. `python3 tools/sync_namespaces.py --apply --include-rust`.
  3. Tool updates `namespace ...` declarations + every reference
     across `lean/` and (with `--include-rust`) `rust-engine/`.
  4. Tool runs `lake build` automatically and reports.

Replaces the previous error-prone manual `sed -i` workflow that
failed twice (cascade replacements; sentinel approach prevents this).
