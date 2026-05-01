# tools/ — repo automation scripts

  - `kernel_regress.sh` — verify `E213.Kernel.*` 101 theorems remain
    literally 0-axiom.  Hook-invoked on Kernel edits.
  - `audit_axioms.py` — `#print axioms` survey across whole tree.
  - `port_candidates.py` — find unported Lean theorems for Rust mirror.
  - `sync_namespaces.py` ★ — auto namespace↔path alignment for E213.
    Detects mismatches between a file's path (e.g. `Math/Cohomology/
    Universal/Prop53.lean`) and its `namespace ...` declaration
    (`E213.Math.Cohomology.Universal.Prop53`).  Updates declarations
    + global references in a single sentinel-protected pass to avoid
    sed-cascade errors.

    Usage:
      python3 tools/sync_namespaces.py             # dry-run
      python3 tools/sync_namespaces.py --apply     # write changes
      python3 tools/sync_namespaces.py --apply --include-rust
      python3 tools/sync_namespaces.py --root lean/E213/Physics
      python3 tools/sync_namespaces.py --skip-list path1,path2

    Default skip list (vertical-layer umbrella sharing — leave alone):
      Firmware/Raw, Firmware/Raw.lean, Firmware/Raw{Levels,Swap}.lean,
      Hypervisor, Infinity, Tactic, Kernel, Prelude.lean.

    Exit codes: 0 OK, 1 unresolved mismatches, 2 build failed.

  - `FORBIDDEN.md` — patterns blocked by hooks.

## Notes for future tooling

When introducing a sub-cluster reorg (move N files into a new dir),
the workflow is:

  1. `git mv` the files into the new sub-dir.
  2. `python3 tools/sync_namespaces.py --apply --include-rust`.
  3. Tool updates `namespace ...` declarations + every reference
     across `lean/` and (with `--include-rust`) `rust-engine/`.
  4. Tool runs `lake build` automatically and reports.

This replaced the previous error-prone manual `sed -i` workflow that
failed twice (cascade replacements; sentinel approach prevents this).
