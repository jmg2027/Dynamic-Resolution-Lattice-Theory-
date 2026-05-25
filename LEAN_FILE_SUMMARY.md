# Lean file summary — derivation policy

The canonical per-file summary of the Lean tree lives in the
**Lean source itself**.  Each file's `/-! … -/` module docstring
states its role; each declaration (`theorem`, `def`, `inductive`,
`structure`, `instance`) has its own `/-- … -/` docstring.  The
`import` statements record dependencies.

To regenerate a markdown summary of any subdirectory:

```bash
tools/lean_summary.py                              # whole tree
tools/lean_summary.py lean/E213/Lib/Math/Cohomology
tools/lean_summary.py lean/E213/Lib/Math/Mobius213/Px --decls-only
```

The script reads the Lean files directly and emits one section
per file with **role** (from module docstring), **decls** (top-
level declarations), and **imports** (with the `E213.` prefix
elided).  Long decl lists truncate to the first 12 names plus a
`(+N more)` indicator.

This replaces the previous hand-maintained `LEAN_FILE_SUMMARY.md`
catalogue.  Hand-maintained catalogues stale; module docstrings
do not.  When module purpose changes, update the docstring; the
summary regenerates.

## Higher-level entry points

  · `lean/E213.lean` — top-level umbrella (5 ring layers)
  · `lean/E213/ARCHITECTURE.md` — ring layer spec
  · `lean/E213/Lib/Math/Cohomology/INDEX.md`,
    `lean/E213/Lib/Math/Real213/INDEX.md`,
    `lean/E213/Lib/Math/Mobius213/Px/INDEX.md`,
    `lean/E213/Theory/Atomicity/INDEX.md` — per-cluster INDEX
  · `theory/INDEX.md` — narrative book (chapters mirror Lean
    subtrees)
  · `STRICT_ZERO_AXIOM.md` — PURE/DIRTY catalogue (terms +
    sealed-by-design + audit command)
