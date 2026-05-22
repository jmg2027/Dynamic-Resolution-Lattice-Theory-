# lean/E213/Lib — DRLT Library Ring

Lib is the **outermost layer** of the four-ring architecture (Term →
Theory → Lens → Lib).  Composite results built on derived APIs from
the inner rings.  Per `lean/E213/ARCHITECTURE.md` ring spec.

## Sub-trees

| Sub-tree | Files | Purpose | Umbrella |
|---|---:|---|---|
| `Math/` | 799 | 213-native mathematics (Real213 + Analysis + Algebra + Cohomology + …) | `Math.lean` |
| `Physics/` | 191 | DRLT physics deployment (AlphaEM, Hadron, Higgs, Couplings, Cosmology, …) | `Physics.lean` |

## Entry points

The `.lean` umbrella files are the **canonical indexes** for each
sub-tree — their module docstrings enumerate every chapter cluster
and explain its role:

  · `lean/E213/Lib/Math.lean`     — full Math sub-tree map
  · `lean/E213/Lib/Physics.lean`  — full Physics sub-tree map

For ring-level structure see `lean/E213/ARCHITECTURE.md`.

## Companion narratives

Each closed sub-tree has a narrative chapter under `theory/math/` or
`theory/physics/`.  See `theory/INDEX.md` for the book map.

## Status invariants

Per `STRICT_ZERO_AXIOM.md`:

  · All mathematical content in `Math/*` and `Physics/*` is fully
    **PURE** on Lean 4 core (no propext, Quot.sound, Classical.choice,
    native_decide in derivations of mathematical statements).
  · `lake build` clean on the production critical path.
