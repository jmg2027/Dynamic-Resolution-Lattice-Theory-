# Mobius213 — sub-tree INDEX

Möbius matrix `P = [[2,1],[1,1]]` and its orbit, encoding the
atomic signature `(NS, NT, det) = (3, 2, 1)`.

**Status**: CLOSED — 30 files, ~450+ PURE declarations.
Sub-tree `Px/` houses the bulk (25 files, ~424 decls).

## Top-level files

| File | Decls | Content |
|---|---|---|
| `Px.lean` | — | Umbrella import for `Px/` sub-tree |
| `Mobius213K32Bridge.lean` | bridge | K_{3,2} ↔ Möbius P state-class connection |
| `Mobius213K33Bridge.lean` | bridge | K_{3,3} ↔ Möbius P state-class connection |
| `TowerConvergence.lean` | tower | Convergent tower limit properties |
| `TowerLInfty.lean` | tower | L(∞) tower-limit construction |

## Sub-tree

  · [`Px/INDEX.md`](Px/INDEX.md) — 25 files, ~424 decls: symmetry species
    catalog + P-orbit closure programme + universal theorems.

## Cross-references

  · Theory: `theory/math/algebra/mobius213_p_orbit_closure.md`
  · Theory: `theory/math/algebra/mobius_canonical_equivalence.md`
  · Companion files (outside this tree):
    - `Lib/Math/Algebra/Mobius213GrandUnification.lean`
    - `Lib/Math/Algebra/Mobius213SignatureAxisCatalog{,Phase2}.lean`
    - `Lib/Math/Algebra/Mobius213OneAsGlue.lean`
    - `Lib/Math/Algebra/Mobius213CrossDomainMeta.lean`
    - `Lib/Math/Algebra/Mobius213ModFive.lean`
