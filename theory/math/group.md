# Group Theory 213

**Status**: Closed (5 files; marathon-completed; blueprint retired).

## Overview

213-native group theory: finite groups (Sym(n), Aut, dihedral,
binary tetrahedral, ...) as **Cayley-table types** with explicit
multiplication tables.  No abstract `Group` typeclass needed for
operational use; the table IS the group.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Group/` (5 files)
- **Umbrella**: `Group.lean`
- **Blueprint**: `blueprints/math/11_group_213.md` (retired)
- **∅-axiom status**: PURE

## Narrative

Classical group theory uses the `Group` typeclass with abstract
axioms.  213's version: each finite group is **the explicit
Cayley table** on a finite carrier:

```
SmallGroup n := {
  carrier : Fin n,
  mul_table : Fin n → Fin n → Fin n,
  ...  -- axiom witnesses, all decidable
}
```

The Group axioms (associativity, identity, inverses) are
**decided** on the Cayley table.  This avoids the typeclass-
synthesis machinery that pulls in `Classical` in Lean.

Used downstream by:
- `Lib/Physics/Symmetry/Sym3Group.lean` (C3 chain Phase 11)
- `Lib/Physics/Symmetry/AutKGroup.lean` (C3 chain Phase 12)
- `Lib/Math/Mobius213/` (Möbius P-matrix order)

## Connection

- `theory/physics/symmetry/c3_chain.md` — Sym(3), Aut(K) as Cayley tables
- `theory/math/universe_chain.md` — Möbius P^n group structure
- `theory/math/cross_domain_unification.md` (C6) — Group as paradigm instance
