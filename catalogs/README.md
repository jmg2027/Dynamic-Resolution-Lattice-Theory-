# 213 Catalogs

Lookup tables for the 213 library.  grep-able.

## Files

  atomic-integers.md     1-1000 atomic integer representations
  physics-constants.md   α, m_p, Ω_Λ, ... atomic chain
  periodic-table.md      113 + 5 super-heavy elements atomic
  falsifiers.md          14 sharp measurement decision propositions
  correspondences.md     same integer multi-framework
  math-theorems.md       math theorems catalog
  cross-domain-identifications.md  10 named CDIs from G109 (math ↔ physics byte-identical Expr)
  recursor-inventory.md  185 inductive types with recursor invocations (G105)
  internal-hubs.md       top E213-internal load-bearing lemmas (G92 surface + G102 Expr)
  falsifier-roster.md    135 decide-verified impossibility theorems (G100 automated catalog)
  correspondence-surface.md  propext / Quot.sound classification — the classical-correspondence surface (A) + thesis (B) + equivR-recoverable (C) + backlog (D) + plumbing (E)

## Usage

```bash
$ grep "137" catalogs/*.md
catalogs/atomic-integers.md:  137 = 1/α_em (prime, ppm)
catalogs/physics-constants.md:  α_em ≈ 1/137.036
catalogs/correspondences.md:  - Fine structure
```

```bash
$ grep -l "neutrino" catalogs/*.md
catalogs/falsifiers.md
catalogs/physics-constants.md
```

## Synchronization

  Lean theorems = ground truth
  Books = narrative
  Catalogs = lookup

  Three sources synchronized (updated at each marathon completion).
