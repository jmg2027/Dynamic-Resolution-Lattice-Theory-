# GRA (Graded Residue Arithmetic) — Lean Formalization

**Marathon**: 16_gra_universality  
**Status**: Phase 1 in progress  
**Blueprint**: `blueprints/math/16_gra_universality.md`

---

## Files

| File | Content | Status |
|------|---------|--------|
| `GRAModel.lean` | Typeclass + GRAIso + refl/symm/trans | 🟡 symm has sorry |
| `NumberTheory.lean` | Trivial (2,3)-model on ℕ (hub) | 🟡 reach/depth sorry |
| `Graph.lean` | R₄ walk-length model + iso to NT | 🟡 reach/depth sorry |

## Phase Plan

- [x] Phase 1a: GRAModel typeclass defined
- [x] Phase 1b: NumberTheory instance (skeleton)
- [x] Phase 1c: Graph instance (skeleton)
- [x] Phase 1d: GRAIso Graph↔NT (trivial on simplified carrier)
- [ ] Phase 1e: Eliminate all sorry in Phase 1 files
- [ ] Phase 2: Analysis instance (R₅)
- [ ] Phase 3: Cohomology instance (R₁)
- [ ] Phase 4: HoTT instance (R₃)
- [ ] Phase 5: Higher Algebra instance (R₂) + Capstone

## Notes

The current Graph instance uses a **simplified carrier** (Nat = walk length)
which makes the iso to NT trivially the identity map. The real mathematical
content is:

1. **Proving that K_{3,2} walk arithmetic actually satisfies A1–A7** (the
   `graph_reach` theorem is the non-trivial part)
2. **Eventually lifting to a richer carrier** (actual Walk structures) where
   the iso is no longer trivially `id` but requires a non-trivial functor.

This staged approach matches the marathon philosophy: get the skeleton
compiling first, then enrich incrementally.
