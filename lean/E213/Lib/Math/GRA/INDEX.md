# GRA (Graded Residue Arithmetic) — Lean Formalization

**Marathon**: 16_gra_universality  
**Status**: Phase 5 complete — Universality Capstone proved  
**Blueprint**: `blueprints/math/16_gra_universality.md`

---

## Files

| File | Content | Status |
|------|---------|--------|
| `GRAModel.lean` | Typeclass + GRAIso + refl/symm/trans | ✅ 0 sorry |
| `NumberTheory.lean` | Trivial (2,3)-model on ℕ (hub) | ✅ 0 sorry |
| `Graph.lean` | R₄ walk-length model + iso to NT | ✅ 0 sorry |
| `Analysis.lean` | R₅ resolution-exponent model + iso to NT | ✅ 0 sorry |
| `Cohomology.lean` | R₁ cochain-degree model + iso to NT | ✅ 0 sorry |
| `HoTT.lean` | R₃ truncation-level model + iso to NT | ✅ 0 sorry |
| `HigherAlgebra.lean` | R₂ operad-level model + iso to NT + Capstone | ✅ 0 sorry |

## Phase Plan

- [x] Phase 1a: GRAModel typeclass defined
- [x] Phase 1b: NumberTheory instance (skeleton)
- [x] Phase 1c: Graph instance (skeleton)
- [x] Phase 1d: GRAIso Graph↔NT (trivial on simplified carrier)
- [x] Phase 1e: Eliminate all sorry in Phase 1 files
- [x] Phase 2: Analysis instance (R₅)
- [x] Phase 3: Cohomology instance (R₁)
- [x] Phase 4: HoTT instance (R₃)
- [x] Phase 5: Higher Algebra instance (R₂) + Capstone
- [ ] Phase 6: Applications (translation theorems)

## Capstone

`GRA_Universality` structure + `gra_universality_witness` proves:
all 5 Readings (NT, Graph, Analysis, Cohomology, HoTT, Higher Algebra)
are pairwise isomorphic as (2,3)-GRA models.

`transitivity` + `any_two_readings_iso` derive arbitrary R_i ≅ R_j
from the hub-and-spoke pattern (each R_i ≅ NT).

## Notes

The current instances use a **simplified carrier** (Nat = grade directly)
which makes the isos to NT trivially the identity map. The real mathematical
content is:

1. **Proving that each domain's arithmetic actually satisfies A1–A7**
   (the reachability theorem is the non-trivial part — Chicken McNugget
   for gcd(2,3)=1)
2. **Eventually lifting to richer carriers** (actual Walk structures,
   Cochain complexes, operad objects, etc.) where the iso requires
   non-trivial functors.

This staged approach matches the marathon philosophy: get the full
5-Reading skeleton compiling first, then enrich incrementally.

## Purity

- 0 sorry
- 0 native_decide (all replaced with decide)
- 0 external axioms
- 0 Mathlib imports
