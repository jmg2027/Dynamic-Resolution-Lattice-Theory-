# theory/math/

Math chapters.  Mirrors `lean/E213/Lib/Math/` (+ `Lens/Number/`).

## Closed chapters (53)

Hub chapters:
- [`cohomology/hodge_conjecture.md`](cohomology/hodge_conjecture.md) — HodgeConjecture/ (67 files, 6 layers)
- [`cayley_dickson/algebra_tower.md`](cayley_dickson/algebra_tower.md) — CayleyDickson/ (50 files)
- [`universe_chain.md`](universe_chain.md) — UniverseChain + Mobius213 + Nat213 (~32 files)
- [`real213.md`](real213.md) — Real213/ (57 files, 7 sub-clusters)
- [`dyadic_fsm.md`](dyadic_fsm.md) — DyadicFSM/ (101 files)
- [`signed_cut.md`](signed_cut.md) — SignedCut/ (35 files; absorbs G37/G38/G39)
- [`geometrization_conjecture.md`](geometrization_conjecture.md) — GeometrizationConjecture/ (13 files, R1 closed, R1+ partial)
- [`padic_real213.md`](padic_real213.md) — Padic/ (8 files, 308 PURE; ring axioms, Hensel inv/sqrt with existence + uniqueness, full ultrametric, Frobenius lift, Teichmüller Cauchy, ℚ_p, DRLT 5-adic anchor)

Cohomology sub-clusters (12 in `cohomology/`):
- `cohomology/{cochain, cup, cupaw, delta, bipartite, fractal, aurifeuillean, hodge, surfaces, universal, examples, bridge}.md`

Analysis sub-clusters (5 in `analysis/`):
- `analysis/{minimal_root, classic_calc, differentiation, flux_m_v_t, integration}.md`

G37-G50 discrete-substrate geometry (11):
- `modulus, number_grid, angle_structure, dialogue_audit, bipartite_decomp, cartesian_vs_disjoint, generation_rule, triangular_tower, operation_topology, level_topology, algebra213_meta_theorems`

Marathon-completed domains (6):
- `combinatorics, information, logic, probability, group, modular_arithmetic` (modular_arithmetic extended by G119 to 13 files: +Bezout / FLT / F_{p²})

Infrastructure (10):
- `axiom_systems, cross_domain_unification, pattern_catalog/pattern_catalog, linalg213, polynomial213, irrational, hyper, cauchy, topology, ode, multivariable, complex, measure, functional, extras, tactic, choice, geometry, cascade_calculus, modulus_structure`

Cross-frame synthesis (2):
- [`sym3_spine.md`](sym3_spine.md) — Sym(3) 8-fold decomposition `2·trivial ⊕ 3·standard` across K_{3,2}^{(c=2)} H¹, Thurston geometries, gluon octet, Akbulut cork; capstone `X1_sym3_cross_frame_capstone`
- [`mobius_canonical_equivalence.md`](mobius_canonical_equivalence.md) — Möbius P = [[2,1],[1,1]] as the canonical equivalence on cuts via Stern-Brocot mediant closure (7 files / 68 PURE); cutEq ↔ sternBrocotEq ∧ (0,0); ValidCutN + signedEq bridges; Pell unit invariant + atomicity anchor

Promotion criteria: `theory/PROMOTION_CRITERIA.md`.
Patterns: `lean/E213/docs/PROMOTION_PATTERNS.md`.
