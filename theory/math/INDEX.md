# theory/math/

Math chapters.  Mirrors `lean/E213/Lib/Math/` by path — each chapter sits
under the same thematic super-cluster as its Lean sub-tree.

## Clusters (mirror of `Lib/Math/`)

### `numbersystems/` — the number tower
`slot_arithmetic` (the slot programme: tuple-tower ontology, witness layer,
sandwich-first, the commuting square, layer constants),
`real213`, `padic_real213`, `signed_cut`, `complex`, `hyper`, `irrational`,
`completeness_relocated`, `completeness_without_completeness`, `probe_twist_conic`.

### `analysis/` — modulus-tracked analysis (no ε-δ)
`classic_calc`, `differentiation`, `integration`, `minimal_root`, `flux_m_v_t`,
`cauchy`, `measure`, `multivariable`, `functional`, `modulus`, `modulus_structure`,
`cascade_calculus`, `ode`, plus the depth / continued-fraction arc
(`divergence_depth_characterization`, `cfinite_orbit_dimension`,
`cf_holonomicity_hierarchy`, `newton_gregory`, `holonomic_modulus`, `form_margin_modulus`,
`tower_native_completeness`, `refined_completability_engine`,
`spiral_coordinate_classification`, `phi_pi_poles`, `markov_spectrum`,
`markov_uniqueness`).

### `algebra/` — algebraic structures + towers
`cayley_dickson/` (algebra tower + exceptional axes), `linalg213`, `polynomial213`,
`group`, `gra_book` (Graded Residue Arithmetic), and the Möbius / P-orbit chapters
`mobius213_p_orbit_closure`, `mobius_canonical_equivalence`, `phi_self_similarity`.

### `cohomology/` — the K_{NS,NT}^{(c)} programme
`cochain`, `cup`, `cupaw`, `delta`, `bipartite`, `fractal`, `aurifeuillean`,
`hodge`, `hodge_conjecture`, `surfaces`, `universal`, `examples`, `bridge`,
`cup_ladder_graduation`, `k32_higher_cohomology`, `k_nm_c_classification`,
`mediant_cohomology_functor`, `tripartite_self_containment`, `sym3_spine`.

### `numbertheory/` — `dyadic_fsm`, `modular_arithmetic`, `eisenstein_period_arithmetic`, `euclidean_division`, `legendre_symbol`, `quadratic_reciprocity`, `zolotarev`, `primitive_roots`, `fibonacci_5adic_valuation`.

### `geometry/` — geometric / topological / discrete-substrate
`geometry`, `topology`, `geometrization_conjecture`, `exotic_4mfd_cork`,
`angle_structure`, `number_grid`, `generation_rule`, `triangular_tower`,
`level_topology`, `operation_topology`, `bipartite_decomp`, `cartesian_vs_disjoint`,
`riemannian_curvature_tensor`, `discrete_curvature`.

### `foundations/` — meta / cross-domain anchors
`axiom_systems`, `pattern_catalog/`, `choice`, `universe_chain`,
`async_growth`, `cross_domain_unification`, `algebra213_meta_theorems`.

### `probability/` — `probability`, `information`.

### `combinatorics/` — `combinatorics`, `logic`, `graph_connectivity`, `bool_enumeration`.

### `logic/` — reverse mathematics / omniscience ledger
`reverse_math_213` (the `Lib/Math/Logic/` mirror — LPO/WLPO/MP/LLPO, the König
selection cost, `WKL ⟺ Heine–Borel`, the object-level axiom-cost ledger).

### `tactic/` — `tactic`, `extras` (math-side infra).

## Promotion

Promotion criteria: `theory/PROMOTION_CRITERIA.md`.
Patterns: `lean/E213/docs/PROMOTION_PATTERNS.md`.
