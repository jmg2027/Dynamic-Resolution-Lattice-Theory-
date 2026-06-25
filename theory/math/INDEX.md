# theory/math/

Math chapters.  Mirrors `lean/E213/Lib/Math/` by path — each chapter sits
under the same thematic super-cluster as its Lean sub-tree.

**Each cluster below is one domain reconstructed from 구분(distinguishing) +
잔여(residue)** via the `⟨C|L⟩⊕Residue` calculus — a Lens reading of the residue,
not a separate theory.  The number tower, algebra, analysis, cohomology, … are
the residue read under successive Lenses (`seed/AXIOM/07_primacy.md` §7.1:
primacy = breadth of such reconstruction).

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
`markov_uniqueness`, `lambert_weld`, `holonomy_of_the_lattice`).

### `algebra/` — algebraic structures + towers
`cayley_dickson/` (algebra tower + exceptional axes), `linalg213`, `polynomial213`,
`group`, `gra_book` (Graded Residue Arithmetic), and the Möbius / P-orbit chapters
`mobius213_p_orbit_closure`, `mobius_canonical_equivalence`, `phi_self_similarity`.

### `cohomology/` — the K_{NS,NT}^{(c)} programme
`cochain`, `cup`, `cupaw`, `delta`, `bipartite`, `fractal`, `aurifeuillean`,
`hodge`, `surfaces`, `universal`, `examples`, `bridge`,
`cup_ladder_graduation`, `k32_higher_cohomology`, `sym3_spine`.

### `numbertheory/` — `dyadic_fsm`, `modular_arithmetic`, `eisenstein_period_arithmetic`, `euclidean_division`, `legendre_symbol`, `quadratic_reciprocity`, `zolotarev`, `primitive_roots`, `fibonacci_5adic_valuation`, `apery_zeta3_arithmetic`, `chebyshev_prime_counting`, `multiplicative_divisor_theory`, `lifting_the_exponent`, `grounded_fundamental_theorem`, `number_theory_over_the_spine`.

### `geometry/` — geometric / topological / discrete-substrate
`geometry`, `topology`,
`angle_structure`, `number_grid`, `generation_rule`, `triangular_tower`,
`level_topology`, `operation_topology`, `bipartite_decomp`, `cartesian_vs_disjoint`,
`riemannian_curvature_tensor`, `discrete_curvature`, `discrete_perelman_core`,
`euclidean_lattice_metric`.

### `foundations/` — meta / cross-domain anchors
`axiom_systems`, `pattern_catalog/`, `choice`, `universe_chain`,
`async_growth`, `cross_domain_unification`, `algebra213_meta_theorems`,
`universal_descent_schema`.

### `probability/` — `probability`, `information`.

### `combinatorics/` — `combinatorics`, `logic`, `graph_connectivity`, `bool_enumeration`, `inclusion_exclusion_set_partitions`, `convolution_generating_functions` (the cut comultiplication, conv semiring + derivation, Vandermonde/binomial/Catalan, figurate sums).

### `order/` — `order_theory` (Galois connections, Boolean algebra, Knaster-Tarski).

### `logic/` — reverse mathematics / omniscience ledger
`reverse_math_213` (the `Lib/Math/Logic/` mirror — LPO/WLPO/MP/LLPO, the König
selection cost, `WKL ⟺ Heine–Borel`, the object-level axiom-cost ledger);
`no_walls_only_parameters` (the tetrachotomy `∅/0/1/many` = absence/wall/forced/free —
choice/forcing/large-cardinals as free Lens parameters, the one internal diagonal wall,
the self-grounding *theorem* `master_classifier_is_the_wall`, and self-classification's
idempotent fixed point; nine ∅-axiom modules).

### `tactic/` — `tactic`, `extras` (math-side infra).

## Promotion

Promotion criteria: `theory/PROMOTION_CRITERIA.md`.
Patterns: `lean/E213/docs/PROMOTION_PATTERNS.md`.
