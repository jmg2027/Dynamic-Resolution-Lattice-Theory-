# theory/math/

Math chapters.  Mirrors `lean/E213/Lib/Math/` (+ `Lens/Number/`).

## Closed chapters (56)

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

Universal meta-structure (1):
- [`gra_book.md`](gra_book.md) — **GRA Book** (textbook treatment): Ch.0–9 + appendices. Formal Definition→Theorem→Proof flow. 7 axioms, 5 Readings (cohomology/operad/HoTT/graph/analysis), GRA Tower ↔ CD Tower duality, number system unification, dimensional proliferation fractal, Adelic decomposition, one-paragraph master statement. **CLOSED** (Marathon 16 — `lean/E213/Lib/Math/GRA/` umbrella, 28 files / 0 sorry). Lean cross-reference table in Appendix B.1.

Cross-frame synthesis (3):
- [`sym3_spine.md`](sym3_spine.md) — Sym(3) 8-fold decomposition `2·trivial ⊕ 3·standard` across K_{3,2}^{(c=2)} H¹, Thurston geometries, gluon octet, Akbulut cork; capstone `X1_sym3_cross_frame_capstone`
- [`mobius_canonical_equivalence.md`](mobius_canonical_equivalence.md) — Möbius P = [[2,1],[1,1]] as the canonical equivalence on cuts via Stern-Brocot mediant closure (7 files / 68 PURE); cutEq ↔ sternBrocotEq ∧ (0,0); ValidCutN + signedEq bridges; Pell unit invariant + atomicity anchor
- [`mobius213_p_orbit_closure.md`](mobius213_p_orbit_closure.md) — P-orbit naturalness boundary (13 Px modules / 206 PURE); tripartite K_{2,1,3} additive complement; mod-p periods + Lucas-Pell trace orbit; refined naturalness hierarchy
- [`phi_self_similarity.md`](phi_self_similarity.md) — φ as the single invariant of `P = [[2,1],[1,1]]`, read three ways (form / count `5^L` / limit-ratio φ), all ∀n ∅-axiom; Cassini norm `fib(2n+2)²+1 = fib(2n+2)·fib(2n+1)+fib(2n+1)²` ∀n; φ as a closed-form `ValidCut`; `fib_convergent_below_phi` ∀n.  Capstone `self_similarity_three_readings`
- [`completeness_relocated.md`](completeness_relocated.md) — completeness is **not** constitutive of a Real213 real (it is a leaf of the import graph, not a root); a real is a decision procedure against ℚ; completeness re-enters only as a limit operation on sequences (`AbCutSeq`), **unconditional** for algebraic reals (φ: closed-form modulus `N=2k`, `phiCompletion_limit_eq_phiCut`) and **modulus-gated** for transcendentals (e ∈ (8/3,3), π ∈ (14/5,4): modulus is a hypothesis, the total one being the LEM `MonotonicBounded` §180–194 refuses).  The algebraic/transcendental split as a theorem
- [`probe_twist_conic.md`](probe_twist_conic.md) — the probe-twist (Möbius `P=[[2,1],[1,1]] ∈ SL₂(ℤ)`, hyperbolic) conserves the φ-norm `Q=m²−mk−k²`, so every cut wobbles along its own hyperbola `Q=N` (`ProbeTwistConic.Q_preserved`); the wobble step is `f⁻¹` (`ProbeTwistDynamics`).  What sorts the reals: quadratic irrationals ride **one** conic (φ/√2 formalised, general case = Lagrange's thm) — transcendentals **escape every** conic (e vs π differ only in escape-regularity).  Marks three tiers: Lean theorem / classical fact / out-of-scope (the elliptic-modular *production* of transcendentals is a separate higher theory this does not reach)
- [`completeness_without_completeness.md`](completeness_without_completeness.md) — **capstone paper**: the whole arc as one thesis ("completeness is a relocated finite operation"). Five parts — cut/modulus → probe-twist conic → cross-determinant divergence depth (1/3/6/∞, = P-recursive rank, ⊥ irrationality measure) → ordinal axis tower (`ratioLift`, `(h,d)<ω²`, exponent recursion, ε₀-is-not-the-end) → naming-the-ceiling-raising = the foundational residue (`diag_not_in_seq`, `cantor_general`, `self_covering_closure`). 15 sections, every `(L)` claim indexed to its ∅-axiom Lean file; self-contained, book-style. **Start here** for the narrative, then drill into `completeness_relocated.md` / `probe_twist_conic.md`

Cohomology classification extension (3):
- [`cohomology/k_nm_c_classification.md`](cohomology/k_nm_c_classification.md) — universal `(NS, NT, c)` cohomology framework (EnrichedKNSNTc): codim ≥ c parametric + codim ≤ c dual-span + arbitrary-m bilateral kill + K_{3, 3} ↔ Möbius bridges + K_{4, 3} asymmetric instance + cross-graph S-row pattern
- [`cohomology/mediant_cohomology_functor.md`](cohomology/mediant_cohomology_functor.md) — Stern-Brocot mediant Vandermonde at the count level (V 2-term / E 4-term / F factored-Vandermonde²); K_{4, 3} = K_{1, 1} ⊕ K_{3, 2} marquee
- [`cohomology/tripartite_self_containment.md`](cohomology/tripartite_self_containment.md) — K_{2, 1, 3} cohomology (Betti = (1, 0, 0)) + K_{3, 2}^{(c=2)} local (2, 1, 3) signature at every point; cross-frame verdict: atomic-level duality preserved (|E| = |△| = 6), cohomology-level duality broken (b₁ = 8 ≠ 0)

Promotion criteria: `theory/PROMOTION_CRITERIA.md`.
Patterns: `lean/E213/docs/PROMOTION_PATTERNS.md`.
