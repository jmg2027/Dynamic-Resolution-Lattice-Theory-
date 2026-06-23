# Derivation-breadth map — what the residue has reconstructed

Primacy = **breadth** of ∅-axiom derivation across math AND physics
(`seed/AXIOM/07_primacy.md` §7.1).  This is the *coverage* view: each
domain is one `⟨C|L⟩ ⊕ Residue` reconstruction from 구분 + 잔여 (not a
separate theory, CLAUDE.md spine), and this map says how far each is
carried.

**Status legend** — grounded in capstone existence, not restated counts:

| Tag | Meaning |
|---|---|
| **closed** | a real ∅-axiom capstone exists (cited); core reconstruction complete |
| **closed + frontier** | core closed; named open extensions in `research-notes/frontiers/` |
| **frontier** | narrative / numerical / parametric-template only; no closed capstone |

> **Per-theorem PURE/DIRTY truth is NOT restated here** — it drifts.
> The single sources of truth are `STRICT_ZERO_AXIOM.md` (PURE/DIRTY
> catalog) and the live scanner `tools/scan_all_axioms.py`.  This map
> cites capstone *names* (grep-checkable) and points to the frontier
> board for the open side.  (Built 2026-06-23 from the Phase-8
> verify-prose-against-Lean audit; re-verify capstone names before
> trusting a row, per the lesson that produced this file.)

---

## Math (`theory/math/`, `lean/E213/Lib/Math/`)

| Domain | Primary capstone (real) | Status |
|---|---|---|
| Nat213 / Int213 | difference-Lens readout (`Int213.neg_subNatNat`); `06_lens_readings` §6.7 | closed |
| Real213 | approximant-sequence + `HasModulus` cuts (`PiCut`, `EulerCut`) | closed + frontier (more transcendental brackets) |
| Complex | `ComplexCut := Cut × Cut` (`Complex/Capstone`) | closed |
| Hyper | `Hyper213` (cofinite equiv); tetration in `Meta/Nat/HyperLadder` | closed |
| Divisor theory | `MobiusInversion.mobius_inversion`, `DirichletConvolution` | closed |
| Quadratic reciprocity | `QuadraticReciprocity.quadratic_reciprocity` | closed |
| Zolotarev | `Zolotarev.zolotarev_mu` | closed |
| Legendre / LTE | `LiftingExponent.lifting_prime_power`, `gauss_qr` | closed |
| Modular / CRT / F_p² | `ModArith` CRT + `FP2Sqrt5.fp2Frob_*` | closed |
| Primitive roots | `exists_primitive_root` | closed |
| Fibonacci 5-adic | `FibZIdentities.fibZ_quintuple` | closed |
| Apéry ζ(3) | `apery_recurrence` | closed |
| PNT / Chebyshev | `ChebyshevLower.chebyshev_constant_interval` (bracket) | closed + frontier (sharper bracket) |
| Pisano / DyadicFSM | `UniversalSplit.universal_split_case` (parametric template) | closed + frontier (`∀ prime p` closure — `dyadic_fsm.md`) |
| Möbius P-orbit | `Mobius213GrandUnification.grand_unification`; `POrbitRing.p_orbit_ring_catalog_master` | closed |
| Cayley–Dickson tower | `hurwitz_tower_L1/L2_capstone` (`AlgebraTowerCapstone.capstone_loaded` = import sentinel) | closed + frontier (higher layers) |
| GRA / φ self-similarity | `phi_self_similarity` family | closed |
| Group / LinAlg / Polynomial | `Group/Capstone`, `linalg213` | closed |
| ODE (Nat-discrete) | `ODE/Capstone.total_witness` (`picard_const`/`picard_exp`) | closed + frontier (more PDE) |
| Measure / Lebesgue | `measureNum` + `lebesgueStepNum` (dyadic brackets) | closed |
| Modulus / Cauchy | `StrongModulus`, `Cauchy/*` | closed |
| Markov spectrum | `markov_tree_branch`, `markov_prime_pow_unique` | closed |
| Cf-finite / holonomicity | `OrbitDimension`, `cf_holonomicity` family | closed |
| Cohomology — bipartite b₀/b₁ | `EulerAndCapstone.parametric_close_capstone`, `universal_kernel_close` | closed |
| Cohomology — K_{3,2} 2/3/4-skeleton | `cohomology_dims_at_full_simple`, `steenrod_squares_at_omega_master` | closed + frontier |
| Cohomology — higher structure | — | **frontier** (`cohomology_higher_structure.md`: Steenrod ladder, Adem/Cartan, Massey, K_{3,3}) |
| Cohomology — cup / Hodge / fractal | `CupAW` Leibniz family, `HodgeConjecture`, `Fractal` | closed |
| Foundations — cross-domain | `joint_math_physics_uniform`, `graded_ring_nu_bridge_capstone` | closed |
| Foundations — async growth / descent | `every_raw_reached`, `MonovariantFlow.descent_reaches` / `euclid_via_descent_invariant` | closed |
| Combinatorics | `Ramsey`, `Sperner`, `BoolEnum.bcount_const`, `GraphConnectivity` | closed |
| Probability / Information | `ProbabilityCut`; LLN | closed + frontier (LLN modulus degenerate) |
| Logic / Order | `bool_lem`, `order_theory` (`mulDiv_gc`) | closed |

## Physics (`theory/physics/`, `lean/E213/Lib/Physics/`) — the DRLT deployment

Scope note: this is **one domain's** falsifiability gate (DRLT Validation
Standard), not the yardstick for the math work above (`seed/AXIOM/07_primacy.md`).

| Observable | Primary theorem (real) | Status |
|---|---|---|
| 1/α_em (0.2 ppb) | `AlphaEM.invAlphaEm_precision_theorem` | closed (precision falsifier) |
| Koide / mass ratios | `Koide = NT/NS = 2/3`; `Mass/*` | closed |
| N_gen = C(NS,NT) = 3 | `Simplex/Generations.drlt_no_4th_gen_falsifier` | closed (falsifier) |
| CKM / CP phase δ=90° | `Mixing.delta_ninety_forced`, `CKMExactUnitarity` | closed |
| Couplings / θ_QCD | `Couplings.SpectrumComplete`, `ThetaQCD` | closed (θ_QCD falsifier) |
| Yang–Mills gap / Weinberg | `YangMills.Gap`, `WeinbergAngle` (≈0.2312 bracket) | closed |
| Cosmology (N_eff, η_B, dark E) | `Cosmology.NeffDerivation`, `EtaBFalsifier` | closed + frontier (no Hubble module) |
| Nuclear / hadron | `Nuclear/*`, `Hadron/*` | closed |
| Master atomic catalog | `Capstones/MasterCatalog.master_atomic_catalog` | closed |

---

## How to read this against the audit

The Phase-8 audit removed citations to Lean that **does not exist**.
Every row above cites a capstone that **does** (grep-checkable).  Rows
tagged *frontier* are exactly where prose had run ahead of Lean; those
open items are now registered under `research-notes/frontiers/` (the
sink rule, `PROCESS.md`).  A row's *closed* tag asserts a real capstone,
**not** a re-counted PURE total — for the ∅-axiom truth of any single
theorem, run `tools/scan_axioms.py <module>`.

## Maintenance

- A new closed Lean sub-tree → add a row, cite its capstone.
- A frontier closes → flip the tag, point the row at the new capstone,
  move the frontier note to `research-notes/archive/`.
- Companion: `STRICT_ZERO_AXIOM.md` (PURE/DIRTY), `catalogs/falsifier-roster.md`
  (the falsifier side), `catalogs/cross-domain-identifications.md`
  (the cross-route agreement that is "no exterior" made measurable).
