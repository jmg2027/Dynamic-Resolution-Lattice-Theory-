# DRLT-213 — State of the framework

**One-paragraph thesis.**  Pointing leaves a residue (Raw).
Lens application IS distinguishing, not a tool applied to Raw
from outside.  Self-consistency forces the atomic signature
`(NS, NT, c, d) = (3, 2, 2, 5)`.  From this the bipartite
cohomology programme (c-counter, Stern-Brocot mediant), the
algebraic P-orbit closure (Lucas-Pell trace ring), and the
physics deployment (α_em at 0.09 ppb, gluon octet from
b_1 = NS² − 1, etc.) all derive — without external parameters,
PURE in Lean.

## Closed at framework level

| Programme | Headline | Lean anchor | Chapter |
|---|---|---|---|
| Atomic forcing | (NS, NT, d) = (3, 2, 5) uniquely forced from atomicity + alive + Pell-Lucas recurrence | `Theory/Atomicity/{PairForcing, Five, ArityForcing, OrbitForcing}` | `physics/foundations/atomic_constants.md` |
| c-counter (5-direction) | `codim ≥ c` parametric ∀(NS, NT, c); `codim ≤ c` **unconditional at every c** (per-layer completeness closed 2026-05-25 via 8 explicit primary cup generators + layer-promotion) | `Cohomology/Bipartite/Parametric/EnrichedKNSNTcMaster.master_Knn_c_counter_resolved` + `V33EnrichedParametricDualSpanHard{,Lift}.joint_psi_kernel_subset_primary` | `math/cohomology/k_nm_c_classification.md` |
| Stern-Brocot mediant functor | V/E/F Vandermonde under mediant; K_{4,3} = K_{1,1} ⊕ K_{3,2} | `Cohomology/MediantCohomologyFunctor.mediant_cohomology_functor_capstone` | `math/cohomology/mediant_cohomology_functor.md` |
| Bipartite-tripartite self-containment | local (2, 1, 3) at every K_{3, 2}^{(c=2)} point + K_{2, 1, 3} cohomology refutes external extension | `Cohomology/Tripartite/V32V213CohomologyBridge.self_containment_cohomology_verdict` | `math/cohomology/tripartite_self_containment.md` |
| P-orbit naturalness | Lucas-Pell trace ring `⟨{L(k)} ∪ {NT, NS, d}⟩_ℤ` exhausts framework-natural integers | `Mobius213/Px/POrbitClosure.framework_natural_via_p_orbit_closure` + `Theory/Atomicity/OrbitForcing` | `math/mobius213_p_orbit_closure.md` |
| Möbius P canonical equivalence | `cutEq ↔ sternBrocotEq ∧ (0, 0)`; P = mediant generator | `Real213/Mobius213{Equiv, SternBrocot, PellInvariant}` | `math/mobius_canonical_equivalence.md` |
| α_em precision (0.09 ppb) | Gram structural + cup-ladder + SO(10) tail | `Physics/AlphaEM/Capstone` | `physics/alpha_em/precision_derivation.md` |
| c3 chain (gauge content) | Sym(3)-action on K_{3, 2}; gluon octet = b_1(K_{3, 2}^{(c=2)}) = 8 | `Physics/Symmetry/C3*` | `physics/symmetry/c3_chain.md` |

## Cross-frame synthesis

Three independent closures share **one proof shape**: an
invariant at a base level, an offset translation indexing
parallel copies, and a cancellation lemma that absorbs the
offset.  Stack the copies, count the summands — that is the
closure.  See `theory/essays/layer_multiplication_pattern.md`
for the shape and `theory/essays/synthesis_interlock_map.md`
for the explicit correspondence between c-counter directions
and P-orbit phases.

## Genuinely open

  · **Arity `c = 2` Lean theorem**: narrative-justified in
    `seed/AXIOM/03_form.md` §3.2 and operationally used
    everywhere, but no Lean theorem closes the "binary is the
    unique non-degenerate combine arity" claim.  Stub +
    statement at `lean/E213/Theory/Atomicity/CombinatorialArity.lean`.
  · **Cochain-level mediant functor**: count-level Vandermonde
    closed; cup-product algebra over the 4 × 9 = 36 mediant
    sub-cells is the next layer.  Massey-class factorisation
    `K_{4, 3} Massey ?= K_{1, 1} Massey ⊗ K_{3, 2} Massey` is
    the named cross-frame conjecture.
  · **Asymptotic P-orbit depth**: empirically `D(p) ≤ 4` for
    `p ≤ 97`; conjectured `O(log p)`; not proved.
  · **PRIMARY cup-image maximality**: `InPrimaryCupSpanPlusBoundary`
    is the dual-spanning restriction; whether it is the unique
    maximal kill-preserving restriction is a structural question.
  · **Geometrization 4-mfd exotic anomaly**: open conjecture;
    below DRLT Validation Standard (no precision theorem, no
    falsifier).  Tracked in `research-notes/G121_*`.
  · **Math ↔ Physics bridge discipline**: the Lean import
    graph has 174 Math → Physics + 56 Physics → Math direct
    imports under `Lib/`; the bounded-context spec
    (`lean/E213/ARCHITECTURE.md` §1 "Lib/" + §3 "Bridge.lean
    for cross-context") calls for routing such citations
    through `*Bridge*.lean` shims.  40 such shims exist
    already; coverage is uneven.  Audit + completion planned —
    see `theory/RESEARCH_PLAN.md` §5.1.

## How to verify

```bash
cd lean && lake build                  # full build (~5 min)
python3 tools/scan_all_axioms.py       # PURE / DIRTY scan
tools/lean_summary.py <subdir>         # per-file digest
```

Result: 0 sorry, 0 external axioms on the production critical
path.  Sealed-DIRTY-by-design modules (~56 theorems, Lens
funext + propext) are catalogued in `STRICT_ZERO_AXIOM.md`
§"Sealed-by-design categories".

## Entry points (suggested reading order)

1. `seed/AXIOM/05_no_exterior.md` §5 — the no-exterior
   philosophical anchor (re-read every session).
2. This file — current framework state.
3. `theory/INDEX.md` — book map (117 chapters).
4. `theory/essays/c_counter_programme_closure.md` — the
   five-direction closure synthesis with parallel to
   P-orbit closure.
5. `theory/essays/p_orbit_closure_master.md` — the algebraic
   side (Lucas-Pell trace ring, OrbitForcing).
6. `theory/essays/layer_multiplication_pattern.md` — the
   shared proof shape across c-counter, P-orbit, mediant.
7. `theory/essays/synthesis_interlock_map.md` — explicit
   correspondence table between the three synthesis essays.
8. `research-notes/G35_chiral_cup_ring_catalog.md` — open
   conjectures with per-conjecture status (active scratch).

## Volatile session state vs. permanent state

`HANDOFF.md` carries per-session boot context and immediate
open problems (≤100 lines).  Chapter additions and promotion
events log to `research-notes/INDEX.md` "Promotion log".
Permanent framework state lives here.

## Companion specs

`seed/RESOLUTION_LIMIT_SPEC.md`,
`seed/THEOREM_METHODOLOGY_SUITE.md`,
`seed/META_SCAN_ARCHETYPES.md`,
`seed/CLOSED_FORM_SPEC.md`.
