# DRLT-213 — State of the framework

**One-paragraph thesis.**  The primitive is **distinguishing**;
the **residue** (Raw) is what it provably leaves — distinguishing
is faithful but never total (`object1_not_surjective`).  Every
object is read as `⟨C | L⟩ ⊕ Residue`, and every domain is that
move applied: a Lens reading of the residue, not a separate
theory.  Self-consistency forces the construction axes
`(NS, NT, d) = (3, 2, 5)`.  The bipartite multiplicity `c` of
`K_{NS,NT}^{(c)}` is **not** forced — it is a *free
Lens-presentation parameter*, removable from every observable;
the cohomology is proved parametrically in `c`, no value
canonical.  On this core the number systems, the bipartite
cohomology, the algebraic P-orbit closure (Lucas-Pell trace
ring), and the physics deployment (α_em, gluon octet from
`b_1 = NS² − 1`) are each reconstructed from distinguishing +
residue — without external parameters, PURE in Lean.

## Closed at framework level

| Programme | Headline | Lean anchor | Chapter |
|---|---|---|---|
| Atomic forcing | **(NS, NT, d) = (3, 2, 5)** uniquely forced from atomicity + alive + Pell-Lucas recurrence + k=2 arity (pigeonhole over `Fin 2` base for k ≥ 3 vacuous); `c = 2` derived, not a fourth primitive | `Theory/Atomicity/{PairForcing, Five, ArityForcing, OrbitForcing, CombinatorialArity}` + `Physics/Foundations/AtomicConstantsParametricFullIff.c2b_full_iff` | `physics/foundations/atomic_constants.md` |
| Bipartite cohomology (b₀, b₁, b₂) | connected `K_{NS,NT}^{(c)}` kernel = the two constants (`b₀ = 1`) for all NS, NT, c; `b₁ = 6, b₂ = 1` at presentation `c=2`, full simple-cycle filling | `Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.universal_kernel_close` + `Cohomology/Bipartite/Filled3CellCohomology.phase1_cohomology_anchor` | `math/cohomology/bipartite.md` |
| Bipartite-tripartite self-containment | K_{2, 1, 3} cohomologically trivial above H⁰ (`(b₀,b₁,b₂)=(1,0,0)`); Massey shadow projection vanishes — external tripartite extension carries no shared cohomology | `Cohomology/Tripartite/V213Betti.K213_betti_capstone` + `V213ShadowProjection` | `math/cohomology/bipartite.md` |
| P-orbit naturalness | Lucas-Pell trace ring `⟨{L(k)} ∪ {NT, NS, d}⟩_ℤ` exhausts framework-natural integers | `Mobius213/Px/POrbitClosure.framework_natural_via_p_orbit_closure` + `Theory/Atomicity/OrbitForcing` | `math/mobius213_p_orbit_closure.md` |
| Möbius P canonical equivalence | `cutEq ↔ sternBrocotEq ∧ (0, 0)`; P = mediant generator | `Real213/Mobius213{Equiv, SternBrocot, PellInvariant}` | `math/mobius_canonical_equivalence.md` |
| α_em precision (0.09 ppb) | Gram structural + cup-ladder + SO(10) tail | `Physics/AlphaEM/Capstone` | `physics/alpha_em/precision_derivation.md` |
| c3 chain (gauge content) | Sym(3)-action on K_{3, 2}; gluon octet = b_1(K_{3, 2}^{(c=2)}) = 8 | `Physics/Symmetry/C3*` | `physics/symmetry/c3_chain.md` |

## Cross-frame synthesis

Independent closures share **one proof shape**: an invariant at a
base level, an offset translation indexing parallel copies, and a
cancellation lemma that absorbs the offset.  Stack the copies,
count the summands — that is the closure.  See
`theory/essays/synthesis/the_forcing_criterion_is_distinguishing.md`
for the criterion separating a forced distinguishing axis from a
removable re-presentation.

## Genuinely open

  · **Asymptotic P-orbit depth**: empirically `D(p) ≤ 4` for
    `p ≤ 97`; conjectured `O(log p)`; not proved.
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
3. `theory/INDEX.md` — book map.
4. `theory/essays/p_orbit/p_orbit_closure_master.md` — the algebraic
   side (Lucas-Pell trace ring, OrbitForcing).
5. `theory/essays/synthesis/the_forcing_criterion_is_distinguishing.md`
   — the forced-axis vs removable-re-presentation criterion.

## Volatile session state vs. permanent state

`HANDOFF.md` carries per-session boot context and immediate
open problems (≤100 lines).  Chapter additions and promotions are
recorded in git history; the research cycle is documented in
`PROCESS.md`.  Permanent framework state lives here.

## Companion specs

`seed/THEOREM_METHODOLOGY_SUITE.md`,
`seed/META_SCAN_ARCHETYPES.md`,
`seed/CLOSED_FORM_SPEC.md`.
