# C-free rebuild — work plan (marathon)

**Mandate (originator):** delete all content based on the *current* `c` (the
`K_{NS,NT}^{(c)}` edge multiplicity) — including the pure parametric cohomology
programme — and rebuild everything c-free.  No deferring.

**Why:** the deep-research finding `c_is_three_distinct_twos.md` established
that the label `c` conflated three distinct 2's, and that the K32
edge-multiplicity `c` is a *selected re-presentation* of `NS²−1`, never a forced
primitive.  The corrected foundation has **no atomic `c`**.

## Corrected foundation (the new ground truth)

- Forced atoms: `(NS, NT, d) = (3, 2, 5)`.  **No `c`.**
- Octet / `1/α₃ = NS² − 1 = 8` — SU(3) adjoint, **direct from `NS = 3`**
  (`SpectrumComplete.alpha_3_channel`); not a graph `b₁`.
- `1/α₂ = d² − 1 = 24`; `1/α₁`-sector prefactors re-expressed c-free.
- The genuine "2" is the **signature/order** = `NT` = period-2 sign = `i`
  (`i²=−1`).  Its home is the metric `(−,+,+,+)` via the signed Hodge
  `⋆²=−1` on `Δ⁴` (to be built).

## Scope decision (originator, 2026-06-16): **literal full delete**

The pure `K_{NS,NT}^{(c)}` parametric cohomology programme is deleted, not
relabelled.  Both the physics-framing `c` and the atomic-tuple `c` go.

## Execution order (rebuild-verified-then-delete for load-bearing; delete-now for leaves)

### Phase A — framing (build-safe, docs/docstrings) — atomic tuple `(3,2,2,5) → (3,2,5)`
Remove every "c is a forced atom / 4th primitive / THE canonical object" claim:
`atomic_constants.md`, `DEGREES_OF_FREEDOM_LEDGER.md`, `VERIFICATION_SPINE.md`,
`theory/INDEX.md`, `THEORY_BOOK.md`, `CAPSTONE_INDEX.md`, blueprints, READMEs.

### Phase B — delete the leaf c-counter cohomology programme
Only 4 external importers.  Delete:
- `lean/E213/Lib/Math/Cohomology/Bipartite/` c-counter files: `V33*`,
  `Parametric/*`, `Massey*`, `V43`, `V32LocalSignature`, the enriched / dual-span
  / indeterminacy files, `Mobius213K33*`.
- `Cohomology/CrossGraphPattern.lean`, `Cohomology/K33Unified.lean`,
  `Cohomology/MediantCohomologyFunctor.lean`,
  `Cohomology/BipartiteStermBrocotClassification.lean`.
- Fix the 2 real external importers (`Geometry/AkbulutCork/Foundation.lean`,
  `Geometry/GeometrizationConjecture/KChartLensAbstract.lean`) — strip c-counter
  usage.
- Theory chapters/essays: `k_nm_c_classification.md`, `k32_higher_cohomology.md`,
  `mediant_cohomology_functor.md`, `tripartite_self_containment.md`,
  `c_counter_*` essays, `disjoint_layers_as_direct_sum.md`,
  `multiplicity_layer_uniformity.md`, etc.  Catalog/INDEX entries.

### Phase C — octet re-rooting (algebraic, not graph)
Redirect every octet/`8`/`b₁(K32)` derivation to `NS²−1` directly.  Delete
`H1K`, `OctetCokernel`, `V32Betti`, `V32`, `K32Projection` (the K32 b₁ machinery)
once importers are re-rooted.  Re-root `PhotonKernel.b_1` → `NS²−1`
(`SpectrumComplete`) or delete `b_1` in favour of the adjoint.

### Phase D — α_em spine c-free re-derivation (RESEARCH-GRADE; verify before delete)
The headline `1/α_em = 137.036` (0.2 ppb, `GramStructuralCapstone`) routes the
prefactors `60/24/12` through `edge_count = c·NS·NT`.  Re-derive c-free:
`12 = NS·NT²` (the temporal axis entering quadratically — the order-2 square),
`60 = NS·NT²·d / 12·d`, `24 = d²−1`.  **Build + verify the c-free chain reproduces
137,035,999,111×10⁻⁹ BEFORE deleting the c-based carriers** — the falsifiability
contract forbids destroying the verified headline result without a verified
replacement.

### Phase E — signature build (new positive content)
Construct the signed-`ℤ` Hodge star on `Δ⁴`; prove `⋆²=−1` at grades 1,3 as an
operator identity; derive `(−,+,+,+)` from the one negative grade; tie to
`NT`/`i`.  ∅-axiom.

### Phase F — sweep, verify, integrate
`lake build` green; `scan_all_axioms` PURE; catalogs / INDEX / HANDOFF synced;
no residual `K_{3,2}^{(c)}` / `c·NS·NT` / `(3,2,2,5)` anywhere.

## Risk register
- **Headline α_em result**: must not be deleted before the c-free re-derivation
  (Phase D) is built and verified to the same ppb.  Hard gate.
- **Build coherence**: leaf deletions (Phase B) keep build green; spine deletions
  (Phase C/D) break it until re-rooted — done in the same phase, not left open.
- **`scan_axioms` purity** preserved throughout.
