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

**Status (2026-06-16): PARTIAL — clean part done, carrier-delete escalated.**

Done (build-green, ∅-pure):
- `PhotonKernel.b_1 := NS*NS-1` (octet, direct from `NS=3`); `num_edges := NS*NT*NT`
  (c-free signature form); dropped `Prefactors.c_lat` dep; `b_1_eq_8` preserved.
- Deleted `Cup/K32Projection.lean` (the explicit c-line `k32_edges=c·NS·NT`,
  `k32_b1=6c−4`); its sole importer `AssignmentForcing` re-rooted c-free.
- `Bare` (IntegerSkeleton.edge_count, Prefactors capstone), `ProjectionRatios`,
  `ChannelCohomologyLoss` (`E_K`, `H1_K:=NS²−1`), `AtomicBase/Edges`: edge counts
  restated `NS·NT²`; dropped the c-multiplicity-only readings.
- `Prefactors.c_lat` KEPT (value = `NT`): consumed as a bare `2` by ~17 downstream
  physics files (TauOverMu, HierarchyTowers, Higgs/{Mass,Quartic,Master}, Hadron,
  Cosmology/DarkEnergy, Capstones/{MasterCatalog,PhysicsTrackComplete},
  ClosedPropagator, FibonacciExtended, …).  Removing it is a Phase-F catalog sweep.

**C3-chain port DONE (2026-06-16): `H1K`/`OctetCokernel` + c=2-graph
Symmetry cluster deleted; capstones re-homed c-free.**

The abstract rep-theoretic content was ported onto a new c-free carrier
`Lib/Physics/Symmetry/OctetModule.lean`: `Octet := Fin 8 → Bool`,
`rank = NS²−1 = 8` (sourced from `SpectrumComplete.alpha_3_channel`, not a
graph `b₁`), the two Sym(3) involution generators `M_S01`/`M_S12`, the
Coxeter presentation `s²=t²=(st)³=e`, the Sym(3)-fixed subspace
(`fixedSize = 4`), the decomposition `2·trivial ⊕ 3·standard`, and the
explicit standard 2-rep pairs.  The 8×8 entries are a valid matrix
realisation of Sym(3) ⊂ GL(8,𝔽₂) (verified by `decide`), carrying no
edge-multiplicity data — the c=2 graph was only the discovery route.

- `C3ChainCapstone.c3_chain_master` (★★★★★) rebuilt c-free: routes through
  `OctetModule` + `Sym3Group` + `AutKGroup` + `BettiKernel` (`H¹(Δ⁴)=0`,
  4-simplex contractibility).  The two graph-embedding conjuncts (ι_edge
  collapse, ι Sym(3)-equivariance) are replaced by the c-free octet
  sourcing `8 = NS²−1`; all abstract conjuncts preserved.
- Geometrization gate `ScopeAndDepth.K32_depth_via_c3_chain_master` +
  `K32_cohomology_depth_features` re-pointed to `OctetModule.rank` /
  `OctetModule.fixedSize` — still proven, still PURE.
- Re-pointed all other consumers (Geometrization/{CrossFrame,Exotic4Mfd,
  Ricci,StructuralMapping,EightGeometries,KChartLensAbstract,Capstone,
  Poincare}, AkbulutCork/{Foundation,CrossFrame,Twist,CorkTheorem}) to
  `OctetModule`.
- `git rm`: Symmetry/{Sym3OnH1K,Sym3OnH1KMatrix,Sym3OnH1KCayley,
  Sym3IrrepDecomp,Sym3StandardReps,Sym3StandardRepThird,IotaKToDelta4,
  IotaSym3Equivariance,Sym3OnKEdges,Sym3BlockDiagonal,C2_6MixedMatrices,
  C2_6OnH1K}, Cohomology/Bipartite/{H1K,OctetCokernel}.

**`V32`/`V32Betti` KEPT.** They are NOT C3-chain-only: a large non-C3
consumer base imports them (HodgeConjecture/*, Mobius213*, Tripartite,
C2DoublingDerivation, DyadicFSM, GeometrizationConjecture/Ansatz, K5,
DiamondShape).  Their c-free re-rooting / deletion is a separate Phase-B/F
sweep, out of scope for the octet C3-chain port.

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
