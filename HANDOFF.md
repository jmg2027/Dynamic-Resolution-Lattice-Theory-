# Session handoff

Branch: `claude/tower-research-analysis-3uWqd`

The durable record of all closed work lives in `lean/E213/` (source of truth) and
`theory/` (narrative).  This file keeps only: the latest arc's one-line map, a
compact index of what is closed, and the detailed next-target list.

## Latest arc — real numbers as cuts, completeness without completeness

A long originator-driven thread, now closed and written up.  Capstone paper
`theory/math/completeness_without_completeness.md` (5 parts, 15 §); detail chapters
`theory/math/completeness_relocated.md` + `probe_twist_conic.md` (§0–13); essay
`theory/essays/real_without_completeness.md`.  Every link is a ∅-axiom theorem.

The chain, each link a theorem (Lean module in parentheses):

  1. **Completeness is relocated, not constitutive** — a real is a decision
     procedure vs ℚ; completion is a leaf of the import graph, unconditional for
     algebraic (φ closed-form modulus) / modulus-gated for transcendental
     (`Real213/AbCutSeq`, `PhiAbCut`, `EulerCut`, `PiCut`, `Analysis/CompletionTower`,
     `ModulusMonoid`, `ResolutionQuantitative`, `ModulusForm`).
  2. **The probe lattice is P-twisted** — `P = [[2,1],[1,1]] ∈ SL₂(ℤ)`,
     order-preserving, `det = NS − NT = 1` (`MobiusProbeTwist`).
  3. **φ is the twist's fixed cut**; e is not (`PhiProbeFixed`, `ProbeTwistFixedPoint`).
  4. **The wobble = `f⁻¹`, backward Pell** (`ProbeTwistDynamics.twist_undoes_step`).
  5. **The wobble's shape = the conic `Q = m² − mk − k²`** — every orbit on its
     hyperbola `Q = N`, disc 5 = NS+NT (`ProbeTwistConic.Q_preserved`).
  6. **The divergence has a form** — cross-det `Wₙ` (discrete Wronskian): φ `±1`,
     e `−n!`, π Wallis (`EulerDivergenceForm`).
  7. **Divergence depth** — lift the form until constant: algebraic 1 < e 3 < π 6 <
     Liouville ∞.  Depth ≠ irrationality measure μ (μ collapses alg=e=π=2); depth =
     the P-recursive / holonomic rank (`DivergenceLadder`, `DivergenceDepth`).
  8. **Finite depth ⟺ P-recursive** (`DepthPRecursive`).  Classical CF data: exp/tan
     family (e, tanh1 = [0;1,3,5,7,…]) finite depth; π/arctan1/ln2 irregular.
  9. **The ratio-lift axis** — `ratioLift` differences the exponent
     (`ratio_is_diff_on_exponent`), so `ratioN^h` floors exactly `c^{poly deg h}`;
     `h` = exponent's polynomial degree (`DepthTower`).
  10. **The `(h,d)` coordinate is an ordinal `< ω²`** — `lex_wf`,
      `no_infinite_descent` (`DepthOrdinal`).
  11. **Third axis = recursion into the exponent** — value-height = 1 +
      exponent-height; `value_floors_iff_exponent_floors` (`DepthExponentRecursion`).
  12. **`ε₀` is not the end** — `ratioN` cannot cross one exponential layer
      (`2^{2ⁿ}` is a fixed point: `ratioN_dexp`, `dexp_not_const`); the heights are
      the classical ordinal hierarchy, with no top (`DepthDoubleExp`).
  13. **Naming the ceiling-raising = the residue** — referencing the whole tower is a
      diagonalisation `diag f n = f n n + 1` escaping every level (`diag_not_in_seq`);
      this is `cantor_general` = the same non-surjectivity as the foundational residue
      `self_covering_closure`.  The arc closes onto its origin (`DepthCeilingResidue`).

Depth-arc Lean: 9 modules, audited PURE / 0 dirty.  Wired into the `Cauchy.lean`
umbrella; full `lake build` clean.

## Closed and promoted (durable homes — do not re-derive)

| Topic | Source of truth | Narrative |
|---|---|---|
| Real-number completeness arc (links 1–13) | `Lib/Math/Cauchy/Depth*`, `Divergence*`, `EulerDivergenceForm`; `Lib/Math/Real213/*`; `Lib/Math/Analysis/*` | `theory/math/completeness_without_completeness.md` (+ `completeness_relocated`, `probe_twist_conic`); essay `theory/essays/real_without_completeness.md` |
| φ self-similarity (form / count `5^L` / limit-ratio φ) | `Lib/Math/SelfSimilarityBridge`, `Real213/{PhiAsCut,PhiConvergence,PhiNormInvariant,PhiAbCut,FibCassiniNat}`, `PellFibCutBridge` | `theory/math/phi_self_similarity.md` |
| The residue / self-covering closure | `Lens/FlatOntologyClosure`, `Lens/PredicateSelfEncoding`, `Theory/Raw/{PrimitiveTower,Lambek}` | `research-notes/G152`, `theory/essays/tower_atlas.md` |
| P-orbit closure (P self-defining; every axis sees `{3,2,1}`) | `Mobius213/Px/{CharPolySelf,MobiusSelfForm,ConvergentDet}`, `Theory/Atomicity/OrbitForcing`, `Mobius213SignatureAxisCatalog` | `theory/essays/{every_axis_sees_p,p_orbit_closure_master}.md` |
| General Cauchy completeness (cut space closed under limits) | `Analysis/CauchyCompleteValid` | `completeness_relocated.md` |

PURE Nat helper infrastructure (reuse, don't re-derive): `Meta/Nat/NatDiv213`
(`mul_div_self_pure`, `mul_div_cancel_left_pure`, `pow_succ_div`, `add_div_right_pos`),
`Meta/Nat/PureNat` (`pow_add`, `mul_assoc`, `add_mul`), `Meta/Tactic/NatHelper`
(`succ_sub`, `add_sub_cancel_right`, `add_sub_of_le`, `sub_add_cancel`).

## Next targets (detailed)

### A. Depth-floor = P-orbit, as one theorem (`research-notes/G154`)

The strongest unclaimed result the arc exposes.  Three sub-trees independently land
on `det = 1` as the floor: the divergence ladder (`const_reaches_floor`), convergent
geometry (`ConvergentDet.convergent_det`, Cassini `Wₙ = ±1`), and atomic forcing
(`OrbitForcing`).  **Depth measures distance from atomicity**: a real's generating
recurrence departs from P's autonomous self-definition by a polynomial of degree
`depth − 2`.  Promotable brick:

> **`depth_floor_is_det_one`** — `reachesFloor` with cross-determinant floor value 1
> ⟹ the convergents satisfy the autonomous Pell/Cassini step (`pellNormStep`), i.e.
> lie on a P-orbit.

Hinge between the analysis-side ladder and the atomic-side forcing.  Main obstacle:
`Wₙ` is `Nat`-abstract in `DivergenceLadder`, the P-orbit is `Int`-valued in
`Mobius213PellInvariant` — bridge needs the sign-free Nat reading of `Wₙ = ±1`
matched to Cassini `a² + 1 = a·b + b²`, via the additive Int→Nat routing already used
in `PellFibCutBridge` (no `Int` subtraction).  Est. one focused session.

### B. `depth_floor_is_det_one`'s converse + the finite-depth recurrence (formal P-recursive)

Currently "finite depth ⟺ P-recursive" is `DepthPRecursive` at the difference-degree
level plus a classical (C) bridge to holonomic rank.  Open: make the bridge a
theorem for the e and π cases — exhibit the explicit polynomial-coefficient recurrence
their convergent data satisfies (e: coeff `n+1`, degree 1; π: degree 4) and prove
`polyDepth d` matches.  This closes the (C) gap in chapter §III/§9–10.  **Architecture
for A+B**: `research-notes/G155` (HolonomicReal type — bundle the recurrence data with
a derived `CertifiedModulus` so the API is unconditional within the holonomic class;
the unproven `Holonomic.toCertifiedModulus` is exactly this target).

### C. The genuine third-axis closure (ratio-on-exponent reaches `c^{c^{poly}}`)

`DepthDoubleExp` proves `ratioN` *cannot* cross one exponential layer; `DepthExponent‑
Recursion` proves the recursion bridge `value-height = 1 + exponent-height`.  Open:
assemble these into a positive theorem that the recursion *does* floor `c^{c^{poly}}`
at the right coordinate (apply the `(ratio,diff)` ladder to the exponent, then to its
exponent), and pin the ordinal rank `ω^r · d` for a depth-`r` tower as a Lean
statement, not just the classical (C) reading.  This is the proven path from `ω²`
toward `ω^ω`.

### D. Liouville's coordinate beyond the two-operator system

`DepthDoubleExp` shows Liouville `c^{k!}` has no finite `(h,d)`.  Open: give it a
coordinate in the *recursion* hierarchy of C — its exponent `k!` floors under ratio
(`k! ↦ k+1`), so it should sit at a specific transfinite coordinate.  Formalising
"the exponent is itself an `expSeq`-like object" is the frontier toward `ε₀`.

### E. Tower duality (longer-horizon, conceptual)

Two open dualities flagged in `tower_atlas.md` / `G154` §2:
  - **GRA-tower ↔ CD-tower**: level `n` of property-loss ↔ level `5−n` of Reading-iso
    gain.
  - **Depth-ladder ↔ Cayley–Dickson tower**: both property-loss/gain towers bottoming
    at a 213-forced floor, both controlled by `5 = d = NS + NT`.  Whether these are
    readings of one tower (as `tower_atlas` argues for the P-orbit towers) or genuine
    coincidence is open.
  - **Flexibility over a non-associative base** (`CDDoubleFlexible.lean` cross-pair
    crux) — the long-standing Cayley–Dickson open item.

## Notes / hygiene

  - **Verify Lean SEQUENTIALLY before commit**: `rm <file>.olean` → `lake env lean
    <file>` (exit 0) → `lake build <module>` → `tools/scan_axioms.py <module>` (N pure
    / 0 dirty) → commit.  build-green ≠ purity-green; never trust cached "Build
    completed"; never parallelise build with scan.
  - **PURE arithmetic**: every Lean-core division-cancel / `pow_add` / `add_sub_cancel'`
    pulls `propext`.  Use the `Meta/Nat` helpers listed above; build new PURE chains
    from `Nat.div_eq_sub_div`, induction, and `Int213.*` additive routing (no `Int`
    subtraction, no `omega`, no `Nat.max`, no `funext` for function-equality — use
    pointwise).
  - `decide` on `Subtype`/`Raw` equality pulls `propext` via `DecidableEq Raw`; use
    `Tree.noConfusion` (for `a ≠ b`) and `of_decide_eq_true` (not `decide_eq_true_eq`).
  - **Repo-first**: grep + INDEX before coding a "missing" cell (`PredicateSelfEncoding`
    and the `add_div_right_pos` helper were both nearly rebuilt).
  - N_U = d^(d²) is **deprecated**; don't cite it as a constant, don't use
    "ℝ = final boss" framing.
