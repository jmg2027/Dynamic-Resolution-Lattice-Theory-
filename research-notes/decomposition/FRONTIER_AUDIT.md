# Frontier audit — stale "missing leg" claims across the decomposition notes

*Audit triggered by `practice/connections.md`'s discovery that three geometry notes
(`curvature.md`, `de_rham.md`, `lie_theory.md`) declared the Riemann/Christoffel/Bianchi tower
"absent" while `Lib/Math/Geometry/TensorCalculus.lean` (23/0 PURE) had already built it. Method:
for every `practice/*.md`, extract each "X is absent / not built / conceptual-only / no `Y` object /
grep returns zero" claim, then grep `lean/E213/` for the named object **under all plausible
namespaces** (the connections lesson: the object often lives where the note didn't grep), and
classify ABSENT vs STALE. A claim is marked STALE only if grep confirms the object exists AND
`tools/scan_axioms.py` confirms it is PURE.*

## Verified PURE anchors used in this audit

| Module | Scan | Key decls |
|---|---|---|
| `Lib/Math/Geometry/TensorCalculus.lean` | **23/0 PURE** | `riemUp`, `riem_antisym_jk`, `riem_flat`, `chris1_symm`, `chris1_metric_compat`, `chris2_*`, `ricciFromRiem`, `riem_bianchi1`, `riemLow_*`, `scalar_einstein` |
| `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean` | **10/0 PURE** | `bracket`, `bracket_antisymm`, `bracket_self`, `tr_bracket_zero`, `jacobi`, `bracket_leibniz` |
| `Lib/Math/NumberSystems/Real213/Mat2/Mat2Killing.lean` | **PURE (0 dirty)** | `adMap` (adjoint), `killing`, `killing_symmetric`, `killing_eq_trace_form`, `killing_gram`, `adX_traceless` |
| `Lib/Math/NumberSystems/Real213/ModularGeometry/NoetherCurrent.lean` | **15/0 PURE** | `current`, `density`, `continuity_eq`, `noether_local` (`∂·j=0 ⟺ Aut-invariant`), `noether_global`, `noether_local_implies_global` |
| `Lib/Math/Algebra/Linalg213/DerivedSeries.lean` | **21/0 PURE** | `gcomm`, `gcomm_id_iff_commute`, `commSet`, `derived_S3_step1` (`[S₃,S₃]=A₃`), `derived_A3_step2` (`[A₃,A₃]={e}`), `solvable_S3`, `three_cycle_commutator_S5` |
| `Lib/Math/Algebra/Icosahedral/A5Perfect.lean` | **9/0 PURE** | `A5` (60 even perms), `A5_card`, `gcommP_even` (commutator of evens is even — structural), `commutators_subset_A5`, `A5_subset_commutators` (`decide`), `a5_perfect` (`[A₅,A₅]=A₅`), `a5_not_solvable` (q=−1 pole) |

## Audit table — claimed-absent objects

| Note | Claimed-absent object | Status | Closing module : theorem / residual |
|---|---|---|---|
| `curvature.md` | "no Riemann/Ricci tensor, no `R^ρ_{σμν}`, no Bianchi, no Christoffel" | **STALE (already corrected in note)** | `TensorCalculus` (23/0); note's "Dropped citations" already carries the connections.md correction. No edit needed. |
| `de_rham.md` | abstract-index Riemann tensor | **STALE (already corrected in note)** | Note lines 176-177, 224-225 already say "the abstract-index Riemann tensor IS built — `TensorCalculus.lean`, 23/0". No edit needed. |
| `de_rham.md` | smooth `Ω^k(M)` form bundle + de Rham iso `H*_dR ≅ H*_sing` | **ABSENT** | Genuine: no smooth form bundle / no de Rham comparison iso. Distinct from the tensor tower. Future Lean target. |
| `lie_theory.md` | "no `jacobi` theorem on `Mat2` commutators" (Leg 3, line 171) | **STALE** | `Mat2Bracket.jacobi` (10/0 PURE). Contradicts the note's own line 154 ("`jacobi` BUILT"). **FIXED.** |
| `lie_theory.md` | "No `bracket`/`Lie`/`Jacobi`/`adjoint`/`Killing` object in `lean/E213`" (break list, line 249) | **STALE** | `Mat2Bracket` (bracket/jacobi) + `Mat2Killing` (adMap=adjoint, killing). **FIXED.** |
| `lie_theory.md` | "scratch (verified, not committed)" anchor for the commutator (table line 234) | **STALE** | `Mat2Bracket.lean` is committed, 10/0 PURE. **FIXED.** |
| `lie_theory.md` | "the Killing form `tr(ad∘ad)` are conceptual" (Leg 4, line 177) | **STALE** | `Mat2Killing.killing` / `killing_gram` (PURE). Note line 267-271 already says "NOW BUILT"; Leg 4 leftover contradicted it. **FIXED.** |
| `lie_theory.md` | tangent `ε` / `T_e G` (`I+εX`, `ε²=0`); BCH matrix-exp weld | **ABSENT** | Genuine: no infinitesimal/tangent object, no matrix exp / BCH. The `h→0` residue. |
| `noether.md` | "No `Noether`/`conserved current`/`∂_μ j^μ` theorem exists in `lean/E213`" (line 152) | **STALE** | `NoetherCurrent.noether_local` (`∂·j=0 ⟺ Aut-invariant`, 15/0 PURE) — under `ModularGeometry/`, not `Physics/` where the note grepped. **FIXED.** |
| `noether.md` | smooth/analytic variational current over a field | **ABSENT** | Genuine residual (strictly smaller): the *smooth* `∂_μ j^μ` over a differentiable field, vs the discrete `current`/`continuity_eq`. |
| `galois_correspondence.md` | "no derived series `[G,G]⁽ⁿ⁾`, no `is_solvable` predicate" (Revelation §4, line 208; header line 20) | **STALE** | `DerivedSeries.solvable_S3` / `derived_series_S3` (21/0 PURE). The note's own body (§D, lines 146-159) already cites this as "NOW GROUNDED"; the header + Revelation §4 leftovers contradict it. **FIXED.** |
| `galois_correspondence.md` | A₅ perfectness `[A₅,A₅]=A₅`; general `isSolvable` predicate | **PARTLY FIXED** | A₅-perfectness now PROVEN (`A5Perfect.a5_perfect`/`a5_not_solvable`, 9/0 PURE): structural upper bound + `decide` lower bound over 60 elements (the un-deduplicated `commList` makes the closure ∅-axiom in ~13s). Only the general `isSolvable` predicate with a proven subgroup-generation step remains. **FIXED (A₅ leg).** |
| `galois.md` | "Solvability by radicals / insolvability of the quintic — entirely absent" (line 203) | **STALE (partial)** | The derived-series / solvable-tower mechanism IS built for S₃ (`DerivedSeries`, 21/0). The quintic / A₅-perfectness remains absent. **FIXED** (split into built-tower + remaining quintic gap). |
| `galois.md` | "even the simplest real Galois group is conceptual" / `Gal` object (line 200-202) | **ABSENT** | A *named* `Gal(L/K)` group-of-a-field-extension object; `galois_correspondence.md` later found a worked `Gal(ℚ(ζ₅)/ℚ)≅C₄` instance via `CyclotomicFive`, but no general `Gal` constructor. Left as-is. |
| `representation.md` | `d>1` Killing / `tr(ad∘ad)` trace character (line 256) | **STALE (already corrected in note)** | Note already cites `Mat2Killing.lean` as closing it. No edit needed. |

### Genuinely-absent claims surveyed and confirmed ABSENT (no edit — honest gaps)

These were grep-checked against all plausible namespaces and confirmed genuinely absent; left as recorded:

- `model_theory.md` / `curry_howard.md` / `godel.md` — no FOL `Formula`/`Sat`/`Derivable`; no typed `Term`/β-reduction/cut-elimination. (Proof-theory / logic-syntax instance absent.)
- `sheaf_theory.md` / `topos.md` — no `Presheaf`/`Sheaf`/`Stalk`/`Cech`/`SheafCohomology`; no named topos / `SubobjectClassifier Ω` / `GeometricMorphism` / `LawvereTierney`.
- `fundamental_group.md` / `knots.md` / `two_cells.md` — no `fundamentalGroup`/`π₁`/`pathHomotopy`/`CoveringSpace`/`vanKampen`; no ambient-isotopy quotient (the colimit/`q=−1` corner + ambient-space construction).
- `tropical.md` — no `TropicalSemiring`/`tropicalize`/`dequantize`/`softmax`/`NewtonPolygon`.
- `surreal.md` — no `Surreal`/`Game`/`{L|R}` type or surreal arithmetic.
- `information_geometry.md` — no divergence functional / Fisher metric (Hessian) / Bregman / dual-flat connections object.
- `quantum_mechanics.md` — no Hilbert space / inner product `⟨ψ|φ⟩` / amplitude `|·|²` / measurement-collapse map.
- `zeta_euler.md` — no analytic `ζ(s)` object; Euler product not stated as a theorem.
- `fourier.md` — no character-orthogonality `Σ_x χ(x)=0`, no DFT/Plancherel.
- `spectral.md` / `graph_theory.md` — no general `d>1` symmetric-operator spectral theorem; no arbitrary-graph `L=D−A` Laplacian eigen-equation.
- `topology.md` — no arbitrary-cover quantifier / non-trivial Heine–Borel.
- `measure.md` / `probability.md` — no general σ-additive measure / countable-cover infimum.
- `ergodic_theory.md` — no measure-preserving-transformation `T_*` / Birkhoff-average / Koopman objects.
- `free_corner.md` — free monad `μ` / νF carrier (flagged structurally blocked, with `MuNuMirror` docstring corroborating).
- `yoneda.md` / `category_theory.md` / `adjunction.md` — no explicit Hom-functor object / `PSh(C)` / packaged completeness; HoTT structurally forbidden.
- `ordinals.md` — no transfinite arithmetic / `ε₀` as a closed ordinal (completed-limit cap).
- `padic.md` — no Ostrowski exhaustiveness classification.
- `entropy.md` — general real-valued `H=−Σ p log p` (non-dyadic) absent (note already says "entropy is NOT absent" for the core; only the general-real-log composite open).

## Summary count

- **Notes corrected this session (in place): 4** — `lie_theory.md`, `noether.md`, `galois_correspondence.md`, `galois.md`.
- **STALE claims fixed: 7** (4 in `lie_theory.md` collapsed into a coherent correction; 1 in `noether.md`; 1 in `galois_correspondence.md`; 1 in `galois.md`).
- **STALE-but-already-corrected (no edit needed): 3 notes** — `curvature.md`, `de_rham.md` (Riemann tower), `representation.md` (Killing).
- **Genuinely ABSENT (confirmed, left as honest gaps): ~22 distinct objects** across ~20 notes (see lists above). The dominant residual shape is the `Real213`-cut / `h→0` smooth-completion (smooth metric, `Ω^k(M)`, tangent `ε`, analytic current, Fisher Hessian, Hilbert space, analytic ζ) and the colimit/quotient `q=−1` corner (isotopy quotient, sheaf gluing, free monad).

## High-value genuinely-absent gaps worth a future Lean target

1. **Smooth `Real213`-cut metric instantiating `dg`/`ddg`** (geometry cluster: `connections.md`/`de_rham.md`/`curvature.md`/`lie_theory.md` all share it) — would weld the abstract-index `TensorCalculus` tower to an actual differentiable metric and close the single largest shared residual.
2. **The `lim_{loop→0}(holonomy−I)/area` weld** tying `HolonomyLattice.holonomy` (finite) to `TensorCalculus.riemUp` (infinitesimal) — they live in separate modules; the analytic identification is named-not-built.
3. **A general `isSolvable` predicate** with a proven subgroup-generation step — the last remaining piece of the insolvability-of-the-quintic leg. (A₅ perfectness `[A₅,A₅]=A₅` is now BUILT: `A5Perfect.a5_perfect`/`a5_not_solvable`, 9/0 PURE, the q=−1 pole dual to `solvable_S3`'s q=+1.)
4. **The de Rham comparison iso `H*_dR ≅ H*_sing(·;ℝ)`** on a smooth form bundle — the differential-topology twin of (1).
