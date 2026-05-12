# MATH_AUDIT/ — chunked audit of `lean/E213/Lib/Math/`

`Lib/Math/` is **797 .lean / 71,140 lines / 47 sub-clusters** —
too large for a single audit doc.  Per Mingu Jeong (2026-05-12)
plan, audited in **9 thematic chunks (A–I)**, each file ≤ 250
lines target.

## Chunk catalog (priority-ordered)

| # | File | Clusters | Files | Status |
|---|---|---|---|---|
| 1 | `C_algebra.md` | CayleyDickson, Group, Polynomial213, Linalg213 | 77 | ✓ initial pass (2026-05-12) |
| 2 | `A_foundations.md` | NatHelpers, Modulus, ModArith, Choice, AxiomSystems, Tactic, Logic, Search | 42 | ✓ initial pass (2026-05-12) |
| 3 | `G_cohomology.md` | Cohomology, HodgeConjecture | 161 | ✓ initial pass (2026-05-12) |
| 4 | `F_dyadic_fsm.md` | DyadicFSM | 116 | ✓ initial pass (2026-05-12) |
| 5 | `E_analysis.md` | Analysis, CascadeCalculus, ODE, Multivariable, Functional, Measure, Trajectory | 104 | ✓ initial pass (2026-05-12) |
| 6 | `B_numerical.md` | Real213, SignedCut, Cauchy, EpsilonDeltaModulus, Complex, Hyper, Infinity, Irrational, NumberGrid | 134 | ✓ initial pass (2026-05-12) |
| 7 | `D_topology.md` | Combinatorics, Topology, LevelTopology, OperationTopology, AngleStructure, TriangularTower, BipartiteDecomp, CartesianVsDisjoint, Diagonal | 42 | ✓ initial pass (2026-05-12) |
| 8 | `H_probability.md` | Probability, Information | 33 | ✓ initial pass (2026-05-12) |
| 9 | `I_misc.md` | Extras, DialogueAudit, GenerationRule, PatternCatalog, UniverseChain | 46 | ✓ initial pass (2026-05-12) |

## Phase 1 cross-Math summary (Explore pass 2026-05-12)

- **22 Theory.Internal violations** — CayleyDickson 압도 (~14),
  NatHelpers (~2), Cohomology (~2), 기타.
- **39 Theory.* direct imports** — 대부분 `Theory.Raw`/`Atomicity`
  (architectural OK), Closed.Nat213Bridge / Atomicity.Five 등 일부
  검토.
- **0** App / Lens.Internal / Term.Internal / Mathlib.
- **0 actual sorry** (R5Vacuity 의 "sorry" 는 docstring comment).
- **PURE 2654 / DIRTY 129 / 0 sealed** (~95% PURE).
- **16 tiny clusters** (1–4 files) — fold candidates.

## Audit 완료 — chunk-별 위반 분포 (2026-05-12)

| Chunk | Files | Violations | Notable |
|---|---|---|---|
| C (Algebra) | 77 | 20 | CayleyDickson 압도 |
| A (Foundations) | 42 | 7 | AxiomSystems/Choice 주제적 |
| G (Cohomology) | 161 | 1 | best-organized (HodgeConjecture API.lean) |
| F (DyadicFSM) | 116 | 0 | ~95% PURE |
| E (Analysis) | 104 | 0 | ODE 중복 (top-level vs Analysis 내부) |
| B (Numerical) | 134 | 5 | Infinity 의 Raw cardinality (주제적) |
| D (Topology) | 42 | 0 | ~100% PURE, 가장 깨끗 |
| H (Probability) | 33 | 0 | ~100% PURE |
| I (Misc) | 46 | 5 | UniverseChain (주제적, Raw axiom chain) |
| **Total** | **755** | **38** | **~95% files clean** |

Math 의 ring 위반 ~5% — Phase 1 의 "22 Theory.Internal" + 16
Theory.Raw 직접 reach (대부분 주제적).  실제 spec violations 중
정리 대상은 ~20 (CayleyDickson 의 Internal reach-in 그룹).

## Per-chunk content 형식

§0 Summary (cluster list + file/line counts)
§1 Ring violations (Theory.Internal / Theory.* / 기타 reach-in)
§2 Cluster docstring overview (1 line per cluster)
§3 Naming/조직 평가 (fold 후보, misalignment)
§4 Axiom status (PURE/DIRTY 분포)
§5 처리 priority (Quick wins / Mid / Long)
§6 결정 보류 marker

## Reference

- `research-notes/THEORY_AUDIT.md` (§1–4 stress-format)
- `research-notes/LENS_AUDIT.md` (2-tier API pattern)
- `lean/E213/ARCHITECTURE.md` (Ring discipline)
- `STRICT_ZERO_AXIOM.md` (PURE/DIRTY canonical)
