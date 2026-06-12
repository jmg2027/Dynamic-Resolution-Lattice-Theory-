# theory/meta/

Meta-analysis chapters mirroring **`tools/`** (the Python scanner
suite) rather than `lean/E213/Lib/`.  These chapters narrate the
scanner work, the closure-pattern taxonomy, and the
cardinality-cut-off methodology.

The strict three-tier discipline (`CLAUDE.md` "Three-tier
discipline") maps `theory/<area>/` to `lean/E213/Lib/<area>/`.
Meta-analysis closure lives in `tools/*.py` instead, so promotion
criteria H1-H4 adapt: H1 (purity) + H2 (build clean) → H1'
(scanners pass `--help`) + H2' (`lake build` still clean, since
scanners can be re-run).  Per `lean/E213/docs/PROMOTION_PATTERNS.md`,
this is the **destination-variant** form of Pattern 1.

## Chapters (8)

| Chapter | Source |
|---|---|
| [`scanner_suite.md`](scanner_suite.md) | `tools/{ast_*,syntax_*,falsifier_*}.py` (11 scanners) |
| [`raw_derivation_levels.md`](raw_derivation_levels.md) | `tools/{ast_typesig,ast_callgraph}_scan.py` + content theorems |
| [`cardinality_cutoff_principle.md`](cardinality_cutoff_principle.md) | `Cohomology/Fractal/AurifeuilleanFullCutoff.lean` (28 PURE) |
| [`cardinality_cutoff_applications.md`](cardinality_cutoff_applications.md) | 6 Lean files in `Cohomology/Fractal/` (191 PURE) |
| [`methodology_patterns.md`](methodology_patterns.md) | Closure-work methodology: Patterns #1-#20 + Reduction patterns #1-#6 |
| [`multiplicity_doctrine.md`](multiplicity_doctrine.md) | Patterns #17 + #20 + four canonical instances (Real213, Derivative, Cup, Modulus) |
| [`pure_lean_patterns.md`](pure_lean_patterns.md) | PURE Lean funext-avoidance pattern catalog (State Accumulator, Bundled Subtype, Setoid Category, Residual Induction) |
| [`boundary_discipline.md`](boundary_discipline.md) | The residue/Lens boundary behind unification, equality, and error: the α/β split + shared-generator criterion, the 2-polarity failure structure, the matched pair of instruments, and the ℤ-uniqueness corollary (`vp_eq_zero_of_gt` vs `cut`/`zpseq_no_finite_certificate`).  Working log: `research-notes/frontiers/general_theory_metaanalysis.md` |

## Action-items registry

The 24-item registry the scanner suite surfaced, plus nine
per-sub-tree deep dives that elaborated each candidate, are closed
to every item.  Closure summary lives in `scanner_suite.md`
§"Open frontier".

## Layout

```
theory/meta/
├── INDEX.md                                ← this file
├── scanner_suite.md                        ← 11-scanner suite + key findings + cross-branch protocol
├── raw_derivation_levels.md                ← (α) logical / (β) structural / (γ) operational taxonomy
├── cardinality_cutoff_principle.md         ← scale-matching cut-off methodology (Hunter ⇔ Aurifeuillean exemplar)
├── cardinality_cutoff_applications.md      ← six-direction application family (B/D/A/C/E/F, 191 PURE)
├── methodology_patterns.md                 ← reusable proof / refactor patterns (#1-#20 + reduction patterns)
├── multiplicity_doctrine.md                ← framework-internal coexistence (4 instances: Real213, Derivative, Cup, Modulus)
└── pure_lean_patterns.md                   ← PURE Lean funext-avoidance pattern catalog (4 architectural patterns)
```
