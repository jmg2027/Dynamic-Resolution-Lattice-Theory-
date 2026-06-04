# Hierarchical Placement — post-M11 final state (+ 2026-05-18 audit)

**Companion document to** `lean/E213/ARCHITECTURE.md` and
`lean/E213/docs/CONSOLIDATION_PROTOCOL.md` (R1–R11 rules).

This document captures the post-Stage-M11 state of the E213 tree:
**every directory has an umbrella file**, and **every umbrella links
the actual files in that directory**.  The §6 "deferred-28"
inventory, which was the only remaining caveat after M11, is now
fully resolved — verified 2026-05-18 by re-running `lake build`
on each entry.  See §6 for the per-cluster status.

The directive that triggered this audit (Mingu, 2026-05-XX):

> 이런 식으로 E213디렉토리 밑의 모든 lean 파일들을 전부 수정 /
> Analysis가 제일 모범케이스인듯 아마도 / 그러고 나면 이제 본질적으로
> 계층적 설계에 대해서 완전하게 어느것이 어디로 들어가야하는지 모두
> 결정 가능할 것

Translation: apply the Analysis-style spec-as-code organization to
all lean files under E213/, after which the hierarchical design is
fully determined.  This document records the determination.

## 1. Spec-as-code coverage (final tally)

Every top-level layer + every Math/Physics sub-tree has an umbrella.

### 1.1 Top-level layer umbrellas (8/8)

| umbrella | files | imports | covers |
|---|---|---|---|
| `E213/Term.lean`     | 23  | 23  | bare-metal type theory + `Tactic/` macros |
| `E213/Theory.lean`   | 27  | 27  | Raw monad, Atomicity/, Tools/ |
| `E213/Lens.lean` | 89  | 79  | Lens algebra (10 deferred — pre-existing API drift) |
| `E213/Meta.lean`       | 27  | 27  | reflective primitives + meta tactics |
| `E213/App.lean`        | 1   | 1   | Simplex executable |
| `E213/OS.lean`         | 12  | 12  | HodgeConjecture/Bridges + Physics/Capstones |
| `E213/Math.lean`       | 469 | 38  | imports topical sub-umbrellas (not files directly) |
| `E213/Physics.lean`    | 127 | 14  | imports topical sub-umbrellas (not files directly) |

### 1.2 Math/ sub-tree umbrellas (17/17)

All Math sub-trees have full umbrella coverage; broken-file counts
are pre-existing API drift, documented inline in each umbrella.

| sub-tree         | files | imports | broken |
|---|---|---|---|
| Analysis         | 74  | 11  | 0 (chapter-style: 7 sub-dir umbrellas + 3 top-level files; DyadicSearch grew from 5→9 files for the G31 trajectory-as-witness IVT) |
| AxiomSystems     | 4   | 4   | 0 |
| Cauchy           | 14  | 14  | 0 |
| CayleyDickson    | 29  | 20  | 9 (heavy variants, LipschitzLens, R5Vacuity, ZSqrtProduct) |
| Choice           | 4   | 4   | 0 |
| Cohomology       | 217 | 208 | 9 (CupAW.LeibnizSmall, Dyadic API drift, etc.) |
| Diagonal         | 2   | 2   | 0 |
| Hyper            | 3   | 3   | 0 |
| Infinity         | 8   | 8   | 0 |
| Irrational       | 6   | 6   | 0 |
| Linalg213        | 8   | 8   | 0 |
| ModArith         | 9   | 9   | 0 |
| Modulus          | 4   | 4   | 0 |
| Polynomial213    | 2   | 1   | 0 (core file at sibling `Polynomial213.lean`) |
| Real213          | 45  | 45  | 0 |
| Tactic           | 5   | 5   | 0 |
| Trajectory       | 1   | 1   | 0 |

### 1.3 Physics/ sub-tree umbrellas (14/14)

All Physics sub-trees have full umbrella coverage; 0 broken.

| sub-tree    | files | imports |
|---|---|---|
| AlphaEM     | 6   | 6   |
| Atomic      | 20  | 20  |
| Basel       | 2   | 2   |
| Cosmology   | 6   | 6   |
| Couplings   | 11  | 11  |
| Foundations | 17  | 17  |
| Hadron      | 8   | 8   |
| Higgs       | 4   | 4   |
| Mass        | 3   | 3   |
| Mixing      | 5   | 5   |
| Nuclear     | 6   | 6   |
| Simplex     | 7   | 7   |
| Substrate   | 13  | 13  |
| YangMills   | 5   | 5   |

## 2. Vertical-layer placement (mechanical)

Per `ARCHITECTURE.md` §0, every file's natural layer is mechanically
determined by its import closure.  Run `tools/layer_audit.py` to
recompute.  Post-M11 distribution:

| top-folder    |  Term |  Theory |  Lens | Meta | App | total |
|---|---|---|---|---|---|---|
| Term/         | 24     | 0        | 0          | 0    | 0   | 24    |
| Theory/       | 0      | 27       | 0          | 0    | 0   | 27    |
| Lens/         | 0      | 0        | 105        | 0    | 0   | 105   |
| Meta/         | 0      | 0        | 0          | 30   | 0   | 30    |
| App/          | 0      | 0        | 0          | 0    | 1   | 1     |
| Lib/Math/     | 49     | 235      | 180        | 9    | 0   | 525   |
| Physics/(127) | 0      | 116      | 11         | 0    | 0   | 127   |
| Prelude.lean  | 1      | 0        | 0          | 0    | 0   | 1     |

**Reading**: `Term/X.lean` files are at  Term by both path AND
mechanical computation.  `Math/X.lean` files' mechanical layer is
distributed across {Term, Theory, Lens, Meta} — the path
encodes the *topical* axis only.

## 3. Layer-claim violations: 0

No file imports a layer above its claimed level.
`tools/layer_audit.py` reports `## Violations: 0`.

## 4. Layer downgrade hints (28 informational)

These files could mechanically move to a lower layer; they're not
violations, just below-claimed-cost.  Listed for future audit.

  - **App → Theory**: `App/Simplex.lean` (1)
  - **Theory → Term**: 7 files in `Theory/Atomicity/`
  - **Lens → Theory**: `Lens/LensCore.lean` (1)
  - **Lens → Term**: 8 files in `Lens/AxiomLenses/Core/`
  - **Meta → Lens**: 5 files (`SelfRecognising`, `Universal/`, etc.)
  - **Meta → Term**: 6 files (`AxiomMinimality`, `Tactic/Derive*`, etc.)

These are *path locality* decisions: e.g. `Theory/Atomicity/Alive`
is mechanically Term-level but lives under Theory/ because it
groups topically with the rest of `Atomicity/`.  Moving them down
is optional and can be deferred.

## 5. Spec-as-code rule compliance (R1–R11)

| rule | description | post-M11 status |
|---|---|---|
| R1  | File name = chapter title; no session-residue suffixes  | clean |
| R2  | Every dir has umbrella `<DirName>.lean`                 | **complete** |
| R3  | Sub-namespace preservation when merging                 | clean |
| R4  | Drop pure-bundle capstones; keep unique content         | 232 sealed deleted |
| R5  | Verify all sub-tree umbrellas individually              | enforced in M11 |
| R6  | Cycle prevention                                        | clean |
| R7  | Sub-cluster at 3+ files; sub-directory at ~30+          | applied |
| R8  | Verify-and-clean after every merge stage                | enforced |
| R9  | Iterative umbrella with broken-file exclusion           | applied |
| R10 | Nested-type-namespace caveat (doubled `X.X.*`)          | documented + applied |
| R11 | Tactic-emitted hardcoded paths                          | M7 + M11b + M11i fixed |

## 6. Deferred / known-broken inventory — RESOLVED (2026-05-18 audit)

All previously-deferred files build clean on the current branch.
Audit re-run 2026-05-18 verified `lake build E213.<file>` ✔ for
each entry below.  The "28 deferred" tally is now **0 deferred**.

### 6.1  ~~Lens (10 deferred)~~ — RESOLVED

All 10 build clean.  Repairs landed in commit `687ff8b7`
(2026-05-06 Lens namespace audit) — `open E213.Meta` drift,
`Math.DiagonalClassification` revival, lens-refines combinator
fixes.  Verified 2026-05-18 audit.

### 6.2 ~~CayleyDickson (9 deferred)~~ — RESOLVED

All 9 build clean (`CDTower`, 4 `*Heavy` variants, `LipschitzLens`,
`R5Vacuity`, `ZSqrtProduct`).  Repairs from the 2026-05-06 CD-cluster
revive pass.  Verified 2026-05-18 audit.

### 6.3 ~~Cohomology (9 deferred)~~ — RESOLVED 2026-05-06

All 9 files restored (commit pending).  Method:

  - `CupAW.LeibnizSmall` — replaced the `pattern_eq` (function-eq)
    rewrite with the per-index-pointwise `pattern_eq_at` chain
    (mirroring the existing `Leibniz.lean` n=5 proof).
    `CupAW.LeibnizScaling` was indirect (LeibnizSmall import).
  - `Dyadic.ArithFSM.V1to2` — moved `ArithFSM1.padTo2` def into
    the `ArithFSM.V1` namespace so dot-notation `m.padTo2` resolves.
    `Hierarchy` analogous: `ArithFSM2.padTo3` added at
    `ArithFSM` namespace, `ArithFSM1.padTo3` moved to V1.
  - `Dyadic.AlgebraicDegree`, `NumberTheory213` — added explicit
    `open` lines for `padTo2_bits_eq` / `padTo3_bits_eq` and the
    LCM/Pisano/Pell helpers (open dependencies were lost in
    the M14 namespace consolidation).
  - `Dyadic.Archive.{EdgeSignature, SubwordComplexity}` —
    added missing `import` of `TierBridge` (where `bit13` lives).
  - `Dyadic.Pell.ProperBridge` — added `open` for
    `pellProperFSMmod`, `pisano_predict_proper`, and the three
    `pellProperN_run_period_*` theorems.

### 6.4 Meta + OS (0 deferred — fully clean post-M11h)

  - Meta: `VerifyConjugationTest.lean` repaired in M11b.
  - OS: `HodgeTate.lean` unblocked by `Bipartite/Filled.lean` fix in M11h.

## 7. Future hierarchical work

### 7.1 Layer downgrades (optional)

The 28 downgrade hints (§4) are candidates for path migration if
topical locality cost is acceptable.  The §6 cleanup that this
work was blocked on is now complete; downgrade work can proceed
when convenient.

### 7.2 ~~Polynomial213 layout~~ — RESOLVED 2026-05-18

The asymmetry was resolved by choosing option 2 (uniform umbrella):
`Polynomial213.lean` is now a pure umbrella over
`Polynomial213/{Core, Sound, Ineq}.lean`.  Core holds the type
defs + Horner evaluation; Sound holds the `eval_*` soundness
lemmas; Ineq holds the `eval_le_of_add` witness pattern.

### 7.3  Lens namespace audit (RESOLVED 2026-05-06)

The 10 deferred Lens files have been repaired (commit `687ff8b7`):
  * `open E213.Meta` (deleted ns) → `open E213.Lens.Instances.{Bool,
    Parity}` and a new `E213.Lens.Diagonal` module restored from the
    M14-Phase-F-deleted `Math.Diagonal.Classification`.  (2026-05-13
    Session H: `Lens/Diagonal.lean` 흡수되어 `Lens/Properties/Diagonal.
    lean` — namespace `E213.Lens.Properties.Diagonal`.)
  * `Hypervisor.Lens` → `Lens` namespace drift in 14 additional files.
  * `Kernel.Congruence.Lens.equiv_slash_congruence` rename in
    `Lens.Algebra.Corresp`.

`lake build E213.Lens` now reports 122/122 ✔.  CayleyDickson (9) and
Cohomology (9) deferred clusters remain.

### 7.4  Padic / ProfiniteSeq full ∅-axiom (RESOLVED 2026-05-06)

`Lib/Math/NumberSystems/Hyper/Padic.lean` and the entire upstream chain are now
**12/12 PURE** (commit pending).  Verified via `#print axioms`:

  * **Padic capstones (5/5)**: `padic_family_cauchy`,
    `padic_family_limit_zero`, `padic_tower_refines`,
    `padic_familyCauchy`, `padic_limit_all_zero`.
  * **ProfiniteSeq leaves (7/7)**: `factorial_pos`, `factorial_dvd`,
    `factorial_eventually_zero_mod`, `factorial_seq_cauchy`,
    `factorial_seq_limit_zero`, `factorial_seq_familyCauchy`,
    `factorial_seq_limit_all_zero`.
  * **Lens-layer dependents** also PURE:
    `Lens.Instances.Leaves.ModNat.{leavesModNat_view_eq, divides_refines}`,
    `Lens.Instances.Cauchy.eventually_class_unique`.

Method (two-stage hardening):
  1. **Quot.sound elimination**: add `Nat213.{zero_mod,
     mul_mod_right}` (term-mode, hook-compliant); inline `omega` as
     `Nat.le_succ_of_le` / `Nat.le_trans` / `Nat213.mul_assoc`.
  2. **propext elimination**: add `Nat213.le_max_{left, right}`
     (term-mode via `Decidable.casesOn` + `if_pos`/`if_neg`);
     add `AddMod213.{add_mod_gen, mod_mod_of_dvd}` (Lib/Math layer,
     PURE via existing `add_mod_left` + `div_add_mod` machinery);
     route `ModNat` and `Cauchy` callers through these.

`AddMod213` is at Lib/Math layer but still importable from
Lens-layer `ModNat.lean` because Lib is the *horizontal* topical
ring — not in the vertical `{Term < Theory < Lens < Meta < App}`
ordering.  The architecture allows Lens → Lib (verified by
`tools/layer_audit.py`: 0 violations).

Earlier diagnosis ("function-eq between ℕ → Bool families")
was incorrect: actual root cause was `omega` + Lean-core
`Nat.{add_mod, mod_mod_of_dvd, mul_mod_right, zero_mod,
le_max_*}` (all `[propext]`-tainted).

## 8. Verification command set

```bash
cd lean
lake build E213.Term E213.Theory E213.Lens E213.Meta \
            E213.App E213.OS E213.Lib.Math E213.Lib.Physics
# Each should report ✔ Built E213.<Layer>.

python3 ../tools/layer_audit.py | head -10
# Expects: ## Violations: 0
```

If both pass, the spec-as-code is complete and the placement
hierarchy is determined.
