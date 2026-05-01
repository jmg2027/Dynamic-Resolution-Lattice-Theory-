# AUDIT_GUIDE — Lean tree cleanup roadmap

Audit scope: 812 Lean files across `lean/E213/`.  This is a guide for
a **dedicated cleanup session** to perform after the merge.  Do NOT
do the cleanup blindly — this guide identifies *targets* and
*priorities*, but each consolidation requires verifying axiom load
preservation.

## Summary of issues

1. **77 `Dyadic*.lean` files** crammed into `Math/Cohomology/`
   — should be in their own `Dyadic/` subdirectory with sub-clusters.
2. **Versioning proliferation**: `v1, v2, v3` capstones still around
   (only latest needed for downstream).
3. **Incremental builds left as files**: `Predictor → 6 → 7 → 8`,
   `Legendre → Ext → 13_19` — only the final form is consumed.
4. **CupAWLeibniz family (20 files)** — many stepping stones to
   `Delta4LeibnizCapstone`.
5. **Exploratory files** mixed with main results
   (e.g., `DyadicSubwordComplexity`, `DyadicEdgeSignature`,
   `DyadicClassifier`).
6. **Research/ (303 files)** — likely lots of exploratory drafts.

## Cleanup ground rule (CRITICAL)

**Every file proposed for removal must be verified DISCONNECTED**:

```
$ grep -r "import E213.Math.Cohomology.DyadicXxx" lean/
```

If any *kept* file imports it → **DO NOT REMOVE**.  Either:
- Move the file (and update imports), OR
- Inline the content into the consumer.

After every batch of changes:
```
$ cd lean && lake build           # must pass
$ # axiom check on all capstones — must remain ≤ {propext, Quot.sound}
```

## Proposed directory structure (Math/Cohomology)

Current: 147 files flat in `Math/Cohomology/`.

Proposed:
```
Math/Cohomology/
├── Bipartite/        (Bipartite32, Bipartite32Betti, BipartiteFilled)
├── Cochain/          (Cochain*, ~4 files)
├── CupAW/            (Cup*, CupAW* — ~22 files; consolidation target)
├── Hodge/            (Hodge*, HodgeProp*, HodgeStar — ~5 files)
├── Universal/        (Universal*, UniversalProp* — ~8 files;
│                      consolidation target)
├── Delta4/           (Delta4Capstone, Delta4LeibnizCapstone)
├── Dyadic/           (77 files reorganized into sub-clusters)
│   ├── ArithFSM/     (15 files: ArithFSM, ArithFSM1, hierarchy,
│   │                   mod{5,7,11,13,17,19,23}, etc.)
│   ├── BitFSM/       (4 files: BitFSM, Bound, Converse, Examples)
│   ├── Pell/         (Pell*, PellProper* — ~13 files)
│   ├── Legendre/     (Legendre213, LegendrePisano* — ~5 files)
│   ├── Tribonacci/   (Trib*, ThueMorse — ~3 files)
│   ├── Lens/         (LCMClosure, Product*, PellLens*,
│   │                  CrossClassLens, SplitSplitLens — ~10 files)
│   ├── Capstones/    (NumberTheory213, Pell, Trib, Algebraic — keep
│   │                  ONE version each)
│   ├── Hierarchy/    (Algebraic Degree tower — 4 files)
│   ├── Signature/    (Signature, SignatureBipartite, SignatureInj,
│   │                  SignaturePredict, ConcretePellSig — 5 files)
│   └── Foundation/   (BitAuto2, Conjecture, Capstone, Forward*,
│                      Tier2Hardness, TierBridge, WalkUniversal,
│                      AtomicityConnection — ~10 files)
└── Misc/             (existing: K5, Fractal*, EulerClosed, Audit,
                       BettiKernel, EncodingBijection*, LeibnizFinding,
                       Paper1Chiral, Real213Bridge, SimplexBasis,
                       TopologyCompare, TrivialCases, WhyDimFive,
                       XorPairCombine, AlphaEMBridge — keep at root)
```

## Versioning consolidation targets

These accumulated through incremental development:

### Number theory capstones (DyadicNumberTheory213)
- `DyadicNumberTheory213.lean` (v1, 4-prime evidence)
- `DyadicNumberTheory213v2.lean` (7-prime)
- `DyadicNumberTheory213v3.lean` (D=5 + D=8) ← **KEEP**

Action: verify `v3` is the only consumer.  Remove v1 and v2.

### Pisano predictors
- `DyadicPisanoPredictor.lean` (4 primes)
- `DyadicPisanoPredictor6.lean` (6 primes)
- `DyadicPisanoPredictor7.lean` (7 primes)
- `DyadicPisanoPredictor8.lean` (8 primes) ← **KEEP**

Action: keep only `8`.  Note: `8` may import from earlier — check
and inline.

### Legendre-Pisano bridges
- `DyadicLegendrePisano.lean` (3-prime)
- `DyadicLegendrePisanoExt.lean` (4-prime)
- `DyadicLegendre13_19.lean` (6-prime)

Action: consolidate into single file (`DyadicLegendrePisano.lean`)
with the 6-prime bridge as the canonical version.

### Pell lens composition
- `DyadicPellLens.lean` (3×5 → 20)
- `DyadicPellLensPairs.lean` (3×7, 5×7)
- `DyadicPellLensTriple.lean` (3×5×7)
- `DyadicPellLensCapstone.lean` (4-conjunct bundle) ← **KEEP**

Action: keep capstone + remove individual files (or consolidate
into one `Lens/PellComposition.lean`).

### CupAWLeibniz family (20 files)

Most are stepping stones to `Delta4LeibnizCapstone`.

Action:
- Identify what `Delta4LeibnizCapstone` consumes.
- Keep only those files.
- Consolidate remaining stones into single
  `CupAWLeibnizDelta4Steps.lean`.

### UniversalProp family (7 files)
`UniversalProp, UniversalProp31, 41, 42, 51, 52, 53`.

Action: identify final consumers, consolidate stepping stones.

## Exploratory file archival candidates

May be exploratory, not consumed downstream:

- `DyadicSubwordComplexity.lean` — exploratory complexity measure.
- `DyadicEdgeSignature.lean` — Fin 12 edge variant.
- `DyadicClassifier.lean` — early classifier.
- `DyadicConjecture.lean` — original conjecture statement.
- `DyadicCapstone.lean` — superseded by NumberTheory213*.

Process for each:
1. `grep -r "import .DyadicXxx" lean/` — find consumers.
2. If no consumer: archive to `lean/E213/Archive/` (preserve trail,
   don't delete).
3. If consumer exists: keep + mark intent in file header.

## Research/ folder (303 files)

Largest cleanup target.

Process:
1. Build dependency graph: which Research files are imported by
   non-Research files?  Those are *load-bearing*.
2. Files only imported within Research/ → exploratory clusters.
   Group by topic, archive or consolidate.
3. Special cases:
   - `Research/Real213*` — Bishop-style constructive analysis.
     Likely organized; check Real213 phase capstones.
   - `Research/Universal*` (5 files) — compare with
     `Meta/UniversalLens*`.

## Meta/ folder (16 files)

Currently mixed: foundational metatheory + experimental lenses.

Suggested:
```
Meta/
├── Universal/        (UniversalLens, BitPattern, Q213, Nat2 — 6 files)
├── Variants/         (BoolLens, MaxLens, ParityLens, PathLens,
│                       ZMod6Lens, LensCatalog, LensCharacterisation)
└── Demo/             (RawInductionDemo, SelfRecognising,
                        CUniquenessBridge)
```

## Per-cluster strategy summary

| Cluster | Files | Strategy |
|---|---|---|
| Dyadic ArithFSM | 15 | Move to `Dyadic/ArithFSM/` |
| Dyadic BitFSM | 4 | Move to `Dyadic/BitFSM/` |
| Dyadic Pell | 13 | Move + consolidate Lens variants |
| Dyadic Legendre | 5 | Consolidate to 2 files |
| Dyadic Capstones | 6 (versions) | Keep latest only |
| Dyadic Predictors | 4 (versions) | Keep `Predictor8` |
| CupAWLeibniz | 20 | Consolidate stepping stones |
| UniversalProp | 7 | Consolidate variants |
| Research/ | 303 | Dependency-graph-driven audit |

## Suggested cleanup-session workflow

Phase 1 — **Mapping** (read-only, ~1 hour):
1. `find lean -name "*.lean" | wc -l` — total count baseline.
2. For each cluster: `grep -lr "import E213.X.Y.Z" lean/` to map
   consumers.  Build a JSON or CSV with rows `(file, consumers, role)`.
3. Mark each file as: KEEP / MERGE-INTO-X / ARCHIVE / DELETE.

Phase 2 — **Versioning consolidation** (one cluster at a time):
1. Pick `DyadicNumberTheory213` cluster.  Verify only `v3` is
   load-bearing.
2. Delete v1, v2.  Run `lake build`.  Verify all axiom checks.
3. Repeat for `DyadicPisanoPredictor`, `DyadicLegendrePisano*`.

Phase 3 — **Directory reorganisation** (per sub-cluster):
1. Create `Math/Cohomology/Dyadic/` directory.
2. `git mv` files into sub-directories (preserves history).
3. Update imports: `E213.Math.Cohomology.DyadicArithFSM` →
   `E213.Math.Cohomology.Dyadic.ArithFSM`.
4. Run `lake build` after EACH sub-cluster move.

Phase 4 — **Stepping-stone consolidation** (CupAWLeibniz, UniversalProp):
1. Identify final theorem in each chain (e.g.,
   `delta4_leibniz_capstone`).
2. Inline intermediate lemmas if they're not used elsewhere.
3. Otherwise consolidate into single `*Steps.lean` per chain.

Phase 5 — **Research/ audit** (largest, last):
1. Build dependency graph.
2. Quarantine non-load-bearing files in `Research/Archive/`.
3. Document remaining files with role headers.

Phase 6 — **Final verification**:
```
$ cd lean && lake build               # must pass
$ # axiom audit on top capstones — ≤ {propext, Quot.sound}
$ git diff --stat HEAD~N HEAD         # show net file delta
```

Target: 800+ → ~400-500 files, with clear directory structure.

## Non-goals (DO NOT do during cleanup)

- ❌ **Refactor proofs**.  Keep proof bodies identical.  Cleanup is
  about *organization*, not *content*.
- ❌ **Strengthen theorems**.  If a stepping stone proves a weaker
  claim than the capstone, leave it as-is.
- ❌ **Add new theorems**.  Defer to dedicated session.
- ❌ **Touch axiom-load-affecting code**.  Any change that introduces
  new axioms is a regression.
- ❌ **Cleanup `Firmware/`, `Hypervisor/`, `OS/`, `Kernel/`, `App/`,
  `Physics/`** — these are well-organized layers.  Leave alone.

## Risk register

1. **Import cycle risk** when consolidating files.  Use:
   ```
   $ lake build E213.X.Y.Z 2>&1 | grep -i cycle
   ```
   to detect.
2. **Axiom regression**: any consolidation that changes proof terms
   may shift axiom load.  ALWAYS re-audit:
   ```lean
   #print axioms E213.Math.Cohomology.DyadicConjecture.X
   ```
3. **Hooks may block** large multi-file edits.  Chunk into smaller
   commits.

## Sequencing recommendation

If running sequential cleanup sessions:

1. **Session 1**: Versioning consolidation
   (NumberTheory213 v1+v2 → v3 only,
    PisanoPredictor → 8 only,
    LegendrePisano* → consolidated).
   Expected: ~10-15 files removed.

2. **Session 2**: Pell Lens consolidation
   (PellLens + Pairs + Triple + Capstone → single file).
   Expected: ~3-4 files removed.

3. **Session 3**: Dyadic directory reorganisation
   (move 77 files into `Dyadic/{ArithFSM, BitFSM, Pell, Legendre,
    Lens, Capstones, Hierarchy, Signature, Foundation, Tribonacci}/`).
   Expected: 0 file count change, large structural improvement.

4. **Session 4**: CupAWLeibniz consolidation.
   Expected: ~10-15 files removed.

5. **Session 5**: Research/ audit.
   Expected: 50-150 files archived/consolidated.

Each session ends with `lake build` clean + axiom re-audit.

## What the cleanup is NOT

This is *cosmetic + structural*.  After cleanup:
- Same axioms, same theorems, same precision results.
- Cleaner file organization.
- ~50% file count reduction (estimated).
- Clear hierarchy (Dyadic/, Universal/, etc.).

The mathematical content is *invariant*.  All achievements
(ToE Level 1-5, Universal Lens at ℕ²/ℚ², Pisano predictors,
0.07 ppm 1/α_em, etc.) remain identical.

## Authors

- Mingu Jeong (Independent Researcher) — theory, audit direction.
- Claude (Anthropic) — audit recommendations.
