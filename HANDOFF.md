# Session Handoff — 2026-05-XX (axiom-strip migration begun)

## Branch

`claude/start-session-zR5Nn`, pushed to origin, working tree clean.

This session began the systematic elimination of `propext` and
`Quot.sound` from `lean/E213/`, replacing them with 213-native
∅-axiom equivalents.  Multiple infra modules were built and
4 leaf files migrated to strict ∅-axiom.

## TL;DR

Goal: every theorem in `lean/E213/` should `#print axioms` → "does
not depend on any axioms" (strict ∅-axiom, stronger than the
DRLT-allowed `{propext, Quot.sound}` baseline).

Progress this session:
  - 213-native helper trio in `Kernel/Tactic/`: Omega213 (extended),
    Nat213 (11 lemmas), Fin213 (1 lemma).
  - 4 leaf files migrated: `Math/Pigeonhole.lean`,
    `Firmware/Atomicity/NonDecomposable.lean`,
    `Firmware/Atomicity/ArityForcing.lean`,
    `Math/Infinity/Pair.lean`.  Total 12 public theorems verified
    strict ∅-axiom this session (24 including helpers).
  - `tools/scan_axioms.py` — efficient per-theorem axiom auditor.
  - Catalog of axiom-leak surfaces in
    `lean/E213/Kernel/Tactic/AXIOM_FREE_STATUS.md` (read first
    before continuing).

Remaining: hundreds of files.  Each requires:
  1. Replace `omega` / `simp` / `simpa` with 213-native equivalents.
  2. Find leaks via `tools/scan_axioms.py <module>`.
  3. Bisect dirty theorems to identify Lean-core lemmas that bring
     propext, add 213-native versions to Nat213/Fin213/etc.
  4. Verify with `#print axioms` → "does not depend on any axioms".

## Source-of-truth pointers

  1. `lean/E213/Kernel/Tactic/AXIOM_FREE_STATUS.md` — migration
     status, methodology, helper catalog, leak surfaces.
  2. `lean/E213/Kernel/Tactic/OMEGA213_MIGRATION.md` — original
     omega → omega213 guide.
  3. `lean/E213/ARCHITECTURE.md` — overall layer architecture.
  4. `tools/scan_axioms.py` — per-theorem axiom auditor.

## Discovered leaks (cataloged in AXIOM_FREE_STATUS.md)

1. `by omega` → propext, Quot.sound  (use `omega213`)
2. `by simp`, `by simpa` → propext  (manual `rw` chains)
3. `Nat.sub_add_cancel` → propext  (use `Nat213.sub_add_cancel`)
4. `Nat.le_sub_of_add_le` → propext  (use `Nat213.le_sub_of_add_le`)
5. `Nat.add_left/right_cancel` → propext  (use Nat213 versions)
6. `Nat.div_lt_iff_lt_mul.mpr` → propext  (TODO — iff destructor)
7. `Fin.elim0` → propext  (use `Fin213.absurd0`)
8. `(0 : Fin (n+1))` literal → propext  (explicit `⟨0, _⟩`)
9. `Prod.mk.injEq.mpr` → propext  (use `congr/congrArg` chain)
10. `match n, h2, h4 with | 2,_,_ | 3,_,_ => ...` (small-case match
    with constraint hypotheses) → propext + Quot.sound  (use
    `match Nat.lt_or_ge n k with | Or.inl ... | Or.inr ...` cascade
    + `Nat.le_antisymm`)

## Open Problems carried forward

### From prior session (still relevant)

  1. **Source-vs-cache discrepancy** (HANDOFF prior §1).  Several
     pre-existing source-level breakages were surfaced this session
     because axiom probing forces fresh re-elaboration that bypasses
     olean cache:
       - `Math/Cohomology/Hodge/Star.lean` — uses unqualified
         `subsetIdx` / `kSubset` (need `open` of Delta.Core /
         SimplexBasis).  Currently masked by olean cache.
       - `E213.Math.Infinity.<sym>` references where namespace is
         actually `E213.Infinity` — fixed in commit `eae6bb6` for
         Godel.lean and ModArith/* (13 files).
       - `E213.Hypervisor.Lens.LeavesModNat` should be
         `E213.Hypervisor.Lens.Leaves.ModNat` — fixed in same
         commit.
     **TODO**: A force-clean rebuild (`rm -rf .lake/build && lake
     build`) will surface remaining source bugs.

  2. **sync_namespaces.py multi-namespace bug** — unchanged.

  3. **WIDE topical sub-clusters** (Math/Cohomology, Math/Real213) —
     unchanged, informational.

### New from this session

  4. **scan_axioms.py + olean invalidation chain.**  When a file is
     edited, all dependent files' oleans are invalidated.  If those
     dependents have pre-existing source bugs (cf. #1), probing
     fails.  Workflow: fix bugs as encountered, or scan only files
     in known-clean chains.

  5. **Vast scope.**  ~600 files have dirty theorems.  Realistic
     completion requires extending Nat213/Fin213/Int213 catalogs
     with 50-100+ more lemmas to cover common patterns (Nat.div,
     Nat.mod, Nat.dvd, Int operations).

## Verification snapshot

```
$ python3 tools/layer_audit.py | head -8
# Layer audit — 909 .lean files under lean/E213/
Vertical: {'Kernel': 0, 'Firmware': 1, 'Hypervisor': 2, 'Meta': 3, 'App': 4}
## Violations: path layer < natural layer  (0)

$ cd lean && lake build
Build completed successfully.

$ python3 tools/scan_axioms.py E213.Math.Pigeonhole \
    E213.Firmware.Atomicity.NonDecomposable \
    E213.Firmware.Atomicity.ArityForcing \
    E213.Math.Infinity.Pair
# 12 pure / 0 dirty (public theorems)
```

## Suggested next-session entry points

### A. Continue axiom-strip migration

Pick the next leaf with dirty theorems.  Run `scan_axioms.py
<module>` first to see baseline.  Bisect leaks via
`_AxiomProbe.lean`, add helpers to Nat213/Fin213.

Candidate next files (smallest first):
  - `Math/IntHelpers.lean` (Int — needs new `Int213.lean` module)
  - `Math/Cohomology/Dyadic/SignatureBipartite.lean` (mod arith —
    needs `Nat213.cases_lt_succ_succ` or similar)
  - `Firmware/Atomicity/Five.lean` (linear Diophantine — needs
    helper `solve_2a_plus_3b_eq_5` or generic small-case search)
  - `Meta/BitPatternUniqueness.lean` (mod 2 + power-of-2 reasoning;
     8 omegas)

### B. Extend Nat213 catalog (high-leverage)

Pre-build commonly-needed 213-native versions of:
  - `Nat.div_lt_iff_lt_mul.mpr` → `Nat213.div_lt_of_lt_mul`
  - `Nat.le_div_iff_mul_le.mpr` → `Nat213.le_div_of_mul_le`
  - `Nat.mod_eq_zero_iff_dvd` → one-direction implications
  - `Nat.add_mod`, `Nat.mul_mod`, `Nat.mod_mod` (forward)
  - `Nat.dvd_sub`, `Nat.dvd_add`, `Nat.pow_dvd_pow`
  - parity helpers: `Nat.even_succ`, `Nat.odd_succ`

Each addition unblocks dozens of files.

### C. Build `Int213.lean`

Same pattern as Nat213 but for Int.  Math/IntHelpers needs:
  - `Int213.le_of_neg_pos`  / similar omega-replacements
  - `Int213.mul_self_eq_zero` (one-direction)

### D. Force-clean rebuild + fix source bugs

`rm -rf lean/.lake/build && lake build` will surface masked bugs.
Fix as encountered — namespace mismatches, broken refs, etc.
This will make scan_axioms reliable.

## Recent commits (this session)

```
128b5a8  AXIOM_FREE_STATUS: catalog Nat213 + 4 migrated files
eae6bb6  Fix pre-existing namespace mismatches surfaced by axiom probing
a126133  Nat213: add_left/right_cancel; Math/Infinity/Pair migrated
4e6f6c0  Nat213.cases_lt_two/three; ArityForcing migrated to ∅-axiom
b8bdd8a  Nat213 expanded; NonDecomposable migrated to ∅-axiom
a2bfefd  Kernel/Tactic: factor Nat213, Fin213 helpers (modularization)
f0591b2  Math/Pigeonhole: first ∅-axiom migration
```

7 commits, +24 ∅-axiom theorems verified, 11 Nat213 + 1 Fin213
helpers cataloged, 13 pre-existing namespace bugs fixed.

## Key precision results (unchanged this session)

| Observable | DRLT | Observed | Error |
|---|---|---|---|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.48 ppb** |
| Magic numbers 7/7 exact, etc. (full table in CLAUDE.md) |

## Authors

  - Mingu Jeong (Independent Researcher) — theory.
  - Claude (Anthropic) — formalization, 213-native helper authoring,
    systematic axiom-strip migration.
