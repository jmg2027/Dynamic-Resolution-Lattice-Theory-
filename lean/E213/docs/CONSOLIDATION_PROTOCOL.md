# CONSOLIDATION_PROTOCOL.md — leaf-directory consolidation procedure

Procedure for cleaning up a Physics/ (or Math/) leaf directory that
contains exploration-trace files: V1/V2/V3 variants, Phase3*, Tight/
Tighter/Sharp progressions, Milestone, WithTail, Unified, etc.

Derived from the 2026-05-05 `Physics/FamousCoincidences/` consolidation
(commits `396585c` rename + `623e377` absorption).  The same procedure
applies to all subsequent leaves.

## Core insight (don't forget)

*"Naming pattern alone does NOT determine what to do."*  V137 might be
a version-number progression OR a "1/137" digit-start workaround.
Phase3* might be a stale exploration trace OR a meaningful sub-topic.
**Read the actual statements + check destinations before deciding.**

The most common state: the file's content is *already absorbed
elsewhere in a more natural form* — the leaf is a deep-research
exploration trace that survived past its absorption.  Default
expectation: most leaf-directory variant content is redundant.

## 13-step procedure

### Phase A — inventory

1. **List files**: `ls <leaf>/*.lean`.  Note total count + naming
   patterns (V*, Phase*, *Tight*, *Sharp*, *Milestone*, *V2*).

2. **Read headers** (~25 lines each): identify per-file topic.
   Cluster by apparent role (variant? supplement? canonical?
   exploration trace?).

3. **Theorem inventory**: `grep -E "^theorem |^def " <files>`.
   Capture every public name + its statement line.

### Phase B — destination discovery

4. **Statement-level grep**: for each substantive theorem
   statement (e.g. `NS * NT = 6`, `d^(d²)`, `NT² = 4`), count
   other files that state the same:

       grep -rl "<statement-pattern>" lean/E213/ --include="*.lean"

   High count (10+) means widely-duplicated atomic identity → likely
   already canonicalized in `Kernel/MonomialAxioms.lean` or
   `Physics/AtomicCorrespondences/AtomicSuperCatalog.lean`.

5. **Theorem-name grep**: for each theorem name (e.g. `koide_atomic`),
   find other files using the same name:

       grep -rln "<thm-name>" lean/E213/ --include="*.lean"

   Hit in another file ⇒ name conflict OR canonical absorption already
   exists.  Both are signals to delete the duplicate.

6. **Caller / import discovery**:

       grep -rln "import E213.<leaf-namespace>" lean/E213/ --include="*.lean"

   List all consumers.  For each, check whether the import is
   actually used (theorem references) or just transitive.

### Phase C — classification

7. For each theorem in the leaf, classify into one of:

   - **(a) Redundant — already absorbed**: same statement (or
     stronger) exists in a natural topical file.  → Delete.
   - **(b) Unique with natural destination**: rare statement that
     belongs in a specific topical file (e.g. SU(5) reps in
     `YangMills/SU5Roots`).  → Move + delete.
   - **(c) Unique multi-reading capstone**: bundled `∧` of multiple
     atomic readings (no single natural home).  → Absorb into
     `Physics/AtomicCorrespondences/AtomicSuperCatalog.super_catalog`
     (or a designated cluster catalog).
   - **(d) Real version-progression artifact**: stale Tight/Sharp/
     Phase3 form genuinely superseded by a Master/Capstone in the
     same dir.  → Delete the older, keep the canonical.

8. **Read destination files** (Phase C-(b),(c)) tail-end to confirm
   the namespace structure + check there's no name collision.

### Phase D — execution (single atomic commit)

9. **Absorb** content per the classification:
   - Append theorems to chosen destination file (preserve the
     statement text; rename if there's a collision).
   - Update the destination's docstring/header to mention the
     absorption (optional but helpful for navigation).
   - Extend any `super_catalog` capstone with the new conjuncts.

10. **Delete leaf files**: `git rm <file>` for each.  If the
    entire directory becomes empty, the directory is auto-removed
    by git.

11. **Update callers**: rewrite `import` lines to point at the new
    destination (or delete the import if no actual usage).

12. **Update navigation docs**:
    - `lean/E213/INDEX.md` — sub-tree list, file counts
    - `lean/E213/ARCHITECTURE.md` — sub-cluster list
    - `CAPSTONE_INDEX.md` — old leaf entries → new destination entries
    - `README.md` (root) — Physics sub-tree mention if present
    - `research-notes/AUDIT_PASS_<date>_lean.md` — file-count table
    - per-directory INDEX.md if exists

### Phase E — verification

13. **Build + axiom invariants**:

       cd lean && lake build              # must report "Build completed successfully."
       python3 tools/scan_all_axioms.py   # PURE/DIRTY/sealed counts

    Real DIRTY count must not increase.  Sealed-by-design count
    may shift if seal entries reference paths that moved.

14. **Single atomic commit** with message structure:

        Leaf N — <leaf>/ <action: rename | absorb | delete>

        <user directive verbatim if pivotal>
        Investigation outcome: <one-paragraph finding>
        Destinations + classifications: <table>
        Removed: <list>
        Updated: <list>
        Build clean.  No theorem signatures changed.

## Common patterns observed

| Pattern | Likely meaning | Action |
|---|---|---|
| `V137`, `V137Tight`, `V137Tighter` | progressive precision attempts toward 1/α_em | usually consolidate into `MasterCapstone` (or whichever holds full term-stack) |
| `Phase3Derivation`, `Phase3Sharp`, `Phase3Manifesto` | stale Phase-3 marathon trace | **almost always delete** if 0 importers (verified pattern from Leaf 3 Higgs/Phase3Derivation: literal aliases of canonical theorems) |
| `Bound`, `BoundTight` | tight bound *extension* (not progression) — adds lower bound to canonical | merge into the canonical (Leaf 2 verified: BoundTight is strict superset of Bound) |
| `Mass`, `MassFinitist` | finitist re-derivation of same observable | usually 0 importers — atomic-identity restatements already covered by canonical (Leaf 3 verified) |
| `MagicNumbers`, `MagicNumbersAtomic`, `MagicNumbersFalsifier`, `MagicNumbersPhase3Derivation` | observable + atomic reading + falsifier + phase trace | **inspect content**: `Atomic` is real (unique decompositions); `Phase3` is alias-only (delete); `Falsifier` may be alias-only despite naming — verify with theorem read (Leaf 4 verified MagicNumbersFalsifier had no falsification logic, just rebundled equalities — deleted) |
| `V1`, `V2`, `V3`, `V4` (no number-encoding role) | could be sub-topics OR variants | inspect each file's actual content |
| `WithTail`, `WithoutTail`, `Unified` | term-coverage variants | usually `MasterCapstone` is the canonical with all terms |

## Stale-citation sweep (do as you go)

Files often contain docstring citations to artifacts that were
deleted in earlier audit passes.  Sweep these whenever editing a
file's docstring:

| Stale citation | Status | Replacement |
|---|---|---|
| `lib/drlt.py:NNN` | deleted (Python ref impl removed) | drop the citation entirely |
| `ch01-ch22`, `ch09 sec 6.1` | `book/chapters/` deleted (per Stage 6 audit) | drop or replace with `lean/E213/` module path if still relevant |
| `SM_NNN`, `eq NN` | old paper-marker (papers/ deleted) | drop |
| `PAPER.md`, `PAPER2.md` | superseded by `seed/AXIOM/` (per `06_formalization.md` §7.2) | redirect to `seed/AXIOM/<chapter> §<ref>` |
| `R12Codomain`, `R3Codomain`, `R4Codomain` | renamed 2026-05-05 (`seed/AXIOM/99_history.md` §9.1) | use `CommBinaryCodomain` / `NonVanishingCodomain` / `ConjugationCodomain` |
| `derive_r4_codomain`, `#verify_r4` | tactic renamed | `derive_conjugation_codomain` / `#verify_conjugation` |

## "Orphan + alias" rule of thumb

A file is *practically orphan* when EITHER:
  (i) **0 importers**, OR
  (ii) only transitive importers (importer file doesn't reference
       any of its theorems, just the import line — Leaf 4
       MagicNumbersFalsifier ↪ Phase3Capstone pattern)

If practically orphan AND its theorems are mostly:
  - `theorem foo := canonical_theorem_name`  (literal alias)
  - `theorem foo : <atomic identity already in Kernel/MonomialAxioms or AtomicSuperCatalog>`
  - `*_capstone` bundles repackaging existing canonical theorems
  - `*_falsifier` bundle that encodes no actual falsification
    logic (just `decide`-trivial equalities)

→ **Confidently delete.**  No need to "find a home" — the content
is fully absorbed in canonical files.  Verified pattern on:

  - `Higgs/MassFinitist.lean`        (Leaf 3, 0 importers)
  - `Higgs/Phase3Derivation.lean`    (Leaf 3, 0 importers)
  - `Nuclear/MagicNumbersPhase3Derivation.lean` (Leaf 4, 0 importers)
  - `Nuclear/MagicNumbersFalsifier.lean` (Leaf 4, 1 transitive
    importer — *naming* "Falsifier" was misleading; content
    inspection showed alias-only)

**Naming alone is not classification.**  A file named
`*Falsifier.lean` may genuinely encode falsification (`Mass/NoFourthGen`,
`YangMills/WMassFalsifier` are real falsifiers) OR may just be a
narrative-framing wrapper around `decide`-trivial atomic identities.
Read the theorems before deciding.

## Caller-usage check (Phase B refinement)

When grep finds importers, distinguish:

  - **Active importer**: the importing file uses ≥ 1 theorem from
    the imported module (grep theorem names + check for refs).
  - **Transitive importer**: import line exists but no theorem
    reference — the import is dead code or only matters for some
    other downstream import chain.

A file with only transitive importers is effectively orphan.
Deletion is safe IF the transitive importer is itself active and
the dependency-chain function (e.g. providing namespace exports,
instances) is preserved through other imports.

## What NOT to do (lessons from FamousCoincidences/)

  - Do NOT rename V1-V4 to topic names without first checking
    whether content is absorbed elsewhere.  (Did this in commit
    `396585c` — had to revert/re-do via `623e377`.)
  - Do NOT preserve a "deep research artifact" file just because
    its statements are correct.  If the statements are absorbed,
    the file is dead weight.
  - Do NOT skip the destination grep — relying on filenames alone
    misses the `koide_atomic` (same theorem name in two files,
    one a duplicate).
  - Do NOT do this in multiple commits — atomic single commit
    keeps revertability + git mv history clean.

## When to ask the user

  - Theorem statement is unique AND has no obvious natural home
    (genuinely orphan).
  - Destination decision is between two roughly-equal candidates.
  - Deletion would lose information that nothing in the codebase
    ever recomputes.
  - The leaf encodes a *physical claim* that you suspect is wrong
    (e.g., a Phase3 derivation that contradicts the corrected spec).

## Cross-reference

  - First leaf execution: commits `396585c` (rename) + `623e377`
    (absorption + deletion).

---

# Reorganization rules (codified 2026-05-05 from M1–M5 lessons)

These rules govern Math/Physics tree reorganization beyond the
13-step leaf-consolidation protocol above.  Established via the
AlphaEM 17 → 6 + Real213 182 → 108 cleanup work.

## R1 — File name = chapter title

Sorted `ls <dir>/` is the table of contents of a textbook for that
sub-tree.  Implications:

  - **Drop session-residue suffixes**: `*Mega`, `*Showcase`, `*Catalog`,
    `*Final`, `*Higher`, `*High`, `*Coverage`, `*More`, `*Generic`,
    `*Mid` (when not topical), `*Combinator`, `*Decide`.
  - **Drop `Phase XX`-named files**: per CLAUDE.md "phase 같은 이해할
    수 없는 중간 과정 내용들은 삭제 필요".  Real content gets a topic
    name (e.g., `PhaseACMinimumProposition` → `MinimumProposition`).
    Pure-bundle Phase capstones get deleted outright.
  - **Each file = one coherent topic** (CLAUDE.md repo organization §1).

## R2 — Every directory has an umbrella `<DirName>.lean`

Per the Physics convention (`Physics.lean` → `Physics/AlphaEM.lean`
→ `Physics/AlphaEM/*.lean`).  Importing the umbrella pulls in the
whole sub-tree.  The umbrella sits **alphabetically adjacent** to
its directory — sorted `ls` puts the entry-point first by
filesystem convention.

Umbrella file structure:
  1. `import` lines for every `.lean` in the directory
     (alphabetical within the body)
  2. Single docstring describing the sub-tree's scope + sub-namespaces

Lean grammar requires `import` lines BEFORE any other top-level
declaration, including doc comments — put imports first, docstring
last.

## R3 — Sub-namespace preservation when merging

Files merged into one `<Topic>.lean` retain their original
namespaces as **sub-namespaces** inside the merged file.  External
`open E213.Physics.AlphaEM.V137 (...)` declarations across the
codebase stay valid without symbol rename.  Only the import line
changes (`import …V137` → `import …Brackets`).

## R4 — Drop pure-bundle capstones; keep unique content

Phase capstone files of the form `theorem phaseXY_capstone : P₁ ∧
… ∧ Pₙ := ⟨lemma₁, …, lemmaₙ⟩` where each `lemmaᵢ` is proven
in an upstream file are **pure packaging** — delete them.  Verify:
`grep` for the capstone theorem name's external usage; if zero
callers, delete.  Files whose entire content is one such bundle:
delete the file.  Files with mixed content: drop the bundle
theorem, keep the rest.

## R5 — Verify all sub-tree umbrellas, not just the default `lake build`

CLAUDE.md says "verify: `cd lean && lake build`".  The default
target builds only `E213.lean` (Kernel/Firmware/Hypervisor) per its
own header.  **Math/Physics sub-trees are NOT in the default
closure.**  Verification must include:

```bash
cd lean
lake build E213.Math.Real213
lake build E213.Math.Analysis213
lake build E213.Physics.AlphaEM
# etc — every umbrella touched by the change
```

Otherwise cascade breaks (e.g. transitive imports broken when a
Phase capstone is deleted) go undetected.

## R6 — Cycle prevention when merging

When two files `A → B` (A imports B) merge into a single file `C`,
and B already imports something that depends on A, the merge
creates a cycle.  Before merging, trace the import closure of every
sub-namespace's required deps.  If merge creates a cycle, **split**:
keep the depended-on namespaces in one file, the dependent ones in
another (`<Topic>Combinators.lean` or similar suffix).

## R7 — Topical sub-clustering at 3+ files; sub-directories at ~30+

CLAUDE.md "Sub-cluster as soon as 3+ thematically-related files
appear".  When a sub-tree exceeds ~30 files, introduce
sub-directories matching natural chapter divisions.  Each
sub-directory gets an umbrella `.lean` per R2.

## R8 — Verify-and-clean after every merge stage

After each merge stage:
  1. `lake build E213.<sub-tree>` — verify the merged sub-tree
  2. `grep -rln "import E213\.\(deleted modules\)$" lean/` — find
     stale imports
  3. `grep -rln "open E213\.\(deleted modules\)" lean/` — find
     stale opens
  4. Auto-add missing direct imports for files using `open
     E213.Math.Real213.X`: a script that ensures `import
     E213.Math.Real213.X` is present (since transitive imports
     through deleted Phase capstones may have broken)

## Common-patterns table

| Pattern | Files matching | Action |
|---|---:|---|
| `*Mega` / `*Coverage` / `*Final` capstone bundle | 6 | Delete |
| `*High` / `*Higher` / `*Generic` polynomial-degree extension chain | 9 | Merge into base file with sub-namespaces |
| `Phase XX*Capstone` 1-thm bundle | 11+ | Delete |
| `Phase XX*Proposition` (multi-thm research content) | rare | Rename to topic name |
| `Has*` / `Is*` typeclass-name files | most | Optional rename to drop prefix (`HasDyadicMVTWitness` → `DyadicMVTWitness`) |
| Pure `example` scratchpads (0 theorems) | 3+ | Delete |
| Re-opened namespace blocks (`end NS / namespace NS` adjacent) | many | Collapse to single block |

## Cross-reference

  - M1 (Real213 Phase artifacts): commits `8e7e630` + `8b1f0b3`
  - M2 (chain consolidation): commits `7b95ddf` + `38161bb`
  - M3 (FluxMVT chains): commits `6a5cf5b` + `14bdd47` + `66e50dd`
  - M4 (full Math tree build fix): commit `4faa0a9`
  - M5a (Real213 umbrella): this commit

---

# Additional rules R9–R11 (M6–M7 lessons, 2026-05-05)

## R9 — Iterative umbrella with broken-file exclusion

When a sub-tree has many pre-existing broken files, build umbrella
**iteratively**: try with all files → identify broken set →
cascade-find transitive importers of broken → exclude all → document
in docstring.  Used in M6f (Cohomology 202/226) and M7
(CayleyDickson 11/29).

## R10 — Nested-type-namespace caveat

Lean 4 `structure X` inside `namespace X` creates path ambiguity:

```
namespace E213.Math.Foo.X    -- module
  structure X where ...      -- full name E213.Math.Foo.X.X
  namespace X                 -- nested
    def ext : ...              -- E213.Math.Foo.X.X.ext
  end X
end E213.Math.Foo.X
```

External files need BOTH `open E213.Math.Foo.X` AND
`open E213.Math.Foo.X.X` to access bare `ext`.  The type-defining
file should NOT open itself.

When method theorems (`mul_comm`, `conj_mul`) live in a separate
`XDomain.lean` rather than in the X namespace, type-class derivation
tactics fail.  **Move method theorems into the type namespace**.

## R11 — Tactic-emitted hardcoded paths

When namespace structure changes, audit custom tactics that emit
hardcoded fully-qualified names (e.g., `mkIdent
\`E213.Meta.ConjugationCodomain`).  Update tactic source to match
the actual class location.

## Cross-reference (extended)

  - M6a Cohomology Capstone deletes: `7851172`
  - M6b Physics + Cohomology cycle break: `7436e0b`
  - M6c Hyper / Diagonal: `b08bfb6`
  - M6d ModArith / Infinity: `c1a7b6f`
  - M6e Linalg213 missing-open cascade: `479c601`
  - M6f Cohomology iterative umbrella: `b8e3157`
  - M6g Math root umbrella: `b77f190`
  - M7 CayleyDickson partial + Tactic: `7eafd3f`
