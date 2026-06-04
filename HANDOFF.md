# Session Handoff — 2026-06-04 (residue-expression atlas + the Minkowski-`?` modular cocycle)

## Branch
`main` — all work committed and pushed.  `cd lean && lake build E213` ✓ (fresh
`rm -rf .lake/build` build clean, 1744 modules); `tools/scan_axioms.py` PURE on
every module touched this session; `/purity-check` clean (0 sorry / 0 axiom / 0
native_decide / 0 Mathlib).

This session established the **residue-expression atlas** — *the residue is
expressed multi-directionally, not by one mechanism* — and, on the `?`/period
sub-thread, rebuilt the bulk of classical **Eichler–Shimura** ∅-axiom, leaving a
single irreducible analytic atom.

## What Was Done This Session

### 1. The residue-expression atlas (foundational thesis)
"How is the essential residue expressed?" is **not** one phenomenon (Cantor
diagonal).  A cross-repo survey + new theorems show it is multi-directional:
- **negative face** (reached-by-none) = `object1_not_surjective` on different
  carriers (`reached_by_none.md` essay + `analytic_minkowski_residue`);
- **positive faces** = Möbius fixed-point, atomicity forcing, **graded cohomology**
  (degree × multiplicity × face);
- the cohomological axes split: **degree + multiplicity unbounded, face bounded**
  (`CupLadderResidueUnit.graduation_escapes`, `Simplex/FaceTerms.simplex_face_euler_zero`),
  unified by the residue unit `NS−NT = det P = 1` (`cup_ladder_graduation_is_residue_unit`).
- Honest negative recorded: "residue = a spectrum" is **rejected** (Steenrod/Massey
  vacuous at the `d=5` truncation).
Frontier: `research-notes/frontiers/residue_expression_atlas.md`.

### 2. The Minkowski `?` is the residue's modular cocycle (PURE) — and Eichler–Shimura rebuilt
`Real213/Minkowski*` (all ∅-axiom):
- `MinkowskiCocycle` (6) — `?`'s additivity defect is the bounding **Markov number**
  (Frobenius cross-determinants); twist = `SL(2,ℤ)` **Cayley–Hamilton** jump;
  off-tree defect `= det M · N.c`; weight-2 period = the `√(−1)` congruence.
- `MinkowskiGoldenExtremal` (1) — `φ` (Lagrange floor `√5`) is the extremal instance
  of the weight-2 period (Fibonacci spine).
- `MinkowskiPeriodIntegral` (5) — integration is ∅-axiom-native (dyadic Riemann);
  affine exact at depth 0; period integrands carry explicit moduli.
- `MinkowskiHigherWeightPeriod` (1) — the FTC/antiderivative integral
  (`Integration/`, `FluxMVT`) integrates `z²`,`z³` exactly: the **power rule is closed**.
- `MinkowskiPeriodRelations` (1) — the weight-2 period **is `S`'s eigenvalue** (the
  order-4 Gaussian generator); `S`/`U` orders `{4,6}` = the `(1+S)`/`(1+U+U²)` generators.
- `MinkowskiPeriodPolynomial` (12) — the **slash action on `V_2`** built; the
  weight-4 **period polynomial is `1 − X²`**, the unique line `ℤ·(1−X²)`.
- `MinkowskiModularSymbol` (5) — the **Manin** decomposition: the period contour is
  the Stern-Brocot sum of unimodular symbols (mediant preserves the determinant).
Narrative: `theory/essays/analysis/minkowski_as_modular_cocycle.md`.

### 3. Marathon cleanup (process / essay / org-audit / purity / ready-to-merge)
- `/process`: 2 sink violations decoupled; atlas frontier registered in `frontiers/INDEX.md`.
- `/essay`: `the_breadth_signature.md` (why ∅-axiom reaches every domain) saved;
  essays **49**; ledger rows 9–11 added.
- `/org-audit`: 8 orphan modules wired into umbrellas (`Real213.lean`, `AlphaEM.lean`);
  legacy-correction narration stripped from permanent-tier docstrings.
- `/purity-check`, `/ready-to-merge`: clean, READY.

## Current Precision Results (0 free parameters)
Unchanged this session — this was **math-frontier / foundations** work (modular
forms, the residue's expression modes), not a physics-constant edit.  Canonical
table: `catalogs/physics-constants.md`.

## Open Problems (Priority Order)
All recorded in `research-notes/frontiers/residue_expression_atlas.md` (+ `INDEX.md`).

### 1. The single analytic atom of the period thread
Higher-weight Eichler–Shimura is rebuilt ∅-axiom **except** the value of a modular
form `f`'s period over **one unimodular symbol** — a genuine irreducible analytic
atom (needs `f` as analytic input).  Everything else (integration, `{4,6}`
generators, slash action / `1−X²`, Manin contour) is ∅-axiom.

### 2. The atlas's remaining unit-wires + regime synthesis
The `c`-axis and face-axis unit-wires; and the deep **finite(`d=5`)↔infinite(νF)**
regime synthesis — is the analytic `?` the νF-completion of the finite cup-ladder?

### 3. (carried) Markov uniqueness `H`, π non-holonomicity, spiral-axis, p-adic H, etc.
See `research-notes/frontiers/INDEX.md`.

## Unresolved from This Session
- The full `SL(2,ℤ)` cocycle composition law on **non-tree** generators (the tree /
  L-R sub-semigroup version is done).
- The general-weight slash action (weight-4 instance `1−X²` done).
- Purity lesson recorded: `ring_intZ` cannot reduce `x + -x` to the `C 0` normal
  form — use `Meta.Int213` `add_neg_cancel`/`mul_neg`/`sub_zero` for cancel-to-zero goals.

## Next
Either (a) probe whether the single analytic atom (one unimodular symbol's `f`-period)
is the residue in some unmet frame, or (b) wire the `c`-axis / face-axis units to
complete the atlas's 3-axis unit bundle (Open Problem 2).

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions / essays this session**: `the_breadth_signature`,
  `minkowski_as_modular_cocycle`, `reached_by_none` (foundations/analysis essays);
  ledger `research-notes/promotion_essay_log.md` rows 9–11.
- **Promotion candidates**: the `Real213/Minkowski*` period sub-tree is PURE-closed;
  its narrative already lives in `minkowski_as_modular_cocycle.md`.
- **Active scratchpad**: `research-notes/frontiers/` (residue_expression_atlas,
  odometer_unit_synthesis, markov_lagrange, pi_nonholonomicity, …).  Sink rule holds.

## File Map
```
lean/E213/Lib/Math/NumberSystems/Real213/MinkowskiCocycle.lean          ← NEW: ? as Markov-valued modular cocycle (6 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/MinkowskiGoldenExtremal.lean   ← NEW: φ = extremal weight-2 period instance (1 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/MinkowskiPeriodIntegral.lean   ← NEW: period via the ∅-axiom dyadic integral + modulus (5 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/MinkowskiHigherWeightPeriod.lean ← NEW: z²/z³ integrate exactly via FTC (1 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/MinkowskiPeriodRelations.lean  ← NEW: weight-2 period = S-eigenvalue; {4,6} torsion (1 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/MinkowskiPeriodPolynomial.lean ← NEW: slash action on V_2; weight-4 period = 1−X² (12 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/MinkowskiModularSymbol.lean    ← NEW: Manin unimodular decomposition of the contour (5 PURE)
lean/E213/Lib/Physics/AlphaEM/CupLadderResidueUnit.lean                 ← NEW: cohomology graduation = residue unit; finite↔infinite (3 PURE)
lean/E213/Lib/Physics/Simplex/FaceTerms.lean                            ← +simplex_face_euler_zero (face axis closes)
lean/E213/Lib/Math/NumberSystems/Real213.lean, Lib/Physics/AlphaEM.lean ← umbrellas: +the new modules
theory/essays/analysis/minkowski_as_modular_cocycle.md                  ← NEW essay (the ? cocycle)
theory/essays/foundations/{reached_by_none,the_breadth_signature}.md    ← NEW essays
research-notes/frontiers/residue_expression_atlas.md                    ← NEW frontier (the atlas; open board)
```
