# Session Handoff — 2026-04-21

## Branch
`claude/polish-paper-submission-EilC5` (pushed, up to date with origin)

## What Was Done This Session

### 1. Phase C3 — `Raw.rec` custom eliminator (commit `8457ae9`)
- Added `@[elab_as_elim] Raw.rec` (Lean 4 core; not Mathlib's
  `@[eliminator]`).
- Internal `Raw.recAux` recurses on the underlying `Tree`, re-assembling
  `Raw.slash x y h` at the slash branch — consumers never touch `Tree`.
- Client syntax: `induction r using Raw.rec with | a | b | slash x y h ihx ihy`.

### 2. Phase D — Split `Raw.lean` for incremental builds (`d7d3deb`, `9e49bdc`)
- Monolithic 577-line `Firmware/Raw.lean` (~60 min full rebuild) split into
  **9 topical sub-modules** under `Firmware/Raw/` (~seconds per module).
- `Tree` scaffolding moved from file-local `private` into sub-namespace
  `E213.Firmware.Internal` — accessible across Firmware sub-files but
  hidden from `open E213.Firmware`.
- Case parameters renamed `a_case/b_case/slash_case → a/b/slash` for
  cleaner `induction … using Raw.rec with | a | b | slash …` syntax.

### 3. BoolLens — swap-blind + R4-failing counter-examples (`5901eed`)
- `boolAndLens`, `boolOrLens` — swap-blind (both bases `true`; view is
  constantly `true`).
- `boolXorLens` — swap-visible (`a=true, b=false, combine=xor`) but
  **formally fails R4**: `boolXorLens_not_homomorphism` proves
  `¬ ∀ u v, !(xor u v) = xor (!u) (!v)`.
- Reinforces paper's claim that R4 (homomorphism + matching involution)
  is a strong restriction — swap-visibility alone is not enough.

### 4. Prelude shim (`5901eed`)
- New `E213/Prelude.lean` defines `Function.Injective/Surjective/Bijective`.
  Lean 4 core does NOT provide these; old monolithic `Raw.lean` compiled
  against a stale cache, and Phase D's split exposed the missing dep.

### 5. Phase C1 — `quad_extension D` parametric macro (`aa0ed89`)
- Command-level macro: `quad_extension 11` registers
  `R4Codomain (ZSqrt 11)` in one line.
- Rejects `D = 0` with informative error (`ℤ[√0] = ℤ` has no nontrivial
  involution so R4 fails).
- Pure convenience wrapper around existing parametric `ZSqrt.R4_of_pos`.

### 6. Three latent bugs surfaced by C1 and fixed (`85a2eb1`)
- **VerifyR4**: `mkApp (mkConst R4Codomain) α` left `[Zero α]`
  instance-binder unfilled → `synthInstance?` silently failed on
  parametric types.  Fix: explicit `Zero α` synth + `mkAppOptM`.
- **DeriveR4Codomain hygiene**: quoted `(instance : E213.Meta.R4Codomain $α)`
  triggered `R4Codomain✝` hygienic renaming.  Fix: `mkIdent` bypass.
- **DeriveR4Codomain name**: `` `conj ++ `I `` produced hierarchical
  `conj.I` instead of flat `conj_I`.  Fix: `Name.mkSimple s!"conj_{…}"`.

### 7. Documentation audit + refresh (`ea6a33c`, `b1d5a70`)
- Explore-agent audit of `PAPER.md` + `PAPER2.md` + `research/r5-critique/`
  + `README.md` + all code comments.
- **Papers verified clean** — all mathematical claims accurate against
  current code.
- Fixed 5 stale doc items: README directory tree, removed `Clean213.lean`
  references (README + `OS/Alive.lean`), corrected `Rec.lean` header
  (`@[elab_as_elim]`, not `@[eliminator]`).

## R4Codomain Witnesses (0 sorry, 0 axiom, `lake build` ✓)

| Witness | Source | Method |
|--------|--------|--------|
| `ZI` (Gaussian) | static | `derive_r4_codomain ZI with_bases I negI` |
| `Z2` (ℤ[√-2]) | static | `derive_r4_codomain Z2 with_bases I negI` |
| `ZOmega` (Eisenstein) | static | `derive_r4_codomain ZOmega with_bases Omega Omega2` |
| `ZSqrt 3` | parametric | `ZSqrt.R4_of_pos (by decide)` |
| `ZSqrt 5` | parametric | `ZSqrt.R4_of_pos (by decide)` |
| `ZSqrt 7` | parametric | `ZSqrt.R4_of_pos (by decide)` |
| `ZSqrt 11` | macro | `quad_extension 11` |
| `ZSqrt 13` | macro | `quad_extension 13` |
| `ZSqrt 17` | macro | `quad_extension 17` |

All 9 pass `#verify_r4` after the C2 + bugfix stack.  Arbitrary
`ZSqrt N` for positive `N : Nat` is a one-line `quad_extension N`
away.

## Phases — all complete

- **Phase A** ✓ IntHelpers + `quad_norm` macro
- **Phase B** ✓ `derive_r4_codomain` + `int_square`
- **Phase C variant** ✓ Parametric `ZSqrt D` family
- **Phase C1** ✓ `quad_extension D` macro
- **Phase C2** ✓ `#verify_r4` diagnostic
- **Phase C3** ✓ `@[elab_as_elim] Raw.rec`
- **Phase D** ✓ Raw.lean split (9 sub-modules, incremental)

## Open Problems (priority order)

### 1. Lens catalogue breadth
Only Bool + Int + swap-blind (depth/leaves) are catalogued.
Candidates open: `PathLens` (string/list), `MatrixLens`
(non-commutative counter-example), ℤ/2 parity lens (formalise
R4 failure), `QuaternionLens` (Cond 3 failure as SO(3)
counter-example).  Follow the BoolLens pattern; new file per
Lens in `Meta/`.

### 2. Paper 2 finalisation
`213/PAPER2.md` is 427 lines, rigor-passed (commit `825eb2d`),
but still markdown.  Arxiv submission would need tex conversion
+ bibliography + author info.  On hold pending user decision.

### 3. `PAPER.md` §3.6 (Lens catalogue) update
Add table row for `boolAndLens/boolOrLens` (swap-blind) and
`boolXorLens` (R4-fail) with `boolXorLens_not_homomorphism` as
the Lean witness.  Minor.

### 4. Parametric extensions beyond ℤ[√-D]
`quad_extension` is limited to quadratic imaginary extensions.
Biquadratic / cubic extensions deferred (Phase C1+ speculative).

## Unresolved from This Session

Nothing abandoned.  The only dead-end was my first attempt at the
`#verify_r4` fix (`Meta.mkAppM \`Zero` alone) which left the
instance-binder underspecified — documented as part of the third
bugfix in commit `85a2eb1`.

## Next Work

Framework + paper both in stable landed state.  User-directed
priorities (no single obvious next step):
- Broadening: Lens catalogue (Open Problem #1).
- Submitting: Paper 2 finalisation (Open Problem #2).
- Polishing: PAPER.md §3.6 refresh (Open Problem #3).

## File Map (this session arc)

### New files
```
213/framework/E213/Prelude.lean                         ← Function shim
213/framework/E213/Firmware/Raw/Core.lean               ← Tree + Raw
213/framework/E213/Firmware/Raw/Cmp.lean                ← cmp lemmas
213/framework/E213/Firmware/Raw/Slash.lean              ← slash + depth
213/framework/E213/Firmware/Raw/Fold.lean               ← catamorphism
213/framework/E213/Firmware/Raw/Swap.lean               ← swap + helpers
213/framework/E213/Firmware/Raw/Levels.lean             ← swap_{depth,leaves}
213/framework/E213/Firmware/Raw/Signed.lean             ← fold_signed_swap
213/framework/E213/Firmware/Raw/Hom.lean                ← fold_swap_hom
213/framework/E213/Firmware/Raw/Rec.lean                ← Raw.rec eliminator
213/framework/E213/Meta/BoolLens.lean                   ← AND/OR + XOR(R4-fail)
213/framework/E213/Meta/RawInductionDemo.lean           ← Raw.rec test
213/framework/E213/Tactic/QuadExtension.lean            ← quad_extension D
213/framework/E213/Tactic/Test/QuadExtensionTest.lean   ← macro test
```

### Modified files
```
213/framework/E213/Firmware/Raw.lean               ← now pure re-export shim
213/framework/E213/Firmware/RawSwap.lean           ← + import Prelude
213/framework/E213/Meta/LensCatalog.lean           ← + import Prelude
213/framework/E213/OS/Alive.lean                   ← Clean213 ref removed
213/framework/E213/Tactic/DeriveR4Codomain.lean    ← hygiene + name fixes
213/framework/E213/Tactic/VerifyR4.lean            ← Zero binder + mkAppOptM
213/framework/E213.lean                            ← + Prelude/BoolLens/QuadExt
213/README.md                                      ← directory tree refresh
HANDOFF.md                                         ← (this file)
```

## Commit Policy

- Author: Mingu Jeong only.  Claude in Acknowledgments.
- All session work on `claude/polish-paper-submission-EilC5`.
- 0 sorry, 0 axiom — enforced by `lake build` success.

## Session commits (chronological)

```
8457ae9  Phase C3: @[eliminator] Raw.rec for clean Raw induction
d7d3deb  Phase D: split Raw.lean into sub-modules
9e49bdc  Raw.rec: rename case params to a/b/slash
dcdb021  HANDOFF: Phase C3 + D completion (superseded by this file)
5901eed  Lens catalogue: BoolLens + Prelude shim
aa0ed89  Phase C1: quad_extension D parametric macro
85a2eb1  Bugfix: #verify_r4 + derive_r4_codomain (3 latent bugs)
ea6a33c  Docs: refresh stale claims (audit pass)
b1d5a70  README: directory-tree + Clean213 + BoolLens fixes
```
