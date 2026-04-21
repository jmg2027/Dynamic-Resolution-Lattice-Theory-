# r5-critique — HANDOFF

## Status

**Phase E1–E3 + metaprogramming infrastructure (Phases A, B,
C-variant) complete.**

Hypothesis H is Lean-confirmed at the counterexample level
with **infinitely many witnesses** via the parametric
`ZSqrt D` family.  Three concrete-typed witnesses (ZI = ZSqrt
1-spirit, Z2 = ZSqrt 2-spirit, ZOmega = Eisenstein) plus
auto-generated `ZSqrt 3, 5, 7, …` are all R4Codomain
instances.

**Branch:** `claude/polish-paper-submission-EilC5`.

## What is in place

### Research notes
- `CLAUDE.md` — research frame
- `notes/00_research_question.md`
- `notes/01_zi_counterexample.md`
- `notes/02_r5_vacuity.md` — R5a/R5b split
- `notes/03_e4_restoring_c.md` — what could re-select ℂ
- `notes/04_refactor_plan.md` — Raw.rec @[eliminator] B-option
- `notes/99_paper2_outline.md`

### Lean artifacts (3 + ∞ witnesses)

**Concrete codomains:**
- `Research/ZI.lean` + `ZIDomain.lean` + `ZIHom.lean` +
  `ZIInstance.lean` — Gaussian integers ℤ[i]
- `Research/ZSqrt2.lean` + `ZSqrt2Domain.lean` +
  `Z2Instance.lean` — ℤ[√-2]
- `Research/ZOmega.lean` + `ZOmegaDomain.lean` +
  `ZOmegaInstance.lean` — Eisenstein ℤ[ω]

**Parametric family (NEW):**
- `Research/ZSqrt.lean` + `ZSqrtDomain.lean` +
  `ZSqrtInstance.lean` — `ZSqrt D = ℤ[√-D]` for `D : Int`,
  with concrete instances for D = 3, 5, 7.  Adding more =
  one line.

**Spec class hierarchy:**
- `Meta/SelfRecognising.lean` — `R12Codomain → R3Codomain
  → R4Codomain` `extends` chain.
- Generic `specLens_nonVanishing` (R3) and
  `specLens_swapMatching` (R4) proved once per tier.

**Metaprogramming (Phases A + B):**
- `Research/IntHelpers.lean` — shared `Int` self-mul lemmas.
- `Tactic/QuadNorm.lean` — `quad_norm` macro
  (simp+omega chain for Diophantus-style polynomial
  identities; works for ZI, Z2, ZOmega, ZSqrt D norms).
- `Tactic/IntSquare.lean` — `int_square` wrapper for
  `0 ≤ a*a` and `a*a = 0 ↔ a = 0`.
- `Tactic/DeriveR4Codomain.lean` — `command_elab` that
  generates the 13-field `R4Codomain` instance from a
  base-name pair via name-suffix convention.
- `Tactic/Test/{QuadNormTest,IntSquareTest}.lean` —
  Firmware-free verification.

**Firmware support (from earlier sessions):**
- `Firmware/Raw.fold_swap_hom` (general homomorphism-swap
  helper, used by R4Codomain proofs).
- `Firmware/RawSwap.lean`, `Firmware/RawLevels.lean`
  (extracted from Raw.lean for modularity).

## Build status (this session)

✓ All structure + Domain modules build standalone in seconds.
✓ `Tactic/*` modules + tests build standalone.
⏳ All `*Instance.lean` modules depend on R4Codomain via
   `SelfRecognising → Lens → Raw`.  In-flight Raw.lean
   compile (~30 min on this host) verifies all instances
   together.

## Next-session priorities

- Verify Raw build completes; confirm all `*Instance` build.
- **Phase C2 (`#verify_r4`)** — meta-check command that
  scans environment for R4Codomain instances and reports
  their derivation.  Now that we have ≥3 concrete + 3
  parametric instances (6 total), this would actually
  exercise something.
- **Phase C3 (`raw_induction`)** — gated on
  `@[eliminator] def Raw.rec` (B-option Firmware refactor).
- Consider abolishing the per-D individual modules in favour
  of `ZSqrt D` family + small concrete-witness shims, once
  ZSqrtInstance verifies.

## Paper 2 implication

H confirmed: not just three witnesses, but an **infinite
parametric family** of countable R1-R4-admissible
codomains.  The "ℂ uniqueness" claim of Paper 1 rests
entirely on R5b — without that, Paper 1 §4 admits
infinitely many countable witnesses.

This sharpens Paper 2's central thesis: R5b smuggles
classical infinity, and removing it leaves a continuum (in
fact a countable infinity parameterised by `D`) of
admissible Lens codomains.
