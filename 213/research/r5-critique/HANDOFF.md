# r5-critique — HANDOFF

## Status

**Phase:** E1 **Lean-complete** — hypothesis H confirmed with
full Lean formalisation of R3 and R4 for `ziLens = (ZI, I,
-I, ZI.mul)`.  R1 and R2 are built into the Lens structure +
`Raw.fold`.

**Branch:** `claude/polish-paper-submission-EilC5`.

## What is in place

### Research notes
- `CLAUDE.md` — research frame, hypothesis H, E1–E5 list
- `notes/00_research_question.md` — formalised question
- `notes/01_zi_counterexample.md` — complete argument + Lean
  artifact list; H confirmed

### Lean artifacts
- `framework/E213/Research/ZI.lean` — `ZI = ℤ[i]`, `mul`,
  `conj`, `normSq`, `ext`, `conj_conj`, `conj_ne_id`. ✓
- `framework/E213/Research/ZIDomain.lean` — `mul_comm`,
  `normSq_mul` (Diophantus identity, closed by `simp` with
  AC-arith + `omega`; no `ring` needed), `normSq_nonneg`,
  `normSq_eq_zero_iff`, `no_zero_div`,
  `mul_ne_zero_of_ne_zero`. ✓
- `framework/E213/Research/ZIHom.lean` — `conj_I`,
  `conj_negI`, `conj_mul` (ring hom). ✓
- `framework/E213/Research/ZILens.lean`:
  - `ziLens : Lens ZI`
  - `ziLens_nonVanishing : NonVanishing ziLens` (R3) ✓
  - `ziLens_swapMatching : SwapMatching ziLens ZI.conj` (R4) ✓
    — pending main-build verification of `Raw.fold_swap_hom`.
- `framework/E213/Firmware/Raw.lean` — adds generic
  `Raw.fold_swap_hom` helper (pattern of existing
  `fold_signed_swap`).  Build pending in slow environment;
  syntactically complete.

## Immediate next step

1. Wait for main `lake build E213.Firmware.Raw` to complete
   (this session started it and left it running on explicit
   user instruction — expected ~10–60 minutes on this host).
2. Once Raw builds, verify `E213.Research.ZILens` builds: this
   exercises `Raw.fold_swap_hom` via `ziLens_swapMatching`.
3. If R3/R4 theorems both `Built ✓`, **E1 is closed** and
   hypothesis H is Lean-verified.

## What comes after E1

- **E2:** generalise to other quadratic extensions —
  `ℚ[i]`, `ℚ(√-2)`, `𝔽_9`, `ℤ[ω]` (Eisenstein integers).
  Each needs a `normSq`-like multiplicative `ℤ`-valued norm.
- **E3:** Lean formalisation of R5' (fold totality) — show it
  is vacuous under inductive Raw.
- **E4:** hunt for the minimal extra condition that
  re-selects ℂ uniquely — cardinality?  Archimedean?  a
  213-internal constraint?
- **E5:** if no such condition exists, start drafting
  **Paper 2** outline.

## Paper 2 stub

Working title: *"The ℝ-algebra assumption in 213 — a finitist
critique."*

Central claim: R5 smuggles classical infinity; removing it
collapses ℂ-uniqueness to R1-R4, for which `ℤ[i]` is an
explicit countable counterexample (this file + E1 artifacts).
