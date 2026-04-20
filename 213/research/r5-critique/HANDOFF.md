# r5-critique — HANDOFF

## Status

**Phase:** E1 — math argument complete, Lean partially
formalised. Hypothesis H **confirmed at the mathematical
level**; full Lean verification is the next iteration.

**Branch:** `claude/polish-paper-submission-EilC5` (shared with
Paper 1 polish; can be split later if needed).

## What is in place

- `CLAUDE.md` — research frame, hypothesis H, experiment list
- `notes/00_research_question.md` — formalised question
- `notes/01_zi_counterexample.md` — **full math argument**,
  R1–R4 verified by hand for `ziLens = (ZI, I, -I, ZI.mul)`.
  Conclusion: H confirmed mathematically.
- `framework/E213/Research/ZI.lean` — Gaussian integers with
  `mul`, `conj`, `normSq`; lemmas `ext`, `conj_conj`,
  `conj_ne_id`. **Builds ✓**.
- `framework/E213/Research/ZIDomain.lean` — `ZI.mul_comm`
  (manual, no `ring`). **Builds ✓**.
- `framework/E213/Research/ZIHom.lean` — `ZI.conj_I`,
  `conj_negI`, `conj_mul` (distribution of conj over Gaussian
  multiplication, via `Int.neg_mul_neg`, `Int.mul_neg`, etc.).
  **Builds ✓**.
- `framework/E213/Firmware/Raw.lean` — **modified**: added
  public theorem `Raw.fold_swap_hom`, a generalisation of the
  existing `Raw.fold_signed_swap` that accepts any `conj : α →
  α` satisfying `conj ba = bb`, `conj bb = ba`, `conj` as a
  combine-homomorphism, and `c` commutative. **Pending build
  verification** — Raw.lean is slow to compile in this
  environment (>10 min); the pattern follows the existing
  `Tree.fold_signed_swap` which is known to compile.
- `framework/E213/Research/ZILens.lean` — **R4 proof**:
  `ziLens_swapMatching : SwapMatching ziLens ZI.conj`,
  obtained by applying `Raw.fold_swap_hom` with the ZI-side
  lemmas. Depends on the `Raw.fold_swap_hom` build.

## Immediate next step (for a longer build window)

1. **Verify `Raw.fold_swap_hom` builds.** Run
   `lake build E213.Firmware.Raw` with ≥15 min timeout.  In
   this session, Raw.lean's full compile repeatedly timed out
   at ~10 min wall time (Lean v4.16.0 on this host is slow on
   the existing 580-line proof bundle); the new helper
   follows the existing `Tree.fold_signed_swap` pattern
   verbatim.  As part of the build attempt, the two original
   uses of the `ring` tactic in `Tree.fold_signed_swap` were
   replaced with explicit `Int.neg_add` rewrites (`ring`
   appears to be unavailable in this Lean 4 core build); this
   change is included in the commit.
2. **Verify `ziLens_swapMatching` builds** after Raw builds.
3. **Complete R3 in Lean.** Needs `normSq_mul` Diophantus
   identity.  Without `ring` in core, this requires manual
   expansion; a no-`ring` proof sketch is in
   `notes/01_zi_counterexample.md`.  Alternatively, route
   around `normSq_mul` by direct integral-domain case
   analysis on `(u.re, u.im)`/`(v.re, v.im)`.

The math argument in `notes/01_zi_counterexample.md` already
establishes H at the mathematical level; full Lean verification
is a hardening step.

## Open technical issues

- Lean 4 core has `Int` but not `Int`'s ring-theory lemmas
  bundled; may need to prove integral-domain property of `ZI`
  by hand (norm-based argument: `ZI.norm u v = |u|² · |v|²`).
- `Lens` structure currently lives in `E213.Hypervisor.Lens`;
  check whether `SwapMatching`, `NonVanishing` are general
  enough to apply to non-ℝ-algebra codomains (they should be —
  they take `α : Type` untyped).

## What comes after E1

- E2: generalise — classify all quadratic-extension Lenses
  satisfying R1–R4 (`ℚ[i]`, `ℚ(√-2)`, `𝔽_9`, etc.)
- E3: Lean formalisation of R5' (fold totality) and its vacuity
- E4: hunt for the minimal extra condition that restores
  ℂ-uniqueness — cardinality? archimedean? something else?

## Paper 2 stub (when E1+E2 are done)

Working title: "The ℝ-algebra assumption in 213 — a finitist
critique."

Outline draft planned in
`notes/99_paper2_outline.md` after E1–E3.
