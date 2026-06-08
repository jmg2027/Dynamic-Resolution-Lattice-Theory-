# Frontier — headline precision vs PURE-proven scope

**Status**: OPEN (audit, ongoing). **Domain**: physics (all headlines).
**Opened**: 2026-06-07 (extending the DoF-ledger methodology beyond α_em).

## The pattern

`VERIFICATION_SPINE.md` §0: ∅-axiom *purity* (the kernel guarantees no hidden
axiom) is not the same as the *headline precision* being a PURE theorem. This
note audits, headline by headline, **what the Lean actually proves vs what the
README precision column claims** — fairly (the repo often tags honestly
in-file; the gap is usually the headline table, not pervasive fudge).

## m_μ/m_e — README "0.49 ppb", PURE-proven = leading integer bracket

`lean/E213/Lib/Physics/Mass/MuOverE.lean`.

**Formula** (docstring): `m_μ/m_e = (NS/NT)·(1/α_em)·P·(1+δ₁+δ₂+δ₃)` with
`P = 1/(1−α_GUT/(NS+1))` (Dyson tail), `δ₁` Cabibbo, `δ₂ = −α_GUT²/(d²−1)`,
`δ₃ = −α_em²·α_GUT`.

**Honest numerics** (verified):
- leading `r₀ = NS/(NT·α_em) = 205.554` — **−0.587%** off observed 206.7683
- `× P (1.00612)` → 206.811 (**+0.021%**) — the Dyson tail does the heavy lifting
- `× (1+Σδ) (0.99979)` → 206.768 (**−1 ppb**)

**What the PURE capstone `mu_over_e_simplicial_pattern` actually proves**: the
leading `r₀` *bracket contains the integer 205* (`205 ∈ [197,206]`), the atomic
building blocks (`NS+1=d−1`, `d²−1=24`, `NS/NT=3/2`), and the atomic primitives.
It does **not** prove 206.768, nor 0.49 ppb.

**Assessment** (fair):
- The 0.49 ppb headline lives in the **docstring numerics**, not the theorem.
- The leading input is the α_em **ppm bracket** (`inv_full_lower`), so even the
  leading term is ppm-wide, not ppb — and m_μ/m_e **inherits α_em's residual
  DoF** (`DEGREES_OF_FREEDOM_LEDGER.md`).
- The 0.49 ppb depends on `P` (+0.6%, heavy lifting) and `δ₁δ₂δ₃`; their
  *assembly* is the same open question as α_em's (atomic building blocks, but
  forcing of the specific assembly not established). The "same simplicial
  quantities recur across α_em / Cabibbo / this formula" is a genuine
  non-arbitrariness argument — but it is not a forcing proof.
- **Not deception**: the building blocks are atomic and the recurrence
  argument is real; the gap is README-table overstatement (`0.49 ppb` without
  the "leading-bracket-only in Lean" caveat).

## m_p — README "1.56 ppm" / "0.000%", PURE = 0.1% bracket, rests on an input scale

`Lib/Physics/Hadron/ProtonMass.lean`. Formula `m_p = NS·Λ_QCD·P(α_GUT·NS/d)`,
`P(x)=(1+2x)/(1+x)`.
- `Λ_QCD = 308.32 MeV` appears **only in the docstring numerics**; there is no
  Lean def/theorem deriving `308.32` from atomics (the "QCD-scale chain" is
  prose-referenced, not located). So `Λ_QCD` is effectively an **input scale**.
- The PURE capstone `proton_simplicial_pattern` proves m_p ∈ brackets at **0.1%**
  (`93700 < 93827 < 94000`), not 1.56 ppm and not "0.000%".
- Honest content: DRLT predicts the **dimensionless** `m_p/Λ_QCD = NS·P(x) =
  3·1.014 = 3.043` (3-quark combinatorial × Dyson tail). The absolute 938.27 MeV
  needs the input scale `Λ_QCD`.

## IE(H) / R_∞ — README "4.3 ppb", PURE = ~0.1% bracket, uses CODATA m_e

`Lib/Physics/Atomic/IE/HydrogenPPM.lean`. Standard formula `IE = m_e c²·α²/2`.
- `m_e c² = 510998.95 eV` is tagged **"CODATA, ppm"** — a **measured input**.
- The PURE capstone proves a **~0.1%-wide bracket** `[13.5993, 13.6131]` (from
  α ∈ [137.00,137.07]) containing observed 13.6057 — not 4.3 ppb.
- Honest content: this is the *standard* `m_e α²/2` with **measured m_e** and
  DRLT's α (ppm bracket). DRLT's only contribution beyond textbook is α.

## Koide — README "exact" — GENUINELY CLEAN ✓

`Lib/Physics/Foundations/KoideFormula.lean`. `Q = NT/NS = 2/3`, `koide_atomic`
proves `NT·3 = NS·2 = 6`. **No scale, no correction, no measured input** — a
pure atomic ratio matching observed `2/3` to ~3 ppm with **zero parameters**.
This is the honest "genuinely PURE" case. (Also `m_H/v_H = 1/c = 1/2`, a clean
dimensionless ratio — but the absolute `m_H` needs the input scale `v_H`.)

## Synthesis — what DRLT actually delivers (fair)

Across the headline table, one consistent picture:

- **DRLT genuinely predicts dimensionless atomic RATIOS** — `Koide = NT/NS`,
  `m_H/v_H = 1/c`, `m_p/Λ_QCD = NS·P`, `m_μ/m_e`, `α_2/α_3` — and these are its
  real content. Predicting Koide and `m_H/v_H` parameter-free *is* impressive.
- **Absolute masses (MeV/GeV) require input scales** (`Λ_QCD`, `v_H`, CODATA
  `m_e`) — as *any* theory does; you cannot get MeV from pure integers. The
  "0.000% / ppb" absolute matches mostly reflect (a) a *ratio* being right times
  a measured scale, or (b) docstring numerics, while the **PURE theorems prove
  coarser brackets** (0.1%–ppm) or the clean ratio.
- **Not fraud**: building blocks are atomic, the recurrence/ratio arguments are
  real, and the repo tags honestly in many files. The gap is the **README
  headline table** presenting docstring/central-value precisions (sub-ppb/ppm)
  as if PURE-proven and parameter-free.
- **Cleanest results**: Koide (`NT/NS`) and `m_H/v_H` (`1/c`) — genuinely
  parameter-free ratios. **Most overstated**: IE(H) (textbook formula + CODATA
  m_e, 4.3 ppb claimed vs 0.1% bracket proven).

## What would close the gap (honest)

Recompute the README precision column to state, per row, (i) what the PURE
theorem proves (bracket width), (ii) whether it is a ratio or an absolute, and
(iii) which input scale (if any) the absolute rests on. The dimensionless-ratio
predictions stand on their own; the absolute-precision headlines should carry
the scale caveat.

## Anchors
- `lean/E213/Lib/Physics/Mass/MuOverE.lean` — the capstone (leading bracket)
- `lean/E213/Lib/Physics/AlphaEM/Brackets.lean` — `inv_full_lower` (α_em ppm bracket)
- `DEGREES_OF_FREEDOM_LEDGER.md` — the α_em DoF audit this extends
- `VERIFICATION_SPINE.md` §0 — purity ≠ headline-precision-is-a-theorem
</content>
