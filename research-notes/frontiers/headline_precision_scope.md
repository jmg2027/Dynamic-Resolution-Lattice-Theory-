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

## What would close it

A PURE theorem carrying the *full* `m_μ/m_e` formula (P + δ's) to ppb — i.e.
the structural-α_em value (not the ppm bracket) times forced corrections —
with `#print axioms` empty, matching 206.768 at the headline precision. Then
the README "0.49 ppb" is backed by Lean, not docstring.

## Next headlines to audit (same lens)
- `m_p = 938.27 MeV` (README 1.56 ppm) — `Lib/Physics/Hadron/ProtonMass`
- `R_∞ = 13.605693 eV` (README 4.3 ppb) — `Lib/Physics/Atomic`
- Koide `Q = 2/3` (exact) — likely genuinely PURE (pure atomic ratio)

## Anchors
- `lean/E213/Lib/Physics/Mass/MuOverE.lean` — the capstone (leading bracket)
- `lean/E213/Lib/Physics/AlphaEM/Brackets.lean` — `inv_full_lower` (α_em ppm bracket)
- `DEGREES_OF_FREEDOM_LEDGER.md` — the α_em DoF audit this extends
- `VERIFICATION_SPINE.md` §0 — purity ≠ headline-precision-is-a-theorem
</content>
