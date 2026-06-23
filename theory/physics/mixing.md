# Flavor Mixing — CKM + PMNS + Cabibbo

**Status**: Closed.  The CP-phase / CKM specifics are canonical in
[`cp_phase.md`](cp_phase.md); this chapter is the broader mixing overview.

## Overview

Flavor mixing matrices: **CKM** (quark sector), **PMNS** (neutrino
sector), the Cabibbo angle, and CP violation.  The entries are Lens
readings of the atomic shape `(NS, NT, d) = (3, 2, 5)` — not a separate
flavour theory, one more `⟨C|L⟩ ⊕ Residue` reconstruction of the same
residue.  The golden ratio φ enters as the apex **modulus** (a real
eigenvalue), *not* as the CP phase.

## Narrative

The mixing observables read the atomic shape under three Lenses:

- **Cabibbo angle**: `λ = 5/22 = d / (d² − NS)` — the canonical
  213 value (catalog falsifier; `5/22 ± 1 %`).  The Wolfenstein
  `A` parameter is a *separate* quantity (`A = φ/c`); it is not the
  Cabibbo angle and should not be conflated with `λ`.
- **CP-violating phase**: `δ = 90°`, **forced** by the complex
  structure being the Cayley–Dickson imaginary unit `i`
  (`ℤ[i]^× = C₄`).  By Niven's theorem a discrete CP phase has
  rational cosine (only `0°, 60°, 90°`), so the earlier golden posit
  `δ = π/φ²` is **demoted as structurally impossible** — the golden
  ratio sits in the apex modulus `R_u = 1/φ²`, never the phase.  Full
  derivation: [`cp_phase.md`](cp_phase.md).
- **Neutrino mass ratios**: ratios of consecutive Fibonacci numbers —
  the same φ read in the (real) mixing angles.

φ appears as the universe-chain fixed point (per
`theory/math/foundations/universe_chain.md`) and the algebra-tower
asymptote (per `theory/math/algebra/cayley_dickson/algebra_tower.md`).
The same φ is read across all three — one Lens result of the matrix
fixed point (§3.5), not three coincidences.

## Connection

- [`cp_phase.md`](cp_phase.md) — **canonical** CKM CP-phase chapter
  (`δ = 90°` forced; apex modulus `1/φ²`; the `C₄`/`i` = signed Hodge
  `⋆` = `ℤ[i]` = `ℚ(ζ₅)` identity).
- `theory/math/foundations/universe_chain.md` — φ as Möbius fixed point
- `theory/math/algebra/cayley_dickson/algebra_tower.md` — φ asymptote rate
