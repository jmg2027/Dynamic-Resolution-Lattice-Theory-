# Falsifiability — 213 discard conditions

(Distilled from AXIOM.md §5.2.1)

## Basic principle

  All results of 213 must be derivable from Lean 4 core + the Raw axiom alone.

## Discard condition

  If *any result is shown to be absolutely impossible without adding an axiom*,
  **the entirety of 213 theory is discarded**.  Not just the result alone.

This is a direct consequence of the §1 declaration that the Raw axiom is
the *minimum residue*: if adding an axiom is genuinely necessary, Raw was
not the minimum.

## Operational principles

- Adding external axioms (Classical, LEM, native_decide, etc.) is entirely
  forbidden.
- Results that are blocked are left as "open," with distinction between
  *permanent wall vs. temporary obstacle*.  A permanent wall triggers a
  theory failure declaration.
- Lean verification = the mechanical auditor of falsifiability.

Mingu's confirmed declaration (2026-04-24).  *Never relaxed*.

## Measurement falsifiers (CLAUDE.md verification criterion 2)

213 must simultaneously provide *formalized new physics that no one can
contest*.

Each *measurable* integer is *atomic-forced*:

| Measurement | Timing | DRLT prediction | If violated |
|---|---|---|---|
| Neutrino ordering | JUNO ~2030 | normal | discard |
| θ_QCD | nEDM ~2027-30 | [2.5,3.0]×10⁻¹¹ | discard |
| 4th gen particles | LHC ongoing | absent | discard |
| PMNS angles | DUNE/HK ~2030 | leading denom {NS,NT,d²-1} | discard |
| Cabibbo λ | LHCb/Belle II | 5/22 ± 1% | discard |
| m_p | Lattice QCD next | 938.27 atomic | discard |
| Magic numbers | verified | {2,8,20,...} | (already verified) |

## Formal guarantees

  Phase 3 Falsifier:
    `phase3_falsifiers : 19-conjunct, 0 axioms`

  Phase 1 precision quantities:
    1/α_em = 137.036 ppm
    m_μ/m_e = 0.48 ppb
    m_p exact (lattice precision)
    Ω_Λ = 0.0008%

## One-line summary

> "Any single measurement deviating from the DRLT forced integer → repo deleted"

This is the *true stake* of 213.
Formal theorem + falsifiable + 0 axioms = a genuinely falsifiable theory.
