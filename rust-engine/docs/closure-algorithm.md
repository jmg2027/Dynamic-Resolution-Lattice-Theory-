# DRLT Observable Closure Algorithm

A meta-pattern emerging from the 2026-05-01 closure session (9 simultaneous
ppm-level closures across hadron, lepton, and EW mixing sectors).

## The Conjecture

> **DRLT Closure Form.** Every observable O that lives on the K_{3,2}^{(c=2)}
> cohomology has a closed form
>
>     O  =  R(NS, NT, d, c)  ·  Π_i (1 + κ_i · α_i^{n_i})
>
> where:
>   - **R** is a small rational in (NS, NT, d, c) with denominator ≤ 100
>   - **α_i** ∈ {α_GUT, α_em} (DRLT primitive couplings)
>   - **n_i** ∈ {1, 2, 3} (cup-chain depth ≤ 3 for composite particles)
>   - **κ_i** is a small atomic count: integer power or linear combination
>     of (NS, NT, d, c) under bound ≤ 1500

## Atomic Count Generators

The integer coefficients κ_i in our 9 closures all derive from a small
generator set under bounded operations:

```
generators       = {NS, NT, d, c}                   = {3, 2, 5, 2}
power-2 set      = {NS², NT², d², c²}               = {9, 4, 25, 4}
power-3 set      = {NS³, NT³, d³}                   = {27, 8, 125}
power-4 set      = {NS⁴, NT⁴, (NS·NT)⁴}             = {81, 16, 1296}
products         = {NS·NT, NS·d, NT·d, NS·NT·d}     = {6, 15, 10, 30}
combinations     = {NS²−1, d²−NS, d²−d+c, NT²·(NS²−1)}
                                                     = {8, 22, 22, 32}
combined-products= {NS²·d, NT·NS²·d, NS²·NT, NS·d²·NT}
                                                     = {45, 90, 18, 150}
```

Empirical claim: every κ_i in our 9 closures appears in this list.
Coefficient reuse (same κ across multiple observables) is the strongest
positive evidence that the closure form is structural, not coincidental.

## The Algorithm

Pseudocode for closing a stuck observable O at target value τ:

```python
def close(O, τ, σ_exp):
    # Phase 0: experimental sufficiency check
    existing = lookup_existing_form(O)
    if abs(existing - τ) / τ < σ_exp:
        return existing, "sufficient"

    # Phase 1 (L5): compositional closure — ALWAYS try first
    for (A, B) such that O ≈ A · B or O ≈ A / B:
        if A.closed and B.closed:
            return A.atomic × B.atomic, f"L5 cascade: {A} · {B}"

    # Phase 2 (L2): strip transcendentals, search rational bases
    bases = [n/m for n, m in atomic_pairs] union {targets within ±50% of τ}
    bases = sort(bases, by=closeness_to_τ)

    # Phase 3 (L3): nested cup-chain depths 1, 2, 3
    for depth in [1, 2, 3]:
        for base in bases:
            for κ_combo in cartesian_product(atomic_counts, depth):
                form = base · Π (1 ± κ_i · α_i^{n_i})
                if abs(form - τ) / τ < σ_exp:
                    # Phase 4 (L4): structural verification
                    if all(κ in anchor_catalog for κ in κ_combo):
                        return form, "L3+L4 structural ★"
                    elif all(triple_atomic(κ) for κ in κ_combo):
                        return form, "L3 multi-atomic"
                    else:
                        return form, "L3 numerical"

    # Phase 5: failure — observable is not on K_{3,2}^{(c=2)} cohomology
    # OR requires deeper class (E modulus shadow, F multi-simplex)
    return None, "stuck — promote to Class E/F or accept gap"
```

## Empirical Evidence (9 closures @ 2026-05-01)

| observable        | R(NS,NT,d,c)        | corrections                          | depth | category |
|-------------------|---------------------|--------------------------------------|-------|----------|
| m_n/m_p − 1       | NS²/(NT²(NS²−1))=9/32| α_em·(1 − NS²·d·α_em)               | 2     | L3       |
| m_p/m_e           | NS·NT·π⁵            | (1 + α_GUT/(NS·NT)⁴)                | 1     | L1+L4    |
| m_n/m_e           | (m_n/m_p)·(m_p/m_e) | inherited                            | —     | L5       |
| (m_n−m_p)/m_e     | (m_p/m_e)·δ(m_n/m_p)| inherited                            | —     | L5       |
| g_p               | (d²−NS)/NT² = 22/4  | (1+NS·NT·α_GUT)(1−NS·d·α_em)·(1−NS²NT·d·α_em²) | 3 | L3 |
| m_τ/m_e           | (m_τ/m_μ)·(m_μ/m_e) | inherited                            | —     | L5       |
| sin²θ₁₃           | α_GUT (single primitive) | (1−NT²·α_GUT)(1+NS·NT·α_GUT²)   | 2     | L3       |
| sin²θ_W           | 30/(60·ζ(2)+30)     | (1 − α_GUT/NS)                      | 1     | L1+L4    |
| r_p · m_p / ℏc    | NT² = 4             | (1 + α_GUT/d³)                      | 1     | L4       |

## Sub-patterns within the algorithm

**A. Anchor-catalog priority (L4 refinement).**  Bias the κ_i search
toward integers already established elsewhere.  If an observable's
fitted κ matches an existing K_25 anchor (4, 6, 8, 15, 22, 32, 45,
90, 125, 1296), promote it from "numerical" to "structural".

**B. Cup-chain sign rule.**  In the closures with multiple α factors,
the signs alternate or match the physical leakage direction:
  - g_p:  (1+α_GUT)·(1−α_em)·(1−α_em²)  — α_GUT additive, α_em subtractive
  - sin²θ₁₃: (1−α_GUT)·(1+α_GUT²)  — α_GUT subtractive, α² additive
  - m_n/m_p: α_em·(1 − α_em)  — α_em with negative tail

This sign pattern likely reflects the cup-product coboundary
direction at the relevant simplex.

**C. Composition cascade (L5) is automatic.**  Once two atomic forms
exist, every dimensionless ratio of their products / quotients
inherits the precision floor.  Example cascade:

```
              m_p atomic
              ↓
   m_p/m_e = m_p · (1/m_e)              [Class C atomic]
   m_n/m_p = 1 + (9/32)·α_em(1−45α_em)  [Class F]
   ↓
   m_n/m_e = m_n/m_p · m_p/m_e          [free, sub-ppm]
   m_n     = m_p · m_n/m_p              [free, sub-ppb]
   (m_n−m_p)/m_e = m_p/m_e · (m_n/m_p − 1)  [free, ppm]
```

The cascade fans out — one Class F closure (m_n/m_p) plus one
Class C atomic (m_p/m_e v2) yields five free closures.

**D. Class assignment by structure.**

| class | structure                       | depth | example      |
|-------|---------------------------------|-------|--------------|
| A     | single propagator P(x)          | 0     | α_em Dyson   |
| B     | (1+α·k) leak                    | 1     | sin²θ_W tail |
| C     | full polynomial in (NS,NT,d)    | 0     | 1/α_em       |
| D     | nested (1+α₁)(1+α₂)(1+α₃)       | 2-3   | g_p, sin²θ₁₃ |
| E     | modulus shadow |G|²/d           | —     | gravity      |
| F     | multi-simplex glued composite   | 2+    | m_n/m_p      |

The depth heuristic: composite-particle (≥ 2 simplices) ⇒ Class D
or F triple cup; single-particle ⇒ Class A/B; full lattice
invariant ⇒ Class C.

## Connections to Lessons L1–L5

| lesson | role in algorithm                                        |
|--------|----------------------------------------------------------|
| L1     | rational-complex principle: π / ζ(2) bracketed shadows   |
| L2     | strip transcendentals → pure-rational base preference    |
| L3     | composite targets need depth ≥ 2 cup-chain               |
| L4     | bias search toward anchor-catalog κ_i (structural ★)     |
| L5     | check compositional closure first (free precision)       |

## Open question

Is the closure form **complete**?  i.e., is there an observable on
K_{3,2}^{(c=2)} that does NOT fit `R · Π(1+κα^n)`?

Current empirical answer: **no failures yet** at depth ≤ 3.  All 9
session closures fit.  Failure modes that *would* break the conjecture:
  - Λ_QCD-anchored observables (m_π, deuteron) need a separate scale,
    not just a coupling correction
  - Observables involving running between scales (1/α_em IR vs UV)
    may need additional bracket structure

Sufficient evidence for the conjecture: a 10th–20th observable closing
to the same form, with κ_i drawn from the anchor catalog.

— added 2026-05-01
