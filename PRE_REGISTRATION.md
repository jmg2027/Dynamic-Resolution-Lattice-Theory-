# Pre-Registration — DRLT's falsifiable forward predictions

> **The single move that converts the program from retrodiction to
> prediction.** A derivation that reproduces an *already-measured* number
> (1/α_em, m_μ/m_e, m_p, Koide, magic numbers) is always vulnerable to
> "you knew the answer." Scientific credibility comes from a claim that
> is **registered before the measurement** and **could come out the other
> way**. This file is that register.
>
> **Pre-registration act.** The git commit date of this file is the
> timestamp. For real priority, this content should also be deposited at
> an immutable external archive (arXiv / Zenodo DOI) — recommended, and
> outside the repo's control.
>
> Scope note (`07_primacy.md` §7.1): these are the **physics branch's**
> falsifiable forward claims. The math branch's primacy rests on breadth
> of ∅-axiom derivation, independent of any measurement.

---

## What makes a row belong here

A prediction qualifies as *forward* (not retrodiction) only if **both**:

1. The deciding measurement is **not yet made** (or will decisively
   sharpen) on a **named experiment with a timeline**, and
2. A plausible experimental outcome would **falsify** DRLT — the claim
   carries risk.

Every DRLT value below is pinned by a **PURE** Lean theorem
(`#print axioms` empty), so the prediction is fixed by the `(NS,NT,c,d) =
(3,2,2,5)` atomic signature, not adjustable after the fact.

Retrodictions (1/α_em, m_μ/m_e, m_p, Koide Q=2/3, magic numbers, …) are
**deliberately excluded** from this register — they live in
`catalogs/falsifiers.md` and are reproductions, not predictions.

---

## P1 — Neutrino mass ordering is NORMAL (highest-confidence binary)

| | |
|---|---|
| **DRLT claim** | Normal ordering; `m_3/m_2 ≈ 5.71` |
| **Lean anchor (PURE)** | `Mixing.NeutrinoMixing.PMNS_simplicial_pattern`; ratio in `NeutrinoRatioDerivation` (F3) |
| **Experiment / date** | JUNO, mass-ordering determination **~2030** |
| **Falsifier** | JUNO measures **inverted** ordering → DRLT discarded |
| **Why it carries risk** | Ordering is a genuine **binary**; JUNO resolves it independently of other parameters. A coin-flip prior makes this the cleanest could-go-either-way test in the program. |

This is the strongest pre-registration: a one-bit prediction on a
near-term experiment whose result DRLT cannot retro-adjust.

---

## P2 — θ_QCD is nonzero at ≈ 2.86 × 10⁻¹¹ (the contrarian prediction)

| | |
|---|---|
| **DRLT claim** | `θ_QCD = J·α_GUT⁴ ≈ 2.86×10⁻¹¹`, bracket `[2.51, 3.00]×10⁻¹¹` |
| **Lean anchor (PURE)** | `Couplings.ThetaQCD.theta_QCD_precision_bracket` (`286 ∈ [251,300]·10⁻¹³`), `drlt_below_bound`, `theta_QCD_pattern` |
| **Experiment / date** | Next-generation neutron-EDM, **~2027–2030** |
| **Falsifier** | nEDM constrains θ_QCD **outside [2.51, 3.00]×10⁻¹¹** (incl. consistent-with-zero below 2.5×10⁻¹¹) → DRLT discarded |
| **Why it carries risk** | This is **contrarian**: the mainstream resolution of strong-CP (Peccei–Quinn / axion) drives θ_QCD → 0. DRLT instead pins a *specific small nonzero value*. The two pictures diverge exactly in the next-gen nEDM window — a sharp, distinctive, falsifiable disagreement. |

The most scientifically valuable row: a prediction that *differs from the
field's default expectation* and is testable on a definite timeline.

---

## P3 — PMNS angles are simplicial (octant + maximality at risk)

| | |
|---|---|
| **DRLT claim** | `sin²θ₁₂ = 4/13` (NT²/(NS²+NT²)); `sin²θ₂₃ = 1/2` (maximal); `δ_CP` denom `d²−1 = 24` |
| **Lean anchor (PURE)** | `Mixing.NeutrinoMixing.PMNS_simplicial_pattern` |
| **Experiment / date** | DUNE / Hyper-Kamiokande precision, **~2030+** |
| **Falsifier** | Precision measurement places θ₂₃ decisively **off maximal** (non-1/2 octant) or θ₁₂ outside the 4/13 bracket → DRLT (this sector) discarded |
| **Why it carries risk** | Current global fits already mildly disfavor exact maximal θ₂₃; DUNE/HK will settle the octant. `sin²θ₂₃ = 1/2` is a hard structural commitment with no tuning room — a real exposure. |

---

## P4 — Super-heavy stability island at Z = 168 (long-horizon)

| | |
|---|---|
| **DRLT claim** | Magic-number closed form predicts a stability island at **Z = 168** (HO magic-7 extension) |
| **Lean anchor** | F14 (magic-number closed form, `Nuclear/`) |
| **Experiment / date** | Super-heavy synthesis, **2050+** |
| **Falsifier** | Island found at a different integer → magic-number Lens discarded |
| **Why it carries risk** | Distinctive integer prediction; long timeline but unambiguous if reached. |

---

## Near-term scorecard (the ones that matter by 2030)

| Pred | Quantity | DRLT (PURE-pinned) | Decides | When | Risk |
|---|---|---|---|---|---|
| **P1** | ν ordering | normal, m₃/m₂≈5.71 | JUNO | ~2030 | binary coin-flip |
| **P2** | θ_QCD | 2.86×10⁻¹¹ | nEDM | ~2027–30 | contrarian vs axion→0 |
| **P3** | sin²θ₂₃ | 1/2 (maximal) | DUNE/HK | ~2030+ | octant tension live |

If all three land, DRLT has made **three correct forward calls** on
independent experiments — qualitatively different evidence from any
number of retrodictions. If any one fails, the falsifiability contract
(`seed/AXIOM/08_falsifiability.md` §8.2) fires.

---

## What to do with this file (outside the repo)

1. **Deposit externally now.** Put P1–P3 (with the PURE Lean theorem ids)
   in an arXiv note or a Zenodo record to get a citable, immutable
   timestamp. The git date is good; an external DOI is unforgeable.
2. **State the brackets numerically and do not move them.** The whole
   value of pre-registration is destroyed by post-hoc bracket
   adjustment — any later change must be a *new*, separately-timestamped
   prediction, never an edit to these.
3. **Track outcomes here.** As each experiment reports, append a dated
   "Outcome" line — confirmed or falsified — without altering the
   original claim.

## See also

- `VERIFICATION_SPINE.md` — the axiom→number audit path
- `DEGREES_OF_FREEDOM_LEDGER.md` — why these values are not tunable
- `catalogs/falsifiers.md` — the full F1–F26 catalog (incl. retrodictions)
- `seed/AXIOM/08_falsifiability.md` — the falsifiability contract
</content>
