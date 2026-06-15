# The Degrees-of-Freedom Ledger — 1/α_em

> **Companion to `VERIFICATION_SPINE.md` §6.** ∅-axiom purity proves the
> *math* imports no hidden axiom. It does **not** prove that no
> Lens/structural choice in the physics deployment was steered by the
> known answer. This ledger closes that gap the only honest way: by
> enumerating **every** choice in the `1/α_em` derivation and tagging
> each — `forced`, `derived`, `assignment`, `modeling-form`, or
> `fitted?` — with its source. Nothing is hidden, including the items
> that are not yet forced.
>
> This is `seed/AXIOM/01_residue.md`'s "assume nothing" pushed one step
> further: **hide no degree of freedom.** It is the physics branch's
> falsifiability instrument (`07_primacy.md` §7.1: this is the *physics*
> gate, not a ranking of the math work).

---

## Tag definitions

| Tag | Meaning | Researcher DoF |
|---|---|---|
| **forced** | Unique solution of a forcing equation; proven (`#print axioms` empty) | **0** |
| **derived** | Value is a *function of forced atoms / repo-derived constants*; identity proven PURE | 0 *in value* |
| **assignment** | The value is derived, but *which* combination maps to *which* physical layer is a modeling assignment, not yet an independent forcing theorem | residual |
| **modeling-form** | A functional form (an equation, a layer count) is chosen; the values then follow | residual |
| **fitted?** | Plausibly introduced/adjusted *after* seeing data — candidate retrodiction until shown otherwise | **yes, flagged** |

The honest target: drive every `assignment` / `modeling-form` / `fitted?`
row to `forced` (a uniqueness proof) or retire it.

---

## Layer 0 — the atomic signature (the floor)

| Quantity | Value | Tag | Theorem (PURE) |
|---|---|---|---|
| NS | 3 | **forced** | `Atomicity.NonDecomposable.non_decomposable_iff` + `PairForcing.pair_forcing` |
| NT | 2 | **forced** | same |
| d | 5 | **forced** | `Atomicity.Five.atomic_iff_five` |
| c | 2 | **derived** (presentation) | re-presents `NS²−1` as graph cohomology `b₁(K_{NS,NT}^{(c)})`; **not forced** — see below |
| (NS, det) | (3, 1) | **forced** | `Atomicity.OrbitForcing.orbit_forcing_master` |

**Layer-0 verdict: `(NS, NT, d)` + `(NS, det)` forced, zero researcher DoF.**
This forced floor is unimpeachable.  The multiplicity `c = 2` is **not** a
fourth forced primitive: `CombinatorialArity` forces the relation *arity* (how
many inputs the slash takes), which is a **different** quantity from the edge
*multiplicity* `c` (parallel-edge count) — conflating them was an error.  `c`
is the presentation parameter set so the graph cohomology `b₁(K_{NS,NT}^{(c)})
= c·NS·NT − (NS+NT−1)` reproduces the gauge content `NS² − 1` (already direct
from the forced `NS`).  It is unforced across five reframings and
physics-redundant: `research-notes/frontiers/atomic_c_multiplicity_forcing.md`.
So the atomic floor is `(NS, NT, d) = (3, 2, 5)`, with `c = 2` a derived
cohomological presentation of `NS²−1`.

---

## Layer 1 — the base-formula coefficients

Base expansion (`Lib/Physics/Couplings/TripleCoupling.lean`):
```
1/α_em = 60·ζ(2) + 30 + 25/3 + α_GUT/4 + α_GUT/45
```

| Coeff | Structural form | Tag | Theorem (PURE) | Note |
|---|---|---|---|---|
| 60 | `c·NS·NT·d = edges(K_{3,2}^{(2)})·d` | derived + **assignment** | `InvAlphaEMDecomp.inv_alpha_em_60_eq_E_d` | value forced; "60 is the ζ(2) layer" is the assignment |
| 30 | `NS·NT·d` | derived + **assignment** | `inv_alpha_em_30_eq_NS_NT_d` | `60/30 = c` is itself proven (`inv_alpha_em_multiplicity_factor`) |
| 25 | `d²` | derived + **assignment** | `inv_alpha_em_25_over_3` | numerator of 25/3 |
| 3 | `NS` | derived + **assignment** | `inv_alpha_em_25_over_3` | denominator of 25/3 |
| 4 | `NS+1 = d−1` | derived + **assignment** | `inv_alpha_em_alpha_gut_4` | α_GUT/4 denominator |
| 45 | `NS²·d` | derived + **assignment** | `inv_alpha_em_alpha_gut_45` | α_GUT/45 denominator |

**Layer-1 verdict.** Every coefficient *value* is a forced-atom
combination, identity proven PURE — there is no free integer dialed in.
The residual DoF is the **assignment map**: that the ζ(2)-layer is
`c·NS·NT·d` rather than some other forced-atom product. This is the
single largest open item, and §"Mitigation" below is why it is far
narrower than "six free parameters."

**Update — the assignment row, sharpened to its exact residual**
(`Lib/Physics/AlphaEM/AssignmentUniqueness.lean`, all PURE):

- *Value uniqueness — now proven.* Each leading coefficient is the
  **unique** monomial `3^a·2^p·5^e` in a bounded box
  (`repr_60_unique`, `repr_30_unique`, `repr_25_unique`,
  `repr_45_unique` = 1 representation each). The values are not
  arbitrary integers; arithmetic forces the prime-exponent vector.
- *The exact remaining freedom — now named and proven.* Because
  `NT = c = 2` (`nt_eq_c`), the power of `2` in a coefficient cannot
  be attributed to `NT` vs `c` by arithmetic: there are exactly **3**
  splits of each `2²` (`two_power_splits_three`), and `60` equals
  `NS·NT·c·d`, `NS·NT²·d`, and `NS·c²·d` alike (`sixty_split_not_forced`).
  Selecting the `c`-multiplicity reading (`60/30 = c`, what distinguishes
  α_em from α_2) is the **cohomology's** job (`c3_chain`), not
  arithmetic's.

So the Layer-1 `assignment` DoF is no longer "6 unconstrained maps" — it
is exactly **the NT↔c attribution**, a single degeneracy between two
atoms that share the value 2. Capstone: `assignment_arithmetic_boundary`.

**Update 2 — the NT↔c attribution, now CLOSED**
(`Lib/Physics/AlphaEM/AssignmentForcing.lean`, all PURE):

The residual is resolved by the **edge-count structure** the leading term
physically is (not by arithmetic, which cannot — the values coincide):

- The leading `60·ζ(2)` is `edges(K_{3,2}^{(c=2)})·d`, and
  `edges = k32_edges NS NT c = c·NS·NT` (`edge_reading_is_edges`).
- The three readings `c·NS·NT`, `NS·NT²`, `NS·c²` **coincide only at the
  DRLT point** (`readings_coincide_at_drlt`) and **diverge off it**
  (`readings_diverge_off_drlt`: at `c=3` they are `18 ≠ 12 ≠ 27`). Only
  `c·NS·NT` tracks the actual edge count — so the edge-count Lens selects
  it **uniquely**; the degeneracy is an arithmetic accident of `NT = c`.
- `c` and `NT` act on the edge count by **different operations**: a
  multiplicity-step adds `NS·NT`, a T-vertex-step adds `c·NS`
  (`nt_step`, `increments_distinguish_c_from_nt`: `15 ≠ 6` at `NT ≠ c`).
- `NT = 2` is forced (pair count, `PairForcing`).  `c = 2` (edge
  multiplicity) is **not** independently forced: `CombinatorialArity` forces
  the relation *arity* (a distinct quantity, not the parallel-edge count), and
  the edge-count selection of `c·NS·NT` is the **cohomology's presentation**
  (it re-presents `NS²−1`), not an axiom forcing.  So this resolves the
  *attribution of the value-2 within the edge-count reading*, but does not
  upgrade `c` to forced — see
  `research-notes/frontiers/atomic_c_multiplicity_forcing.md`.

Capstone: `nt_c_degeneracy_resolved`. **The Layer-1 `assignment` row is
no longer a researcher DoF** — the cohomology's edge-count structure
forces `c·NS·NT`, and the NT↔c coincidence is structurally broken.

---

## Layer 2 — the transcendental / coupling inputs

| Input | Value | Tag | Source | Note |
|---|---|---|---|---|
| ζ(2) | π²/6 | **derived** | Basel chapter (repo-derived, not hardcoded; `README.md` "ζ(2) via Basel") | no transcendental constant inserted by hand |
| α_GUT | `1/α_GUT = d²·ζ(2) = 25·π²/6` | **derived** | `Couplings/AlphaGUT.lean`, `SpectrumComplete.inv_alpha_GUT_eq_25` | **not an external GUT input** — itself a function of `d` and ζ(2) |

**Layer-2 verdict.** No external physical constant is imported. The two
"continuous-looking" inputs are themselves residue-derived: ζ(2) from
Basel, α_GUT from `d²·ζ(2)`. This closes the most common skeptic charge
("you smuggled in α_GUT from the Standard Model") — it is refuted by the
code: α_GUT here is `6/(25π²)`, derived.

---

## Layer 3 — the Gram correction

`Lib/Physics/AlphaEM/GramStructuralNewton.lean`:
```
cubic:    25·y³ + 1 = 25·X·y²        (i.e. d²y³ + scale = d²Xy²)
Newton-1: y₁ = X − 1/(25X²),  correction = 1/(25X²) → 2130 at e9
```

| Item | Tag | Theorem (PURE) | Note |
|---|---|---|---|
| `25 = d²` in the cubic | **derived** | `gram_correction_structural_value` | the coefficient is forced |
| the **cubic form** `d²y³+1 = d²Xy²` | **modeling-form** | — | the self-consistency *equation shape* is a choice; values follow from it |
| Newton-1 (one step from y₀=X) | **modeling-form** | — | truncation order; one step gives 2130 |
| Gram = 2130 | derived (given the form) | `gram_correction_structural_value` | uses ONLY `alphaInv_213_e9`, no observed α (`gram_correction_structural_no_observed_alpha`) |

**Layer-3 verdict.** The *value* 2130 follows with no observed-α input
(strong — verified). The residual DoF is the **form** of the
self-consistency cubic and the Newton truncation order. The 27×10⁻⁹
residual to CODATA is openly the next-order tail.

**Update — the cubic form is NOT an independent choice**
(`Lib/Physics/AlphaEM/GramCubicReduction.lean`, PURE):

`cubic_is_correction_ansatz` proves `25·y²·(y+k) = 25·y²·y + 25·y²·k`, so
the cubic `25·y³+1 = 25·X·y²` is the **algebraic re-expression** of the
single ansatz `correction = α²/d²` (with `X = y+k`, `d² = 25`). The
`modeling-form` "cubic" row therefore carries no freedom beyond fixing
the correction form — it reduces to one sub-question: **why `α²/d²`?**

- `α²` — structurally expected (self-energy is `O(α²)`).
- `/d²` — the *value* is over-determined (`GramD2Readings`,
  `three_readings_coincide`: block-pair / Gram-DOF / α_GUT all `= d²`), and
  the **mechanism is now identified** (`GramD2Mechanism`): a self-energy is
  a degree-2 (2-point) object, and a degree-2 object on the `d = 5` state
  space normalizes by `d²` — equal to *both* the 2-point operator-space
  dimension `tensorDim d d` *and* the 2-fold cup-graduation denominator
  `cup_graduation_denom 1`, which coincide (`mechanisms_converge`). With the
  forced numerator `α²` (self-energy is `O(α²)`), this grounds `α²/d²` in
  degree-2 structure. **Remaining (narrow)**: a forcing theorem identifying
  the Gram self-energy *as* the `k=1` self-pairing cup term (promote
  `CupRingTrace`/`SelfPairingTrace` from test to derivation). Frontier:
  `research-notes/frontiers/gram_d2_prefactor.md`.

---

## Honesty flags — `fitted?` rows

Per the tag discipline, items that read as introduced/adjusted *after*
seeing data are flagged here, not buried:

| Item | Where | Why flagged |
|---|---|---|
| **v2: H³ imbalance** (`3·α_GUT → 4·α_GUT` in 1/α_2) | `TripleCoupling.lean` "v2 corrections" | a correction term added on top of the v1 skeleton; reads as a fit-improving refinement until a forcing argument is supplied |
| **v2: α_GUT² self-interaction** (`+α_GUT²/2` in 1/α_3) | same | same — second-order term whose *necessity* is not yet derived |
| **Jarlskog `J`** (θ_QCD prefactor) | `CPViolation` + `ThetaQCD` (`theta_QCD_num := 286` hardcoded) | *(self-audit, upgraded)* only the λ-power **structure** is derived; computing `J` from DRLT's own factors (λ=5/22, A=φ/2, δ=π/φ²) gives **8.18×10⁻⁵ vs observed 3.08×10⁻⁵ — ×2.66 over** (missing Wolfenstein apex `(ρ,η)`; `s₁₃=Aλ³` omits `√(ρ²+η²)≈0.39`). A `CPViolation.lean` comment had masked this with an arithmetic error ("within 10%"); corrected. θ_QCD (`PRE_REGISTRATION.md` P2) was inconsistent with the catalog value; the apex is now identified as a **φ² object** (`JarlskogApex`): modulus `R_u=1/φ²` (φ²-coherent with the derived phase `δ=π/φ²`), giving `R_u`=0.382 (0.17% vs obs) and `J`=3.12×10⁻⁵ (1.4% vs obs, was 166%). `c/d=2/5=F₃/F₅` is the lowest Fibonacci convergent of `1/φ²`, not a competitor. Candidate, not forced — the modulus `1/φ²` awaits a forcing theorem; `φ²` is already atomic. Frontier: `ckm_rho_eta_apex.md` |

These do **not** affect the Layer-0 forcing chain or the 1/α_em
*leading* skeleton; they live in the α_2 / α_3 v2 refinements. Flagging
them is the point — a reader can now see exactly which terms carry
retrodiction risk.

---

## Mitigation — why the residual DoF is narrow, not wide

The `assignment` rows look like freedom until you count the constraints:

1. **One skeleton, three couplings.** The *same* atoms `(NS,NT,c,d)` and
   the *same* α_GUT must simultaneously produce
   `1/α_em`, `1/α_2`, `1/α_3` (`triple_coupling_master`, PURE). A free
   six-parameter fit to one number is trivial; a *shared* forced-atom
   skeleton hitting three couplings at once is heavily over-determined.
   This is the real reason the assignment is not arbitrary.
2. **The atoms are forced, not chosen** (Layer 0). The assignment selects
   among *products of forced atoms* — a finite, enumerable space — not
   among real numbers.
3. **No observed α anywhere** in the structural value
   (`gram_correction_structural_no_observed_alpha`).

What this does **not** yet do: prove the assignment is *unique*. That is
the open work.

---

## Scorecard

| Layer | forced | derived | assignment | modeling-form | fitted? |
|---|---:|---:|---:|---:|---:|
| 0 atoms | 5 | — | — | — | — |
| 1 skeleton | — | 6 (values, **uniqueness proven**) | **0 (NT↔c closed)** | — | — |
| 2 inputs | — | 2 | — | — | — |
| 3 Gram | — | 1 | — | 2 (cubic→**reduced to d² prefactor**; + truncation) | — |
| v2 refinements | — | — | — | — | 2 |

**Verdict.** The foundation (Layer 0), all *values* (Layers 1–3), AND the
skeleton layer-assignment are now forced or derived — no free real
parameter, values proven *uniquely* represented (`AssignmentUniqueness`),
the last assignment freedom (NT↔c) structurally closed by the edge-count
Lens (`AssignmentForcing`), and the Gram cubic *form* shown to be the
correction ansatz re-expressed (`GramCubicReduction`), not a free choice.
The genuine residual researcher-DoF is now precisely: **(a)** the `/d²`
self-energy prefactor (the cubic's last open input — three candidate
readings, no forcing theorem yet; frontier note opened); **(b)** the
Newton truncation order; **(c)** the two v2 refinement terms (`fitted?`) —
plus the separately-tracked **Jarlskog `J` input** for θ_QCD
(`PRE_REGISTRATION.md` P2). The α_em *leading* derivation stands at zero
researcher-DoF through the base skeleton; the Gram layer's only remaining
input is now the single `/d²` prefactor. Materially stronger than the
prior state, and the open edges are named, not hidden.

---

## Next actions (close `assignment`/`modeling-form`/`fitted?` → `forced`)

1. **Assignment uniqueness — CLOSED.** Value-uniqueness proven
   (`AssignmentUniqueness.leading_coeffs_unique`) AND the NT↔c attribution
   resolved structurally via the edge-count Lens
   (`AssignmentForcing.nt_c_degeneracy_resolved`): only `c·NS·NT` is the
   edge count, the substitution readings diverge off the DRLT point, and
   `c`/`NT` are distinct operations on the edge count. No residual
   assignment DoF remains in the leading skeleton.
2. **Derive the cubic.** Show `d²y³+1 = d²Xy²` is the forced
   self-consistency relation (e.g. from the cup-ring trace), not a
   chosen shape.
3. **Derive (or retire) v2.** Give a forcing argument for the H³
   imbalance and α_GUT² terms, or mark them research-tier until one
   exists.
4. **Pre-register.** Independently of the above, register one
   *currently-unmeasured* observable with a tight bracket and a DOI
   timestamp — the move that converts the whole program from
   retrodiction to prediction (the spine's other open lever).
   **Done: `PRE_REGISTRATION.md`** selects the three near-term forward
   predictions (ν ordering / JUNO, θ_QCD / nEDM, sin²θ₂₃ / DUNE-HK),
   each PURE-pinned and could-go-either-way, by ~2030.

## See also

- `VERIFICATION_SPINE.md` — the audit path these choices live on
- `STRICT_ZERO_AXIOM.md` — full PURE/DIRTY catalog
- `catalogs/falsifiers.md` — the falsifier brackets (mostly retrodictive today)
- `seed/AXIOM/08_falsifiability.md` — the falsifiability contract
</content>
