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
| c | 2 | **forced** | `Atomicity.CombinatorialArity.arity_2_unique_via_k_ge_3_vacuous` |
| (NS, det) | (3, 1) | **forced** | `Atomicity.OrbitForcing.orbit_forcing_master` |

**Layer-0 verdict: zero researcher DoF, proven.** This is the floor
the whole derivation stands on, and it is unimpeachable. Everything
below is built *from* these — the question is only whether the
*building* adds freedom.

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

---

## Honesty flags — `fitted?` rows

Per the tag discipline, items that read as introduced/adjusted *after*
seeing data are flagged here, not buried:

| Item | Where | Why flagged |
|---|---|---|
| **v2: H³ imbalance** (`3·α_GUT → 4·α_GUT` in 1/α_2) | `TripleCoupling.lean` "v2 corrections" | a correction term added on top of the v1 skeleton; reads as a fit-improving refinement until a forcing argument is supplied |
| **v2: α_GUT² self-interaction** (`+α_GUT²/2` in 1/α_3) | same | same — second-order term whose *necessity* is not yet derived |

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
| 1 skeleton | — | 6 (values, **uniqueness proven**) | 1 (**NT↔c only**) | — | — |
| 2 inputs | — | 2 | — | — | — |
| 3 Gram | — | 1 | — | 2 | — |
| v2 refinements | — | — | — | — | 2 |

**Verdict.** The foundation (Layer 0) and all *values* (Layers 1–3) are
forced or derived — no free real parameter exists anywhere, and the
coefficient values are now proven *uniquely* represented
(`AssignmentUniqueness`). The genuine residual researcher-DoF is exactly
three things, and they are now named and (for the first) sharpened:
**(a)** the skeleton assignment — reduced to the single `NT↔c` attribution
(both = 2), to be closed by the cohomology's `c`-multiplicity reading;
**(b)** the Gram cubic's form + truncation order; **(c)** the two v2
refinement terms. That is the honest state — far stronger than
"numerology," and not yet "0 DoF."

---

## Next actions (close `assignment`/`modeling-form`/`fitted?` → `forced`)

1. **Assignment uniqueness — PARTIALLY CLOSED.** Value-uniqueness is
   proven (`AssignmentUniqueness.leading_coeffs_unique`): each
   coefficient is the unique box-monomial. The residual is now isolated
   to the single `NT↔c` degeneracy (`assignment_arithmetic_boundary`).
   *Remaining*: derive the `c`-multiplicity attribution from the
   cohomology (`c3_chain`'s `60/30 = c`) as a forcing theorem — this is
   a physics derivation, not a `decide`, and is the honest next target.
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

## See also

- `VERIFICATION_SPINE.md` — the audit path these choices live on
- `STRICT_ZERO_AXIOM.md` — full PURE/DIRTY catalog
- `catalogs/falsifiers.md` — the falsifier brackets (mostly retrodictive today)
- `seed/AXIOM/08_falsifiability.md` — the falsifiability contract
</content>
