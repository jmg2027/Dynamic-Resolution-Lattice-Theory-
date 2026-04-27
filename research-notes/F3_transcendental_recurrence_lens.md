# F3 — Recurrence Lens classification of transcendentals

## User question (2026-04-26)

> "On 213's natural number pickup protocol, are transcendentals like
> π or e defined as a stream with a special pattern-generating rule
> (or lens structure), beyond just an endless trajectory?"

Specialization of D2's FSM/ICT classification to cut form.

## Core framing

Each real is a valid function of RealCut (Nat → Nat → Bool).  The
*Generating Lens* (recurrence) is the rule that unfolds this cut
function.

**Recurrence Lens** structure:

```
state : Type
init : state
transition : state → state
output : state → Nat → Nat → Bool
```

각 step: state n+1 = transition (state n).  Cut at (m, k) by partial
output 의 limit.

## Classification

### Tier 1 — Algebraic (FSM)

State = finite (Fin n).  Transition = modular.  Convergence = exact
finite step (rational) or cyclic.

- Rationals: 1-state Lens (constant).
- √p (algebraic irrationals): Pell-type state, mod-N Lens with finite
  period.

### Tier 2a — Transcendental with canonical Lens

**e**: state = (i, factorial_i, partial_sum_i).
- transition: i → i+1, factorial *= i+1, sum += 1/factorial.
- Recurrence: a_{i+1} = a_i / (i+1).
- Convergence: tail ≤ 2/(N+1)! — super-exponential.
- Has a *canonical* Lens — natural unique choice.

### Tier 2b — Transcendental with multiple Lenses

**π**: multiple representations:
- Leibniz: a_i = (-1)^i / (2i+1), tail ~ 1/N — slow.
- Wallis: product (2i)²/((2i-1)(2i+1)) — moderate.
- Madhava-Leibniz: combined — faster.
- BBP (digit extraction) — fast.

All are valid Lenses, all yield the same cut-equivalence class.
*No canonical choice* — no "preferred" Lens structure for π.

## Significance

All reals within 213 are *unfoldings of some Lens-recurrence*:

- Algebraic: finite state (Tier 1).
- Transcendental with canonical: factorial / specific recurrence.
- Transcendental with multiple: equivalence class of Lenses.

Difference from ZFC ℝ's *power-set* arbitrary subset: all reals
within 213 have a *generative recurrence*.  No "arbitrary" subsets —
every cut function is the output of some Lens.

## Cross-references

- `notes/D2_complexity_class_hierarchy.md` (FSM/ICT classification).
- `notes/F2_real_as_lens_output.md` (Real = Lens output reframe).
- `framework/E213/Research/Real213CutExp.lean` (e 의 recurrence
  Lens — factorial series).
- `framework/E213/Research/Real213RecurrenceLens.lean` (formal
  structure).
