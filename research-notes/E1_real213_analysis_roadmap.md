# E1 — Marathon roadmap for *full* analysis / calculus on Real213

## Goal

Accept Real213 as native ℝ and formalize the **full program of
Bishop-style constructive analysis** framework-internally.  No
attempt to map to ZFC ℝ — *213's own* analysis.

## Methodology

- Lean 4 core only (no Mathlib).
- 0 sorry, 0 external axioms (≤ propext + Quot.sound).
- 213-internal rebuild of Bishop (1967) + Bridges-Vita (2006)
  literature — *that program is prior art*, 213's contribution is
  *substrate uniformity* (Lens) + *machine verification*.
- Points where it gets stuck = true framework boundary candidates
  (CLAUDE.md falsifiability applied).

## Phase A — Type-level foundation of Real213

| # | Milestone | Status | File |
|---|-----------|--------|------|
| A1 | Real213 type definition | ✓ done | `Real213.lean` |
| A2 | equivalence (refl/symm/trans) + Setoid | ✓ done | `Real213Equiv.lean` |
| A3 | Constant embedding (Raw → Real213) | ✓ done | `Real213Const.lean` |
| A4 | Order (le, lt) — Bishop-style | ✓ done | `Real213Order.lean` |
| A5 | Constructive sign / positivity | ✓ done | `Real213Sign.lean` |

**A4 challenge**: precise use of order proxy = orderProj m k.
Typical definition of le: ∀ k ≥ 1, ∃ N, ∀ i ≥ N, projection
inequality holds with margin 1/k.

**A5 challenge**: *constructive* form of trichotomy — weak form of
`r > 0 ∨ r ≤ ε` (no full LEM trichotomy).

## Phase B — Arithmetic structure

| # | Milestone | Status | Notes |
|---|-----------|--------|-------|
| B0 | Real213StrictPos subtype (solution from E2) | ✓ done | `Real213StrictPos.lean` |
| B1 | Addition (on StrictPos) | **wall** | modulus combination proof incomplete (see E2) |
| B2 | Negation | pending | use Raw's a/b swap? abLens-internal swap |
| B3 | Multiplication | pending | product modulus for bounded sequences |
| B4 | Division (with positivity) | pending | *modulus* form of r ≠ 0 |
| B5 | Algebraic compatibility of equiv (le part) | partial | `Real213OrderExtra.lean` (le_of_equiv, equiv_of_le_le) |

**Core of B**: the modulus of addition = the modulus of the *sum* =
*max of each modulus* (or +1 correction).  Standard result of
Bishop §1.2.

## Phase C — Convergence + Cauchy completeness

| # | Milestone | Status |
|---|-----------|--------|
| C1 | Real213-valued sequence | pending |
| C2 | Cauchy definition for Real213 sequences | pending |
| C3 | Cauchy completeness of Real213 (Cauchy → limit) | pending |
| C4 | Convergence of monotone bounded sequence (constructive form) | pending |

**Foundation of C3**: since Real213 itself is a (sequence + modulus)
pair, Cauchy completeness is *almost trivial* — a key shortcut of
Bishop's approach.

## Phase D — Continuity

| # | Milestone | Status |
|---|-----------|--------|
| D1 | Real213 → Real213 function type | pending |
| D2 | Continuity (modulus form, Bishop-style) | pending |
| D3 | Uniform continuity on bounded interval | pending |
| D4 | Composition + arithmetic preservation | pending |
| D5 | Constant + identity functions are continuous | pending |

## Phase E — Differentiation

| # | Milestone | Status |
|---|-----------|--------|
| E1 | Difference quotient | pending |
| E2 | Differentiability (modulus form) | pending |
| E3 | Sum/product rule | pending |
| E4 | Chain rule | pending |
| E5 | Mean value theorem (constructive form) | pending |

## Phase F — Integration

| # | Milestone | Status |
|---|-----------|--------|
| F1 | Riemann partition | pending |
| F2 | Cauchy sequence of Riemann sums | pending |
| F3 | Definition of integral (continuous integrand only) | pending |
| F4 | Fundamental theorem of calculus (FTC) | pending |
| F5 | Linearity, monotonicity | pending |

## Phase G — Specific functions

| # | Milestone | Status |
|---|-----------|--------|
| G1 | exp, log via power series | pending |
| G2 | sin, cos via power series | pending |
| G3 | Framework-internal definition of π | pending |
| G4 | Ditto for e (already partially in EulerCombinatorialPure) | partial |

## Phase H — Specific theorems

| # | Milestone | Status |
|---|-----------|--------|
| H1 | IVT (constructive, with explicit interval halving modulus) | pending |
| H2 | Extreme value theorem (uniform continuous on compact) | pending |
| H3 | Taylor expansion | pending |
| H4 | Explicit modulus form expression for anonymous ε-N | pending |

## Suggested progress priority

1. **A4 + A5** (order + sign) — most basic of analysis.  ~a few days.
2. **B1 + B5** (addition + equiv compatibility) — first step of arithmetic.
3. **C3** (Cauchy completeness) — *almost trivial* given Real213's
   definition.  A big symbolic milestone.
4. **D1-D5** (continuity) — substrate of basic calculus.
5. ... marathonically thereafter.

## Estimated effort

Each milestone ≈ 1-3 Lean files (each ≤ 80 lines).  Total ≈ 50-100
modules.  Multiple milestones possible per session.

## Falsifiability checkpoints

Expected stuck points pre-marked for each phase:

- **B2 (negation)**: is Raw's a/b swap natural?  (SwapLens already
  exists)
- **B4 (division)**: *constructive* form of positivity — tricky even
  in Bishop.
- **D3 (uniform continuity)**: framework-internal definition of
  *compact* — key to bypassing ZFC compact.
- **F3 (integration)**: measure theory ⇒ bypass = Riemann only.
  Lebesgue is absent from the framework (separate large effort).
- **G3 (π)**: a *constructive series* for π is possible (Leibniz or
  Wallis), but no closed form.

If all of the above are stuck, falsifiability applies — if any phase
is *permanently* stuck, framework is discarded (CLAUDE.md §1.5).

## ROI awareness

- Phase A-C is the *foundation* — most important to reach here,
  approximately 8-15 modules.
- Phase D-F is *core analysis* — maximum effort required.
- Phase G-H is *specific results* — bonus, if needed.

## Cross-references

- `notes/D1_zfc_real_as_final_boss.md` (retracted framing, valid evidence).
- `notes/D2_complexity_class_hierarchy.md` (Tier classification).
- `notes/D3_real213_native_R.md` (Real213 = native ℝ statement).
- `framework/E213/Research/Real213.lean`, `Real213Equiv.lean`,
  `Real213Const.lean` (Phase A 의 done parts).
- `framework/E213/Research/HasModulus.lean` (Bishop modulus
  infrastructure).
- `framework/E213/Research/PellHasModulus.lean` (concrete instance).
