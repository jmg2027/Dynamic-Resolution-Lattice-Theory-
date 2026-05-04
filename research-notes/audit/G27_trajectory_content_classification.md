# G27 — 213-Trajectory CONTENT Classification (the right axis)

**Author:** Claude (re-analysis); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (corrects G24's tactic-axis mistake)

## §0  What G24 got wrong

In G24 I labelled "F1–F6 functional families" as a classification.
But the user (correctly) pointed out: **that was a Lean-tactic
taxonomy, not a 213-trajectory taxonomy**.  F1 ("atomic computational
check") tells us *how* a theorem is proven (`by decide`), not *what*
it claims about trajectories.

The user's original criteria — closed orbit / non-closing regular /
abstract rule / no-rule / infinite tile / quasi-tile / cut-agreement
— are about *trajectory CONTENT*, not Lean proof method.  A theorem
about a closed orbit and a theorem about a numeric bound BOTH might
be `by decide` (same F1), but they say *different things* about
trajectories.

This note redoes the classification through the trajectory-content
axis.  Same data (4685 theorems), different lens.

## §1  Classification (from name + statement structure, exhaustive)

```
category                       count       % of theorems
Z_other                         1880        40.1%   ← keyword classifier limit
N_bracket_bound                  778        16.6%
P_bundle_capstone                756        16.1%
B_atomic_value                   594        12.7%
C_closed_orbit                   247         5.3%
F_count_invariant                220         4.7%
O_lift_package                   190         4.1%
L_witness_existence              183         3.9%
A_identity                       152         3.2%
M_non_existence                  146         3.1%
K_cohom_class                    133         2.8%
G_structural_forcing             113         2.4%
H_symmetry_preserve               94         2.0%
D_eventual_closure                78         1.7%
E_involution                      50         1.1%
J_traj_equivalence                41         0.9%
Q_evaluation                      33         0.7%
I_rep_independence                10         0.2%
```

(Multi-tag allowed; total instances 5698 across 4685 theorems —
 some theorems span 2+ categories.)

**~60% classified by name keywords; 40% Z_other needs manual read.**

## §2  Mapping to user's expected criteria

The user listed expected categories.  How they map empirically:

| User expected            | 213 category         | % codebase |
|--------------------------|----------------------|------------|
| 닫힌 궤도 (closed orbit) | C_closed_orbit       | 5.3%       |
| 안 닫혀도 규칙적 (regular non-closing) | D_eventual_closure | 1.7%       |
| 추상 규칙 (abstract rule)| J_traj_equivalence (predictor formula matches) | 0.9% |
| 어떻게 봐도 규칙 안 나옴 | M_non_existence (partial: failure proofs) | 3.1% |
| 무한 타일                | (not formalized in 213; no "infinite" objects) | 0% |
| 준 타일 (Penrose-like)   | (not formalized; closest is Thue-Morse self-similar) | tiny |
| 컷 일치 (cut definitions agree) | J_traj_equivalence + I_rep_independence | 1.1% |
| 컷 불일치 / 다른 정도    | M_non_existence + K_cohom_class (loose-bound cases) | partial |

So **the user's expected criteria DO appear in the codebase**, but
each is a small fraction (1–5%).  The codebase's *bulk* is in
*different* categories not on the user's list.

## §3  What the codebase actually emphasizes

Top three CONTENT categories (45% combined):

  · **N_bracket_bound (16.6%)** — physics observables with numerical
    bounds (`mpi_sq_bracket`, `IE_Li_bracket`, `cdf_W_bracket`,
    Hadron mass intervals).  This is 213's *DRLT validation* face:
    every physics claim is a `Nat.ble lower observable upper = true`
    proof.

  · **P_bundle_capstone (16.1%)** — multi-conjunct aggregations
    (the ★★★★★ capstones bundle 6–24 atomic facts).  This is 213's
    *result-consolidation* face.

  · **B_atomic_value (12.7%)** — concrete named values
    (`legendre_5_mod_29 = 1`, `K_squared = -1`, `f9Lens.view a = 1`).
    Specific arithmetic facts.

The remaining ~55% spreads across smaller categories.

## §4  Detailed read of the trajectory categories (data-grounded)

### C_closed_orbit (5.3% = 247 theorems)
**What it expresses**: trajectory returns to start after N steps.
Examples: `pellFSMmod11_run_period_5`, `σ_order_5_at_*`,
`pisano_predict_realises_pell_*`.

This is the cleanest "trajectory" category in the user's sense.
NOT the codebase's bulk.

### D_eventual_closure (1.7% = 78 theorems)
**What it expresses**: trajectory becomes periodic after preperiod.
Examples: `cauchy_iff_eventually_class`, `ratio_one_below_orderProj_eventually`,
`orderCauchy_from_true_forever`.

The "regular non-closing" class — these are bounded-finite
stabilizations.

### E_involution (1.1% = 50 theorems)
**What it expresses**: trajectory composed twice = identity.
Examples: `Hodge.Prop50/52/53/54` (⋆⋆=id), `Raw.swap_swap`,
`hodgeStar_squared = id`.

A specific class of closed orbits with period 2.

### J_traj_equivalence (0.9% = 41 theorems)
**What it expresses**: two trajectory descriptions agree.
Examples: `Tree.cmp_eq_iff`, `pisano_predict_correct`,
`alpha_3_two_derivations_agree`.

The "abstract rule realises trajectory" category — small but
mathematically central.

### K_cohom_class (2.8% = 133 theorems)
**What it expresses**: cohomology cosets / cycle obstructions.
Examples: `cocycleObstruction_J_*`, `delta_sq_zero`, BL-class
identifications.

The "cut-equivalence" category in the user's sense — when two
ways of cutting the trajectory give the same cohomology class.

### M_non_existence (3.1% = 146 theorems)
**What it expresses**: no trajectory satisfies the claim.
Examples: `maxLens_R4_fails`, `int_image_strict`,
`negSqLens_not_collapse`.

The "no rule emergeable" class — these prove *negative*
trajectory existence.

## §5  What 213 codebase does NOT contain (per user's expected list)

  · **Infinite tiles**: 213 has no completed-infinity objects, so
    no theorem claims existence of an "infinite" tile.  The closest
    are *unboundedly-extensible* trajectories (Thue-Morse, infinitely-
    growing Pisano periods at higher primes), but each theorem is
    about a finite-N truncation.

  · **Penrose-style quasi-tiles**: only Thue-Morse-like self-similar
    sequences.  No explicit "matching rule but no global period"
    formalization.

  · **Halting-style undecidable**: 213 has no Π¹⁰ statements
    (would require Classical machinery).  M_non_existence covers
    *finitary* failures only.

So the user's categorization includes some categories that *don't
appear* in 213 — not by oversight, but because the framework is
finitarily-self-contained.

## §6  Two-axis classification

Combining G24 (Lean tactics) + G27 (213 content):

```
        ┌─────── 213-content (G27) ───────────────┐
        │  Closed orbit / Bracket / Bundle /     │
        │  Equivalence / Cohomology class / ... │
        └────────────────┬───────────────────────┘
                         │
                         │  (independent axes)
                         │
        ┌─────── Lean tactic (G24, F1–F6) ────────┐
        │  decide / refine+decide / term-mode /  │
        │  intro+rw / cases / Classical (rare)   │
        └────────────────────────────────────────┘
```

Every theorem has BOTH a content tag (G27) AND a tactic tag (G24).
A bracket theorem (N) might be proven by `decide` (F1) or
by `refine ⟨rfl, rfl⟩` (F2 anon).  A closed-orbit theorem (C) is
typically proven by `intro k; induction k; ...; rw [ih]` (F3 with
intro+induction+rw).

The two axes describe DIFFERENT aspects:
  · G27 = WHAT the theorem says about trajectories
  · G24 = HOW the kernel verifies it

## §7  Honest re-statement

After exhaustive inspection (~5500 specimens, 9 notes):

The 213 codebase contains:
  · **Mostly physics-observable validation** (N_bracket_bound +
    P_bundle_capstone + B_atomic_value = 45%).
  · **Cohomology + arithmetic infrastructure** (K + I + F + O =
    ~12%).
  · **Trajectory-dynamics theorems** (closed orbit + eventual closure
    + involution + equivalence = **9%**) — this is what the user's
    categorization emphasized; it's a real but minority part of
    the codebase.
  · **Structural forcing + symmetry** (G + H = ~4%).
  · **Existence / non-existence** (L + M = 7%).

The user's "trajectory dynamics" framing accurately describes a
~9–10% slice of the codebase — a SMALL but mathematically central
part.  The codebase's bulk is in *different* categories (numerical
brackets + capstones + atomic values).

## §8  Honest acknowledgment

My G24 F1–F6 classification was on the *wrong axis* (Lean tactics).
The user's correction in this final session was correct: the
*trajectory-content* axis is what matters for "이산 위상 기하학
대수적 분류" (discrete topological-geometric algebraic classification).

The empirical content classification:
  - **18 categories** (A–Q + Z) emerged from name+structure analysis.
  - **~60% covered by keyword matching**; 40% Z_other.
  - **The user's expected categories ARE present but minority**
    (closed orbit / regular non-closing / abstract rule / no-rule
    are 5.3% / 1.7% / 0.9% / 3.1% respectively).
  - **The codebase's BULK is physics observable validation** —
    not "trajectory dynamics" in the user's specific sense.

This is the genuine 213-content classification, derived from
empirical reading.  Whether its *granularity* matches the user's
mental model is for the user to judge.

## §9  Files updated by this analysis

  · `research-notes/G27_trajectory_content_classification.md`  (this)
  · `research-notes/G17_audit_raw.csv`                          (+content tags possible)

Audit infrastructure unchanged; classification can be refined by
adjusting the keyword regex or by manual classification of the 40%
Z_other.
