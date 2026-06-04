# 0 = ∞ and the two folds — the residue at the bottom of the number tower

## Overview

`0` and `∞` are not a dual pair of values; they are **one pre-Lens object** — the residue — named
twice, and the number tower is the machine that excludes it to produce genuine values.  This chapter
consolidates that into one picture.  Under the reciprocal fold `0` and `∞` are the single point at
which the fold returns no value (canon §6.5: at raw level point ≡ K_∞ ≡ ∞).  A fold may handle the
pair only *status-symmetrically* (canon §6.9): treating `0` as a value while treating `∞` as an
unreached limit is a torsioned, mixed-status fold.  `ℤ`'s own fold (negation) therefore has exactly
two correct closures, and the two founding folds — negation (additive) and reciprocal
(multiplicative) — are mirror involutions on the shared four-point fixture `{∞, 0, +1, −1}`,
generating a Klein four-group whose third element is the founding elliptic swap.  The same `0`/`∞`
residue resurfaces, one fold over, as the **maximum-entropy ceiling**: the bottom and the top of the
number tower are the one residue read through the multiplicative and additive folds.

## Lean source

- Files:
  - `lean/E213/Lib/Math/Cauchy/ZeroInfinityHole.lean` — `0`/`∞` as one reciprocal hole (5 PURE)
  - `lean/E213/Lens/Number/IntFoldForms.lean` — ℤ's two status-symmetric fold forms (13 PURE)
  - `lean/E213/Lens/Number/FoldDuality.lean` — negation/reciprocal mirror on the fixture (13 PURE)
  - `lean/E213/Lens/Number/FoldKlein.lean` — the Klein four-group + fixed-point-free antipode (9 PURE)
  - `lean/E213/Lib/Math/DetSpectrumPoles.lean` — the two poles as the two folds' non-values (1 PURE)
  - `lean/E213/Lib/Math/MaxEntropy.lean` — structurelessness as a positive property (8 PURE)
- Canon: `seed/AXIOM/06_lens_readings.md` §6.5, §6.6, §6.9.
- ∅-axiom status: 0 DIRTY across all files.

## Narrative

### 0 = ∞ is one hole, not two dual values

The reciprocal fold `x ↦ 1/x` returns a value for every nonzero integer-with-inverse except one
point.  Inside the values that point is `0` — the unique `q` with no multiplicative inverse,
`zero_no_reciprocal : q · 0 ≠ 1` (`ZeroInfinityHole`).  Through the reciprocal the same point is `∞`
(`1/0`).  There is no second object: the reciprocal *failure* at `0` is what "`∞`" names.  So "`0` is
like `∞`" is exact, and "not dual" is exact — duality needs two objects, and this is one.  Canon §6.5
states it at the root: before any Lens, a point (the minimal pointable) and the infinite K_∞ are
*literally the same object*.  `0` (a point, the additive null) and `∞` are that one structureless
residue.

### Status-symmetry: a correctness condition on folds (§6.9)

Canon §6.6 — without external before/after, *state and state-transition are not separable*.  A
"value" is a state; "a limit transitioned toward but not reached" is a state-transition.  Hence a fold
that treats `0` as a value while treating `∞` as a not-yet-reached state imports exactly the
before/after §6.6 forbids.  The corrected rule (§6.9): **within one fold, `0` and `∞` must carry the
same status** — both genuine carrier elements, or both absent.  Using `0` as a value commits one to
`∞` (the reciprocal `1/0`); the two cannot be taken by halves.  And "`0` as a value" is already a
cross-layer move: in the difference-Lens completion `0` is the entire diagonal class `{(n, n)}`,
infinitely many prim-distinct Raws identified — reading that as a *stratum value* folds a degenerate
sub-view in.  `0`/`∞` are never single-stratum values; they are the residue every stratum points at.

### ℤ's two correct fold forms

`ℤ` is the difference-Lens readout (§6.7); its own fold is negation `x ↦ −x`.  Plain `ℤ` has `0` but
no `∞` — negation's only fixed point is `0`, the `∞`-direction an unreached limit: the torsioned
form.  There are exactly two status-symmetric closures (`IntFoldForms`):

  - **One-point** `ℤ̂ = Option Int`, `∞ = −∞`.  `negHat` is an involution (`negHat_involutive`) whose
    fixed points are *exactly* `{0, ∞}` (`negHat_fixed_iff`) — both fixed.  The discrete projective
    line.
  - **Two-point** `ℤ̄ = IntBar`, `+∞ ≠ −∞`.  `negBar` fixes only `0` and **swaps** `±∞`
    (`negBar_fixed_iff`, `negBar_zero_fixed_inf_swapped`) — the `∞`-pair a negation 2-cycle.  The
    discrete extended line.

In both, `∞` is a genuine carrier element of the same status as `0`, curing the torsion; and the
genuine integers `n ≠ 0` are proper negation 2-cycles `{n, −n}` (`negHat_value_two_cycle`).  `0`/`∞`
are the fold's symmetry centres, not values in the sense the nonzero integers are.

### The two folds are mirror images

On the shared four-point fixture `Q4 = {∞, 0, +1, −1}` (the reciprocal-closed core of `ℤ̂`), both
founding folds are total involutions and exact mirrors (`FoldDuality`):

  - **negation** `negQ` **fixes** the hole pair `{0, ∞}` (`negQ_fixes_zeroInf`) and **swaps** the
    units `{±1}` (`negQ_swaps_units`);
  - **reciprocal** `recQ` **swaps** `{0, ∞}` (`recQ_swaps_zeroInf`) and **fixes** `{±1}`
    (`recQ_fixes_units`).

Each ℤ/2 fold fixes the orbit the other swaps (`two_folds_dual_on_pairs`).  This is the sharpest form
of "`0` is to `+` as `1` is to `×`": the additive fold's fixed pair is the multiplicative fold's
swapped pair, and conversely.

### The Klein four-group, and the antipode is the founding swap

The two folds commute (`negQ_recQ_comm`) and their composite `bothSwap = negQ ∘ recQ`
(`FoldKlein`) is the third non-identity involution: it **swaps both** orbits (`bothSwap_swaps_both`)
and is therefore **fixed-point-free** (`bothSwap_no_fixed`).  Together with the identity,
`{id, negQ, recQ, bothSwap}` is the Klein four-group `ℤ/2 × ℤ/2` (`klein_four_group`), and the three
non-identity elements are completely classified by which orbit they fix: `negQ` the hole pair, `recQ`
the units, `bothSwap` neither (`klein_fixed_orbit_profile`).

Across frames, `bothSwap` is the negative reciprocal `x ↦ −1/x`: on the fixture `∞ ↦ 0`, `0 ↦ ∞`,
`+1 ↦ −1`, `−1 ↦ +1`.  That is precisely the Möbius action of `S = [[0, −1], [1, 0]] = comp 0 1 =
Mat2.S` — the **founding elliptic swap**, the elliptic floor of the discriminant dial
(`EllipticPeriodicTier.comp_eq_S`, `FoundingDynamicBridge.founding_swap_is_elliptic_floor`, `S² =
−I`).  So the antipode of the §6.9 Klein group is the static invert-swap of the number-tower
founding, and its matrix order `4` (`periodic_elliptic_S`) halves to projective order `2` exactly
because `S² = −I` acts trivially on the projective fixture.  The §6.9 fold structure and the elliptic
dial are one structure, joined at this swap.

### The same residue is the maximum-entropy ceiling

The `0`/`∞` residue resurfaces one fold over, at the top.  Read on the Casoratian (the discrete
Wronskian, ratio the determinant `q`), the `det`-spectrum has a non-value at each end
(`DetSpectrumPoles.det_spectrum_poles_and_center`):

  - `q = 0` — the Casoratian collapses to `0` (`cas_zero_collapses`): the multiplicative-fold hole,
    the value-image of `0`/`∞`;
  - `q = −1` — the Casoratian is `MaxEntropy` (no finite difference-depth, `MaxEntropy.golden_cassini_maxEntropy`):
    the additive-fold ceiling, the non-surjection (`CeilingSchema.ceilings_are_nonsurjectivity`);
  - `q = +1` — the doubly-finite centre: never `0` and `polyDepthZ 0`.

So the bottom (`0`/`∞`, multiplicative hole) and the top (maximum entropy, additive ceiling) are not
two unrelated boundaries: they are the one structureless residue read through the two folds.
"Floor", "ceiling", "boundary" are Lens-cut artifacts (§5.1) — there is only the residue and the
strata that point at it.  Maximum entropy is the residue named positively (incompressibility,
measure-free) rather than as a privation (`MaxEntropy.maxEntropy_not_surjective`).

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `zero_no_reciprocal` | `ZeroInfinityHole` | `q · 0 ≠ 1` — `0` is the unique reciprocal hole (the value-side `∞`) |
| `self_reciprocal_iff_unit` | `ZeroInfinityHole` | `q·q = 1 ↔ q = ±1` — reciprocal-fixed core is the units |
| `negHat_fixed_iff` | `IntFoldForms` | one-point fold fixes exactly `{0, ∞}` |
| `negBar_fixed_iff` | `IntFoldForms` | two-point fold fixes only `0`; `±∞` a 2-cycle |
| `int_correct_fold_forms` | `IntFoldForms` | the two status-symmetric closures of ℤ's negation |
| `two_folds_dual_on_pairs` | `FoldDuality` | negation fixes `{0,∞}`/swaps `{±1}`; reciprocal the mirror |
| `klein_four_group` | `FoldKlein` | the two folds generate `ℤ/2 × ℤ/2` |
| `klein_fixed_orbit_profile` | `FoldKlein` | the three folds classified by fixed orbit (hole / unit / none) |
| `det_spectrum_poles_and_center` | `DetSpectrumPoles` | hole at `q=0`, ceiling at `q=−1`, centre at `q=+1` |
| `maxEntropy_not_surjective` | `MaxEntropy` | structurelessness as a positive non-surjection |

## Research-note provenance

Narrative-from-scratch — no per-file research notes.  The conceptual course-correction that produced
canon §6.9 (status-symmetry; `0`/`∞` never a stratum-value) is recorded in §6.9 itself and the
CLAUDE.md failure-modes catalog ("0/∞ as a stratum-value (mixed-status fold)").

## Open frontier

- The multiplicative fold is formalized on the reciprocal-closed core `Q4`; its full one-point
  carrier is the projective rationals `ℚ̂` (the `NatPairToQPos` reciprocal extended with `0`/`∞`),
  not yet built end to end.
- π remains the elliptic irrational-rotation pole — the `det = +1` face at an angle with no finite
  order — and its continued-fraction non-holonomicity is the standing open boundary
  (`theory/math/analysis/phi_pi_poles.md`).

## How to verify

```bash
cd lean && lake build E213.Lens.Number E213.Lib.Math.MaxEntropy E213.Lib.Math.DetSpectrumPoles
python3 tools/scan_axioms.py E213.Lens.Number.IntFoldForms
python3 tools/scan_axioms.py E213.Lens.Number.FoldDuality
python3 tools/scan_axioms.py E213.Lens.Number.FoldKlein
python3 tools/scan_axioms.py E213.Lib.Math.Cauchy.ZeroInfinityHole
```
