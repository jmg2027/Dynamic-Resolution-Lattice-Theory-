# The unit `1` — the residue's single distinguishing, read everywhere

In 213 the unit `1` is **one value, not one operator**: the single self-distinguishing step of
the residue, read through different Lenses as the ascent-rung, the descent-drop, the determinant,
the off-diagonal glue, the carry, the Cassini sign, and the reciprocal.  The honest unification is
*downward* — identity of the value — never an operator that unifies the readings.

## 213-native answer

The unit is the count-Lens reading of one distinguishing.  Its canonical pinning is
`Lens/Number/SharedUnitAcrossReadings.the_unit_is_one_across_readings`: the count-difference glue
`NS − NT = 1` (`Mobius213OneAsGlue.ns_minus_nt_is_one`), the Möbius/ratio determinant
`det P = NS − NT = 1` (`mobius_det_eq_ns_minus_nt`, `mobius_det_is_unit`), the Cassini oscillation
`det(toggle) = 1` (`CassiniUnimodular.toggle_det_unit`), and the reciprocal `x·(1/x) = 1`
(`NatPairToQPos.qpair_mul_swap_eq_qOne`) — four readings, one value.

## Derivation

The unit is not confined to the algebra.  `SharedUnitAcrossReadings.unit_bridges_dynamics_and_readings`
carries the *same* `1` into the residue's **dynamics**: the ascent climbs by it
(`MuNuMirror.ascent_adds_unit`: `(rawTower (n+1)).depth = (rawTower n).depth + 1`), the descent
drops by it (`Lambek.part_depth_succ_le`: `IsPart c p → c.depth + 1 ≤ p.depth`), and these are
byte-identical to the glue and the determinant.  `Cauchy/ReentryUnit.reentry_unit_across_scales`
closes the convergent/escaping split onto the same `Nat` successor (`peel_overflow_is_unit`):
well-foundedness distinguishes the *direction*, not the unit.

The same `1` is the **carry**.  The odometer starts at it (`Theory/Raw/Odometer.carry_zero`) and
generates a free `ℤ`-action with it (`Odometer.odo_unit_action`); in the residue's own Fibonacci
base the carry `011 → 100` *is* the unit lifting one spiral rung
(`Real213/ZeckendorfCarry.zeck_carry_weight`: `fib(i+2) + fib(i+3) = fib(i+4)`, ground case
`1 + 2 = 3`).  And it is the **Cassini** `W = ±1` (`FibCassiniNat.fib_cassini_norm`): the gap
between frozen and dynamic φ that the convergent never closes
(`theory/math/algebra/phi_self_similarity.md` §3.6) is exactly this `1`.

## Dual function

This is the classical "unit" with its packaging stripped (`the_form_of_the_residue.md`).  The
multiplicative-and-additive identity, the `SL`-determinant, Fibonacci/Pell unimodularity, the
`+1` successor, the Cassini constant — classically these are distinct facts that *happen* to all
be `1`.  213's reading is sharper: they are not a coincidence of separate `1`s but one value, the
residue's single distinguishing, resolved by different Lenses.  The agreement is the content, not
an accident.

## Cross-frame connections

`NS − NT` (count-difference) = `det P` (Möbius/ratio) = the ascent-rung and the descent-drop (Raw
dynamics) = the binary and golden carry (odometer / Zeckendorf) = Cassini `W` (oscillation) =
`x·(1/x)` (reciprocal) — one value, six resolutions, witnessed together by
`unit_bridges_dynamics_and_readings` + `the_unit_is_one_across_readings`.  Read **additively** the
unit gives counting / growth; read **multiplicatively** it gives the unit orders / rotation — the
same `+1` through a q-Lens, the two meeting at φ (`phi_self_similarity.md`); as a *map* it is the
residue's successor (`the_residue_unit_odometer.md`).

## Open frontier (the honest boundary)

The unit is shared as a **value**; there is no operator monoid unifying the readings.  They live
on different codomains (`α`, `Raw → Bool`, `Int`, the depth `Nat`), and `Tower.PairCompletion` has
no shared carrier — forcing a single common map is the category error
`Lib/Math/Foundations/ResidueForm` names (and `the_form_of_the_residue.md` warns against).  So
"the unit is one" is a downward identity of value, established case-by-case across the readings,
**not** a single upward operation.  The constructive landing is the conjunction term
`unit_bridges_dynamics_and_readings` itself: a ∅-axiom proof that the ascent `+1`, the descent
`+1`, the glue `NS − NT`, and `det P` are the *same* `1`.

## How to verify

```bash
cd lean
lake build E213.Lens.Number.SharedUnitAcrossReadings
python3 tools/scan_axioms.py E213.Lens.Number.SharedUnitAcrossReadings
python3 tools/scan_axioms.py E213.Lib.Math.Analysis.Cauchy.ReentryUnit
```

## One line

> **The unit `1` is the residue's single distinguishing — one value read as ascent, descent, det,
> glue, carry, Cassini, and reciprocal; the agreement is downward (identity of value), not an
> operator that unifies the readings.**
