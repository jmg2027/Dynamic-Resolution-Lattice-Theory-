# Frontier: pending computed-modulus analysis theorems

Clean Tier-C "force the modulus" targets in the style of `Analysis/ExtremeValue`,
`BanachFixedPoint`, `RiemannContinuous` (all closed). Attempted but not yet
landed — the obstruction is propext-clean pure-`Nat` arithmetic for the
inequality bookkeeping (no division in statements), which is fiddlier than the
metric-`close` telescoping the landed cases used.

- ~~**Cesàro mean**~~ **DONE** — `Analysis/CesaroMean` (16 PURE): averaging
  modulus computed `Nstep m = N + 2^m·E + 1` (`E` = early-term spread), via the
  multiplied-out `Nat` inequality `closeAvg`. (Pure-twin: core `Nat.add_mul` →
  `NatHelper.add_mul` cleared all leaks.)
- **Limit arithmetic** — sum/product of two modulus-convergent sequences is
  modulus-convergent (the new modulus computed: `Ω m = max(r₁(m+1), r₂(m+1))` for
  the sum). Clean, reuses `MetricModulus.ctri`.
- **Squeeze/sandwich** with modulus.

Recommendation: do these directly (not via a dispatched agent) — the difficulty is
purely the `Nat`-inequality propext-avoidance, which is better handled
interactively with `NatHelper`/`PureNat` twins than in a one-shot prompt.

## Update (LA — DONE)

**`Analysis/LimitArithmetic` (12 PURE) landed** — the sum limit law on `distMet`:
`distN_add_le` (additive-compatibility core), `add_converges` (modulus computed
`m ↦ max(ra(m+1), rb(m+1))`), `closeN_add_core`, `const_add_const_converges`,
`shift_converges`. Product DONE (`SqueezeProduct.mul_converges_bounded`, modulus shifted by
bit-length `floorLog 2 K + 1`). Squeeze DONE (`SqueezeProduct.squeeze_converges`).

### (historical) earlier stall note
**Limit arithmetic (sum) on `distMet`** — attempted, did NOT close. The blocker is
the additive-compatibility lemma `distN_add_le : distN (a+u) (b+v) ≤ distN a b +
distN u v` (`distN x y = (x-y)+(y-x)`). The needed sub-fact `(a+u)-(b+v) ≤
(a-b)+(u-v)` is true (`b+(a-b) ≥ a`, `v+(u-v) ≥ u`, then `Nat.sub_le_iff_le_add`)
but every route through it touches propext-dirty truncated-subtraction Iff lemmas.
**Recommendation:** prove `distN_add_le` directly with the pure twins — needs
`a ≤ b + (a-b)` (pure form of `Nat.le_add_sub`) and a pure `sub_le_of_le_add`
(grep `NatHelper`; `closeN_tri` in `UniformLimitContinuous` already does similar
bookkeeping — copy its idiom). Once `distN_add_le` is PURE, `add_converges`
(modulus `max(ra(m+1), rb(m+1))`) follows by the `closeN` halving as in `closeN_tri`.
Two agent one-shots stalled on exactly this lemma; do it interactively.
