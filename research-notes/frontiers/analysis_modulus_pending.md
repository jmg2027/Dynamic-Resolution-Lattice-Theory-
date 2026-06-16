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
