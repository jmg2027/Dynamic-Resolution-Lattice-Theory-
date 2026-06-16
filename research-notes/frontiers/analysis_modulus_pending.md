# Frontier: pending computed-modulus analysis theorems

Clean Tier-C "force the modulus" targets in the style of `Analysis/ExtremeValue`,
`BanachFixedPoint`, `RiemannContinuous` (all closed). Attempted but not yet
landed — the obstruction is propext-clean pure-`Nat` arithmetic for the
inequality bookkeeping (no division in statements), which is fiddlier than the
metric-`close` telescoping the landed cases used.

- **Cesàro mean** — `a → L` with modulus `r` ⟹ the averages `(Σ_{k<n} a k)/n → L`
  with a computed averaging modulus `≈ E·2^m` (`E` = early-term spread). State the
  "average within `1/2^m`" as a multiplied-out `Nat` inequality (`2^m·|P n − n·L|
  < n`) to avoid real division. Reuse `MetricModulus`/`distMet`.
- **Limit arithmetic** — sum/product of two modulus-convergent sequences is
  modulus-convergent (the new modulus computed: `Ω m = max(r₁(m+1), r₂(m+1))` for
  the sum). Clean, reuses `MetricModulus.ctri`.
- **Squeeze/sandwich** with modulus.

Recommendation: do these directly (not via a dispatched agent) — the difficulty is
purely the `Nat`-inequality propext-avoidance, which is better handled
interactively with `NatHelper`/`PureNat` twins than in a one-shot prompt.
