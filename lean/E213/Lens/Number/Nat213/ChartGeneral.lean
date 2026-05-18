import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Nat213.ChartGeneral — chart-parameterised Method A chain (Option D)

Per `research-notes/2026-05-18_lens_emergence_path.md` §5 Option D.
The existing `Nat213.Raw.numeral / succ` hardcodes the chart choice
`(Raw.a, Raw.b)`.  This file exposes the *general* chart: any pair
`(r₀, r')` of distinct Raws can serve as the chain seeds.

The default chart `(Raw.a, Raw.b)` specialises `chartChain` back to
`Raw.numeral`, so this file is purely additive (no existing
definition is modified).

**Scope.**  Parameterised definition + the default-chart
specialisation theorem.  A full chart-invariance theorem — for
instance `value (chartChain r₀ r' h n) = value r₀ + n * value r'` —
requires a generalised `≠ r'` chain invariant whose proof depends
on properties of `r'` (atomicity, leaves count, ...).  Deferred.

∅-axiom standard; no Mathlib / Classical / propext / Quot.sound /
omega.
-/

namespace E213.Lens.Number.Nat213

open E213.Theory E213.Theory.Raw.Endomorphic

/-- The general Method A chain from two distinct Raws.
    `chartChain r₀ r' _ 0 = r₀`; each successor wraps in `r'` via
    `slashOrSelf`.  When `slashOrSelf` sees the inner element equal
    to `r'` (chain collapse), it returns the inner element
    unchanged — the chain stops growing.  Whether this collapse
    occurs depends on the choice of `(r₀, r')`; for the default
    `(Raw.a, Raw.b)` the existing `Raw.numeral_ne_b` invariant
    prevents it. -/
def chartChain (r₀ r' : Raw) (_h : r₀ ≠ r') : Nat → Raw
  | 0     => r₀
  | n + 1 => slashOrSelf (chartChain r₀ r' _h n) r'

theorem chartChain_zero (r₀ r' : Raw) (h : r₀ ≠ r') :
    chartChain r₀ r' h 0 = r₀ := rfl

theorem chartChain_succ (r₀ r' : Raw) (h : r₀ ≠ r') (n : Nat) :
    chartChain r₀ r' h (n + 1)
      = slashOrSelf (chartChain r₀ r' h n) r' := rfl

/-- The default chart `(Raw.a, Raw.b)` reproduces `Raw.numeral`. -/
theorem chartChain_default (n : Nat) :
    chartChain Raw.a Raw.b (by decide) n = Raw.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show slashOrSelf (chartChain Raw.a Raw.b _ k) Raw.b
        = Raw.numeral (k + 1)
      rw [ih]
      rfl

end E213.Lens.Number.Nat213
