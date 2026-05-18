import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Nat213.ChartGeneral — chart-parameterised Method A chain (Option D)

Per `research-notes/2026-05-18_lens_emergence_path.md` §5 Option D.
The existing `Nat213.Raw.numeral` hardcodes the chart `(Raw.a, Raw.b)`.
This file exposes the *general* chart: any two distinct Raws can
serve as chain seeds, and `value` grows linearly along the chain.

Results:
  - `chartChain r₀ r' h : Nat → Raw` — parameterised Method A chain
  - `chartChain_default` — the `(Raw.a, Raw.b)` chart recovers `Raw.numeral`
  - `chartChain_ne` — the chain never collapses onto `r'`
  - `chartChain_value` — `value (chartChain r₀ r' h n) = value r₀ + n * value r'`

∅-axiom standard; no Mathlib / Classical / propext / Quot.sound /
omega / native_decide.
-/

namespace E213.Lens.Number.Nat213

open E213.Theory E213.Theory.Raw.Endomorphic
open E213.Term.Internal (Tree)

/-- The general Method A chain from two distinct Raws.
    `chartChain r₀ r' _ 0 = r₀`; each successor wraps in `r'` via
    `slashOrSelf`. -/
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

/-! ### Chain non-collapse — needed for chart-invariance

`Raw.slash_ne_right` (now in `Theory.Raw.Slash`) gives
`Raw.slash x y h ≠ y` for any `(x, y, h)`.  Combined with
`slashOrSelf_of_ne`, this yields `chartChain r₀ r' h n ≠ r'` for
every `n`. -/

/-- The chart-parameterised chain never lands on `r'` — chain
    non-collapse.  Generalises `Raw.numeral_ne_b` to arbitrary
    `(r₀, r')`. -/
theorem chartChain_ne (r₀ r' : Raw) (h : r₀ ≠ r') (n : Nat) :
    chartChain r₀ r' h n ≠ r' := by
  induction n with
  | zero => exact h
  | succ k ih =>
      show slashOrSelf (chartChain r₀ r' h k) r' ≠ r'
      rw [slashOrSelf_of_ne ih]
      exact E213.Theory.Raw.slash_ne_right _ _ ih

/-! ### Chart-invariance theorem — `value` is linear along the chain -/

/-- **Chart-invariance**: along any chart `(r₀, r')` with `r₀ ≠ r'`,
    the leaves count of `chartChain r₀ r' h n` is `value r₀ + n *
    value r'`.  Proof: induction on `n`, using `chartChain_ne` to
    expand `slashOrSelf` to `Raw.slash`, then `Raw.fold_slash` to
    decompose `value`. -/
theorem chartChain_value (r₀ r' : Raw) (h : r₀ ≠ r') (n : Nat) :
    Raw.value (chartChain r₀ r' h n) = Raw.value r₀ + n * Raw.value r' := by
  induction n with
  | zero =>
      show Raw.value r₀ = Raw.value r₀ + 0 * Raw.value r'
      rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
      show Raw.value (slashOrSelf (chartChain r₀ r' h k) r')
        = Raw.value r₀ + (k + 1) * Raw.value r'
      rw [slashOrSelf_of_ne (chartChain_ne r₀ r' h k)]
      show Raw.value (E213.Theory.Raw.slash (chartChain r₀ r' h k) r'
                        (chartChain_ne r₀ r' h k))
        = Raw.value r₀ + (k + 1) * Raw.value r'
      unfold Raw.value
      rw [E213.Theory.Raw.fold_slash 1 1 (· + ·)
            (fun u v => Nat.add_comm u v)
            (chartChain r₀ r' h k) r' (chartChain_ne r₀ r' h k)]
      show Raw.value (chartChain r₀ r' h k) + Raw.value r'
        = Raw.value r₀ + (k + 1) * Raw.value r'
      rw [ih, Nat.succ_mul]
      -- goal: Raw.value r₀ + k * Raw.value r' + Raw.value r' = Raw.value r₀ + (k * Raw.value r' + Raw.value r')
      rw [Nat.add_assoc]

end E213.Lens.Number.Nat213
