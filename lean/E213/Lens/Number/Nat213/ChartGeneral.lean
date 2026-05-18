import E213.Lens.Number.Nat213.Raw
import E213.Meta.Tactic.NatHelper

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

/-! ### Chart-chain injectivity in `n` (added 2026-05-18)

`chartChain r₀ r' h n = chartChain r₀ r' h m → n = m`: each chain
step adds `value r' ≥ 1` to the running `value`, so distinct `n`
yield distinct `value`s, which forces distinct Raws. -/

open E213.Term.Internal (Tree)

/-- Every Raw has positive `value` (leaves ≥ 1). -/
theorem value_pos (r : Raw) : 1 ≤ Raw.value r := by
  show 1 ≤ Raw.fold 1 1 (· + ·) r
  rw [Raw.fold_eq_leaves r]
  exact Tree.leaves_pos r.val

/-- **Chart-chain value injectivity**: chains with distinct indices
    have distinct `value`s.  Uses the 213-native
    `Meta.Tactic.NatHelper.mul_left_cancel_pos` to avoid the
    propext-tainted core `Nat.eq_of_mul_eq_mul_left`. -/
theorem chartChain_value_injective (r₀ r' : Raw) (h : r₀ ≠ r')
    {n m : Nat}
    (heq : Raw.value (chartChain r₀ r' h n)
            = Raw.value (chartChain r₀ r' h m)) :
    n = m := by
  rw [chartChain_value r₀ r' h n, chartChain_value r₀ r' h m] at heq
  have hcanc : n * Raw.value r' = m * Raw.value r' :=
    E213.Tactic.NatHelper.add_left_cancel heq
  have hpos : 0 < Raw.value r' := value_pos r'
  -- `mul_left_cancel_pos` wants `c * a = c * b`; commute first.
  have hcanc' : Raw.value r' * n = Raw.value r' * m := by
    rw [Nat.mul_comm (Raw.value r') n, Nat.mul_comm (Raw.value r') m]
    exact hcanc
  exact E213.Tactic.NatHelper.mul_left_cancel_pos hpos hcanc'

/-- **Chart-chain injectivity**: the chain function `n ↦ chartChain
    r₀ r' h n` is injective.  Direct corollary of the value-level
    statement. -/
theorem chartChain_injective (r₀ r' : Raw) (h : r₀ ≠ r')
    {n m : Nat}
    (heq : chartChain r₀ r' h n = chartChain r₀ r' h m) :
    n = m :=
  chartChain_value_injective r₀ r' h (congrArg Raw.value heq)

/-! ### Residue invariant along the chart-chain (added 2026-05-18)

`chartChain r₀ r' h n` has `value` congruent to `value r₀` modulo
`value r'`.  In other words, the entire arithmetic progression
`value r₀, value r₀ + value r', value r₀ + 2·value r', …` lies in
one residue class mod `value r'`.  This is the chart-relativity
*residue invariant*: the chart `(r₀, r')` partitions `Nat` into
classes mod `value r'`, and the chain walks within a single class. -/

/-- **Residue invariant**: every chart-chain element has the same
    residue as `r₀` modulo `value r'`.  Direct consequence of
    `chartChain_value` + `Tactic.NatHelper.add_mul_mod_self_pure`. -/
theorem chartChain_value_mod (r₀ r' : Raw) (h : r₀ ≠ r') (n : Nat) :
    Raw.value (chartChain r₀ r' h n) % Raw.value r'
      = Raw.value r₀ % Raw.value r' := by
  rw [chartChain_value r₀ r' h n]
  exact E213.Tactic.NatHelper.add_mul_mod_self_pure
    (Raw.value r₀) (Raw.value r') n

/-- **Chart-chain value lower bound**: every chart-chain element has
    `value ≥ value r₀`.  The chain only grows from its seed. -/
theorem chartChain_value_ge (r₀ r' : Raw) (h : r₀ ≠ r') (n : Nat) :
    Raw.value r₀ ≤ Raw.value (chartChain r₀ r' h n) := by
  rw [chartChain_value r₀ r' h n]
  exact Nat.le_add_right (Raw.value r₀) (n * Raw.value r')

/-- **Chart-chain monotonicity**: the value sequence is non-decreasing
    along the chain. -/
theorem chartChain_value_mono (r₀ r' : Raw) (h : r₀ ≠ r') {n m : Nat}
    (hnm : n ≤ m) :
    Raw.value (chartChain r₀ r' h n)
      ≤ Raw.value (chartChain r₀ r' h m) := by
  rw [chartChain_value r₀ r' h n, chartChain_value r₀ r' h m]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (Raw.value r') hnm) _

/-- **Chart-chain strict monotonicity**: distinct chain indices give
    strictly increasing values.  Uses `value_pos` (every Raw has
    ≥ 1 leaves) to ensure the chain step adds positive content. -/
theorem chartChain_value_strict_mono (r₀ r' : Raw) (h : r₀ ≠ r') {n m : Nat}
    (hnm : n < m) :
    Raw.value (chartChain r₀ r' h n)
      < Raw.value (chartChain r₀ r' h m) := by
  rw [chartChain_value r₀ r' h n, chartChain_value r₀ r' h m]
  apply Nat.add_lt_add_left
  have hpos : 0 < Raw.value r' := value_pos r'
  have h1 : n + 1 ≤ m := Nat.succ_le_of_lt hnm
  have h2 : (n + 1) * Raw.value r' ≤ m * Raw.value r' :=
    Nat.mul_le_mul_right (Raw.value r') h1
  have h3 : n * Raw.value r' < n * Raw.value r' + Raw.value r' :=
    Nat.lt_add_of_pos_right hpos
  have h4 : n * Raw.value r' + Raw.value r' = (n + 1) * Raw.value r' := by
    rw [Nat.succ_mul]
  rw [h4] at h3
  exact Nat.lt_of_lt_of_le h3 h2

end E213.Lens.Number.Nat213
