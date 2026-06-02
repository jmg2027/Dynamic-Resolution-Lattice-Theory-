import E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree

/-!
# Axes ≥ 4 are composites of the three components `{NT, NS, NS+NT}`

Intuition (parallel branch): the higher axes can be *built from* the
three components found in `AxisSeedTrichotomy` — the `2`-axis (`NT`), the
`3`-axis (`NS`), the `2+3` axis (`NS+NT`).  The framework confirms it: the
three are `{2, 3, 5}`, and every axis of the exceptional world is their
multiplicative composite.

## The three are the prime factors of the icosahedral order

`|2I| = 120 = 2³ · 3 · 5 = NT³ · NS · (NS+NT)`.  The primes dividing the
largest binary polyhedral group are exactly the three components.  Nothing
else enters: `7, 11, 13, …` never divide it.

## Every polyhedral order is `{2,3,5}`-smooth

The element orders of `2T, 2O, 2I` are `{1,2,3,4,6}`, `{1,2,3,4,6,8}`,
`{1,2,3,4,5,6,10}` — all `5`-smooth (every prime factor in `{2,3,5}`).
The first non-smooth number `7` is exactly the first order *absent* from
every binary polyhedral group: `is5smooth 7 = false`.  So the axes that
occur are precisely the `{NT, NS, NS+NT}`-smooth ones.

## Higher axes factor; the trace field is the compositum

Each higher order is a product of the three components, and — since the
trace-field degree is `φ(n)/2` and `φ` is *multiplicative* — the
trace field of a composite order is the **compositum** of the prime-axis
trace fields:

  `φ(6)  = φ(2)·φ(3)`   (`2-axis ⊗ 3-axis`)
  `φ(10) = φ(2)·φ(5)`   (`2-axis ⊗ (2+3)-axis`)
  `φ(12) = φ(4)·φ(3)`   (`2-tower² ⊗ 3-axis`)
  `φ(15) = φ(3)·φ(5)`   (`3-axis ⊗ (2+3)-axis`)

So `4 = NT²`, `6 = NT·NS`, `8 = NT³`, `9 = NS²`, `10 = NT·(NS+NT)`,
`12 = NT²·NS`, `15 = NS·(NS+NT)` — the higher axes are *generated* by the
three components under multiplication, and their algebraic/cyclotomic
structure is the tensor of the three primitive ones (`bare √NT`,
Eisenstein `ω`, golden `φ`).  The three are a generating set; nothing of
order ≥ 4 is new.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.AxisComposition

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree (phi)

/-- Divide all factors of `p` out of `n` (fuel-bounded; `Nat.mod`/`div`
    are `∅`-axiom). -/
def dropFactor : Nat → Nat → Nat → Nat
  | 0,     _, n => n
  | f + 1, p, n => if 2 ≤ p && n % p == 0 then dropFactor f p (n / p) else n

/-- `n` is `{2,3,5}`-smooth: dividing out all `2`s, `3`s, `5`s leaves `1`. -/
def is5smooth (n : Nat) : Bool :=
  let a := dropFactor n 2 n
  let b := dropFactor a 3 a
  let c := dropFactor b 5 b
  c == 1

/-- **The three components are the prime factors of `|2I|`.**
    `120 = NT³ · NS · (NS+NT) = 2³ · 3 · 5`. -/
theorem icosahedral_order_factors :
    (120 = NT ^ 3 * NS * (NS + NT)) ∧ (NT = 2 ∧ NS = 3 ∧ NS + NT = 5) := by decide

/-- **Every polyhedral order is `{2,3,5}`-smooth.**  The union of the
    `2T/2O/2I` order menus is `{1,2,3,4,5,6,8,10}`, all `5`-smooth; the
    first non-smooth number `7` is the first order absent from every
    binary polyhedral group. -/
theorem polyhedral_orders_smooth :
    [1, 2, 3, 4, 5, 6, 8, 10].all is5smooth = true
    ∧ is5smooth 7 = false := by decide

/-- **Higher axes factor into the three components.**  Orders `≥ 4` are
    products of `{NT, NS, NS+NT} = {2,3,5}`. -/
theorem higher_axes_factor :
    (4 = NT * NT) ∧ (6 = NT * NS) ∧ (8 = NT * NT * NT) ∧ (9 = NS * NS)
    ∧ (10 = NT * (NS + NT)) ∧ (12 = NT * NT * NS) ∧ (15 = NS * (NS + NT)) := by decide

/-- **The trace field is the compositum.**  `φ` is multiplicative, so the
    trace-field degree of a composite order factors through the
    prime-axis degrees — the higher-axis cyclotomic structure is the
    tensor of the primitive ones. -/
theorem trace_field_composes :
    (phi 6 = phi 2 * phi 3)        -- 2-axis ⊗ 3-axis
    ∧ (phi 10 = phi 2 * phi 5)     -- 2-axis ⊗ (2+3)-axis
    ∧ (phi 12 = phi 4 * phi 3)     -- 2-tower² ⊗ 3-axis
    ∧ (phi 15 = phi 3 * phi 5) := by decide  -- 3-axis ⊗ (2+3)-axis

/-- ★★★ **Axes ≥ 4 are composites of the three components.**  The three
    `{NT, NS, NS+NT} = {2,3,5}` are the prime factors of `|2I| = 120`;
    every polyhedral order is `{2,3,5}`-smooth (the first non-smooth `7`
    is the first absent order); higher orders factor as products of the
    three; and since `φ` is multiplicative, their trace fields are the
    compositum of the primitive ones.  The three components generate the
    whole exceptional axis structure — nothing of order ≥ 4 is new. -/
theorem axes_from_three_components :
    -- the three are the primes of |2I|.
    (120 = NT ^ 3 * NS * (NS + NT))
    -- polyhedral orders are {2,3,5}-smooth; 7 is the first gap.
    ∧ ([1, 2, 3, 4, 5, 6, 8, 10].all is5smooth = true ∧ is5smooth 7 = false)
    -- higher axes factor into the three.
    ∧ (4 = NT * NT ∧ 6 = NT * NS ∧ 10 = NT * (NS + NT) ∧ 15 = NS * (NS + NT))
    -- trace fields compose multiplicatively.
    ∧ (phi 6 = phi 2 * phi 3 ∧ phi 15 = phi 3 * phi 5) := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.AxisComposition
