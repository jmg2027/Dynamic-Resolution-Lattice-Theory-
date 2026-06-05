/-!
# Configuration-lattice count of the generative cycle (∅-axiom)

The slash-cycle (each line → a point, each new point joins all not-yet-connected
points) is a confluent concurrent process; its reachable intermediate
configurations are the order ideals of the cycle's operation dependency poset
`P(V,s)` (Birkhoff), a finite distributive lattice — the configuration domain of
the corresponding (conflict-free) Winskel event structure.  `V` = vertices at
cycle start, `s` = new points spawned this cycle.

The poset `P(V,s)` has height 2; counting order ideals by the set `S ⊆ {creations}`
that is "in" (`|S|=k`) gives the closed form

    I(V,s) = Σ_{k=0}^{s}  C(s,k) · 2^{V·k} · 2^{C(k,2)} .

Here `cfgIdeals` realizes this sum by **structural recursion on the upper index**
(`cfgSum`), so it inducts cleanly (the `List.range`/`foldr` form needs the
propext-tainted `List.range_succ_eq_map` / `List.foldr_append`, blocked under the
∅-axiom standard).  Verified: cycle 1 = `I(2,1) = 5`, cycle 2 = `I(3,2) = 145`,
cycle 3 = `I(5,7) = 72 304 608 555 084 001`.  All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount

/-- Pascal binomial (no Mathlib). -/
def binom : Nat → Nat → Nat
  | _,     0      => 1
  | 0,     _ + 1  => 0
  | n + 1, k + 1  => binom n k + binom n (k + 1)

/-- `binom s 0 = 1` for every `s` (the match is stuck on a variable first arg;
    case-split unsticks it). -/
theorem binom_zero (s : Nat) : binom s 0 = 1 := by cases s <;> rfl

/-- The `k`-th summand `C(s,k) · 2^{V·k} · 2^{C(k,2)}`. -/
def cfgTerm (V s k : Nat) : Nat := binom s k * 2 ^ (V * k) * 2 ^ (k * (k - 1) / 2)

/-- The `k = 0` summand is `1` for every `V, s`. -/
theorem cfgTerm_zero (V s : Nat) : cfgTerm V s 0 = 1 := by
  show binom s 0 * 2 ^ (V * 0) * 2 ^ (0 * (0 - 1) / 2) = 1
  rw [binom_zero, Nat.mul_zero]

/-- Partial sum `Σ_{i=0}^{j} cfgTerm V s i`, by structural recursion on `j`. -/
def cfgSum (V s : Nat) : Nat → Nat
  | 0     => cfgTerm V s 0
  | j + 1 => cfgSum V s j + cfgTerm V s (j + 1)

/-- Order-ideal count of the cycle's operation poset `P(V,s)`: the full sum
    `Σ_{k=0}^{s} C(s,k) · 2^{V·k} · 2^{C(k,2)}`. -/
def cfgIdeals (V s : Nat) : Nat := cfgSum V s s

/-- ★ Cycle 1: `I(2,1) = 5` (the 5-state lattice). -/
theorem cycle1 : cfgIdeals 2 1 = 5 := by decide

/-- ★ Cycle 2: `I(3,2) = 145`. -/
theorem cycle2 : cfgIdeals 3 2 = 145 := by decide

/-- ★★ Cycle 3: `I(5,7) = 72 304 608 555 084 001` — the previously-uncomputed
    "vast" term, now exact. -/
theorem cycle3 : cfgIdeals 5 7 = 72304608555084001 := by decide

/-- ★ The dominant (`k = s`) term is `2^{sV + C(s,2)}`; concretely at cycle 3 the
    top term is `2^56`. -/
theorem dominant_term_cycle3 :
    binom 7 7 * 2 ^ (5 * 7) * 2 ^ (7 * 6 / 2) = 2 ^ 56 := by decide

/-- ★★★ Master: the configuration-lattice (order-ideal) counts of the first three
    cycles of the slash-generative process. -/
theorem config_lattice_count_master :
    cfgIdeals 2 1 = 5
    ∧ cfgIdeals 3 2 = 145
    ∧ cfgIdeals 5 7 = 72304608555084001 := by decide

/-- ★ Empty cycle (`s = 0`): exactly one configuration (the empty graph), for
    every `V` — the lattice bottom. -/
theorem cfgIdeals_zero (V : Nat) : cfgIdeals V 0 = 1 := rfl

/-- ★ One growth axis (`s = 1`, parametric in `V`): `I(V,1) = 2^V + 1` — the
    cycle-1 lattice for `V` pre-existing vertices (matches `cycle1` at `V = 2`). -/
theorem cfgIdeals_one (V : Nat) : cfgIdeals V 1 = 2 ^ V + 1 := by
  show (1 : Nat) + 1 * 2 ^ (V * 1) * 1 = 2 ^ V + 1
  rw [Nat.mul_one V, Nat.one_mul, Nat.mul_one, Nat.add_comm]

/-- `cfgSum V s 0 = 1` (the base summand). -/
theorem cfgSum_zero (V s : Nat) : cfgSum V s 0 = 1 := cfgTerm_zero V s

/-- The partial sum is positive for every upper index (the `k=0` term is `1`). -/
theorem cfgSum_pos (V s j : Nat) : 0 < cfgSum V s j := by
  induction j with
  | zero => rw [cfgSum_zero]; exact Nat.one_pos
  | succ k ih => exact Nat.lt_of_lt_of_le ih (Nat.le_add_right _ _)

/-- ★★ **General positivity** (∀ V s): the configuration lattice is non-empty —
    every cycle has at least one intermediate state (the empty configuration).
    Proved by structural induction on the recursive sum (no `List`/`propext`). -/
theorem cfgIdeals_pos (V s : Nat) : 0 < cfgIdeals V s := cfgSum_pos V s s

end E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount
