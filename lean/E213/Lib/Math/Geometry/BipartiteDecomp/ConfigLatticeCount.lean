/-!
# Configuration-lattice count of the generative cycle (∅-axiom)

The slash-cycle (each line → a point, each new point joins all not-yet-connected
points) is a confluent concurrent process; its reachable intermediate
configurations are the order ideals of the cycle's operation dependency poset
`P(V,s)` (Birkhoff), a finite distributive lattice — the configuration domain of
the corresponding (conflict-free) Winskel event structure.  `V` = vertices at
cycle start, `s` = new points spawned this cycle (= edges created in the previous
cycle).

The poset `P(V,s)` has height 2: `s` minimal creations `A_i`; for each `i`, `V`
private connection atoms (cover `A_i` only); and `C(s,2)` cross atoms (each covers
two creations `A_i, A_j`).  Counting order ideals by the set `S ⊆ {A_i}` that is
"in" (|S|=k) gives the closed form

    I(V,s) = Σ_{k=0}^{s}  C(s,k) · 2^{V·k} · 2^{C(k,2)} .

Verified here: cycle 1 = `I(2,1) = 5`, cycle 2 = `I(3,2) = 145`, cycle 3 =
`I(5,7) = 72 304 608 555 084 001` (the term the prior notes left as "vast").
Dominant term `k=s`: `I(V,s) ~ 2^{sV + C(s,2)}` = `2^(edges added this cycle)`.

All declarations PURE (∅-axiom), proved by `decide` on concrete `Nat` arithmetic.
-/

namespace E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount

/-- Pascal binomial (no Mathlib). -/
def binom : Nat → Nat → Nat
  | _,     0      => 1
  | 0,     _ + 1  => 0
  | n + 1, k + 1  => binom n k + binom n (k + 1)

/-- Order-ideal count of the cycle's operation poset `P(V,s)`:
    `Σ_{k=0}^{s} C(s,k) · 2^{V·k} · 2^{C(k,2)}`. -/
def cfgIdeals (V s : Nat) : Nat :=
  (List.range (s + 1)).foldr
    (fun k acc => acc + binom s k * 2 ^ (V * k) * 2 ^ (k * (k - 1) / 2)) 0

/-- ★ Cycle 1: `I(2,1) = 5` (the 5-state lattice). -/
theorem cycle1 : cfgIdeals 2 1 = 5 := by decide

/-- ★ Cycle 2: `I(3,2) = 145`. -/
theorem cycle2 : cfgIdeals 3 2 = 145 := by decide

/-- ★★ Cycle 3: `I(5,7) = 72 304 608 555 084 001` — the previously-uncomputed
    "vast" term, now exact. -/
theorem cycle3 : cfgIdeals 5 7 = 72304608555084001 := by decide

/-- ★ The dominant (`k = s`) term is `2^{sV + C(s,2)}` = `2^(edges added this
    cycle)`; concretely at cycle 3 the top term is `2^56`. -/
theorem dominant_term_cycle3 :
    binom 7 7 * 2 ^ (5 * 7) * 2 ^ (7 * 6 / 2) = 2 ^ 56 := by decide

/-- ★★★ Master: the configuration-lattice (order-ideal) counts of the first three
    cycles of the slash-generative process. -/
theorem config_lattice_count_master :
    cfgIdeals 2 1 = 5
    ∧ cfgIdeals 3 2 = 145
    ∧ cfgIdeals 5 7 = 72304608555084001 := by decide

/-- ★ Empty cycle (`s = 0`): exactly one configuration (the empty graph), for
    every `V` — a parametric `∅`-axiom identity (the lattice bottom). -/
theorem cfgIdeals_zero (V : Nat) : cfgIdeals V 0 = 1 := rfl

/-- ★ One growth axis (`s = 1`, parametric in `V`): `I(V,1) = 2^V + 1` — the
    cycle-1 lattice for `V` pre-existing vertices (matches `cycle1` at `V = 2`).
    Proved `∅`-axiom via the PURE `Nat` lemmas (no `propext`). -/
theorem cfgIdeals_one (V : Nat) : cfgIdeals V 1 = 2 ^ V + 1 := by
  show (0 + 1 * 2 ^ (V * 1) * 1) + 1 = 2 ^ V + 1
  rw [Nat.mul_one V, Nat.one_mul, Nat.mul_one, Nat.zero_add]

/-- ★ Two growth axes (`s = 2`, parametric in `V`): `I(V,2) = 2^{2V}·2 +
    2·2^V + 1` (cross-term `C(2,2)=1` doubles the top piece).  Matches
    `cycle2` (= 145) at `V = 3`.  PURE. -/
theorem cfgIdeals_two (V : Nat) :
    cfgIdeals V 2 = 2 ^ (V * 2) * 2 + 2 * 2 ^ (V * 1) + 1 := by
  show ((0 + 1 * 2 ^ (V * 2) * 2) + 2 * 2 ^ (V * 1) * 1) + 1
        = 2 ^ (V * 2) * 2 + 2 * 2 ^ (V * 1) + 1
  rw [Nat.zero_add, Nat.one_mul, Nat.mul_one]

/-- ★ Three growth axes (`s = 3`, parametric in `V`): `I(V,3) = 2^{3V}·8 +
    3·2^{2V}·2 + 3·2^V + 1` (the `k=3` cross-term carries `2^{C(3,2)} = 2^3 = 8`).
    PURE. -/
theorem cfgIdeals_three (V : Nat) :
    cfgIdeals V 3 = 2 ^ (V * 3) * 8 + 3 * 2 ^ (V * 2) * 2 + 3 * 2 ^ (V * 1) + 1 := by
  show ((((0 + 1 * 2 ^ (V * 3) * 8) + 3 * 2 ^ (V * 2) * 2) + 3 * 2 ^ (V * 1) * 1) + 1)
        = 2 ^ (V * 3) * 8 + 3 * 2 ^ (V * 2) * 2 + 3 * 2 ^ (V * 1) + 1
  rw [Nat.zero_add, Nat.one_mul, Nat.mul_one]

end E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount
