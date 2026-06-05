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

end E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount
