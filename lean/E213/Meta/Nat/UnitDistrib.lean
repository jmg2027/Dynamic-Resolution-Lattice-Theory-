import E213.Meta.Nat.UnitGrid

/-!
# UnitDistrib — the bridge law: distributivity, generated

`UnitList` generated the additive monoid (`+`-comm, `+`-assoc) and `UnitGrid`/
`UnitBox` the multiplicative monoid (`×`-comm, `×`-assoc), each as the
count-shadow of a unit-structure double-count, none presupposing the Nat law it
produces. The two operations were generated *in isolation*. This file generates
the **bridge** that couples them — left-distributivity `a·(b+c) = a·b + a·c` —
the same way.

A uniform `a × (b+c)` grid is `a` rows, each of width `b+c`. Counting it row by
row, splitting each row's contribution into its `b`-part and `c`-part and then
*regrouping the columns additively*, separates the total into the `a × b` grid's
count and the `a × c` grid's count — `a·b + a·c`. The regrouping is pure
addition (`add_assoc`/`add_left_comm`), so distributivity falls out **without**
assuming `Nat.left_distrib` / `Nat.mul_add`. Generated, not borrowed; ∅-axiom.

This is the last law before the arithmetic genuinely needs the `×`-atom (prime)
structure: with `+`, `×`, and their distributive bridge all generated, the
remaining frontier is primality / unique factorization (FTA).
-/

namespace E213.Meta.Nat.UnitDistrib

open E213.Meta.Nat.UnitList (count fromNat count_fromNat)
open E213.Meta.Nat.UnitGrid (UGrid total rows total_rows mul_comm_from_grid)

/-- A four-term additive regrouping: `(b+c)+(p+q) = (b+p)+(c+q)`. Pure `+`-law
    plumbing (associativity + left-commutativity), distinct from the
    distributivity being generated. -/
theorem add_shuffle (b c p q : Nat) : (b + c) + (p + q) = (b + p) + (c + q) := by
  rw [Nat.add_assoc b c (p + q), Nat.add_left_comm c p q, ← Nat.add_assoc b p (c + q)]

/-- **Row-count is additive in the width split**: an `a`-row grid of width
    `b+c` has the same total as the `a`-row width-`b` grid plus the `a`-row
    width-`c` grid. Proved by induction on the row count `a` using only
    `+`-laws — no multiplication appears, so no distributivity is presupposed. -/
theorem total_rows_add (b c : Nat) :
    ∀ (a : Nat), total (rows a (b + c)) = total (rows a b) + total (rows a c)
  | 0     => rfl
  | a + 1 => by
      show count (fromNat (b + c)) + total (rows a (b + c))
            = (count (fromNat b) + total (rows a b))
              + (count (fromNat c) + total (rows a c))
      rw [count_fromNat, count_fromNat, count_fromNat, total_rows_add b c a]
      exact add_shuffle b c (total (rows a b)) (total (rows a c))

/-- ★★★★★ **Left-distributivity is the shadow of the grid width-split**:
    `a·(b+c) = a·b + a·c`. Counting the `a × (b+c)` unit grid one way gives
    `a·(b+c)`; splitting its width into a `b`-block and a `c`-block and
    regrouping the columns additively gives `a·b + a·c`; same units, so equal.
    Generated, not presupposed — the cone uses only `+`-laws and `total_rows`
    (itself `succ_mul`-based), never `Nat.mul_add` / `Nat.left_distrib`. The
    bridge law coupling the two generated monoids. -/
theorem mul_add_from_grid (a b c : Nat) : a * (b + c) = a * b + a * c :=
  calc a * (b + c)
      = total (rows a (b + c))              := (total_rows a (b + c)).symm
    _ = total (rows a b) + total (rows a c) := total_rows_add b c a
    _ = a * b + a * c                       := by rw [total_rows, total_rows]

/-- ★ **Right-distributivity** `(a+b)·c = a·c + b·c` — the dual bridge, derived
    from the generated left-distributivity (`mul_add_from_grid`) and the
    generated `×`-commutativity (`mul_comm_from_grid`). Uses only *generated*
    laws, so the cone is `Nat.right_distrib`/`Nat.add_mul`-free too: with both
    distributive laws now generated, the commutative semiring `(ℕ,+,·,0,1)` is
    complete as a generated discipline. -/
theorem add_mul_from_grid (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm_from_grid (a + b) c, mul_add_from_grid c a b,
      mul_comm_from_grid c a, mul_comm_from_grid c b]

end E213.Meta.Nat.UnitDistrib
