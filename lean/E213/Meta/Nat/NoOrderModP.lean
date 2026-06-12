/-!
# NoOrderModP — folding the counting line into a circle destroys order

A left-to-right order needs a smallest thing and no loops.  On the
counting line ℕ — `1, 2, 3, …`, the numbers you get by adding one unit
at a time — that is fine: it never comes back on itself.

Fold that line into a **circle of length `p`** — the points `1, 2, …, p`
with "after `p` comes `1` again" — and the order cannot survive.  Going
up forever would have to come back down to where it started.

This file makes that exact.  The points are `1, 2, …, p`.  "Next" is
`next x = x + 1`, except `next p = 1` (the one wrap).  A relation `R x y`
reads "x is below y".  Suppose `R`

* never says a thing is below itself (`irrefl`),
* is preserved by chaining (`trans`),
* is preserved by `next` on both sides (`transl`),
* puts `1` below `2` (`start`).

Then there is no such `R` — the result is `False` (`no_wrapping_order`):
walking `next` from `1` gives `1 < 2 < … < p < 1`, and chaining lands
back on `1`, so `1 < 1`, which `irrefl` forbids.

No `0` and no `ℤ` enter.  The points start at `1` (one unit), and the
contrast is the bare counting line ℕ, which keeps the order precisely
because it does not wrap.

All decls ∅-axiom; bare recursion / induction + the decidable test
`x < p` (no `%`, no `0`).
-/

namespace E213.Meta.Nat.NoOrderModP

/-- The next point on the circle `1, 2, …, p`: `x + 1`, except `p` wraps
    back to `1`. -/
def next (p x : Nat) : Nat := if x < p then x + 1 else 1

/-- The orbit of `1` under `next`: `orbit 0 = 1`, then keep applying
    `next`.  It runs `1, 2, …, p, 1, …`. -/
def orbit (p : Nat) : Nat → Nat
  | 0     => 1
  | k + 1 => next p (orbit p k)

/-- For the first `p` steps the orbit just counts up: `orbit k = k + 1`
    while `k < p` (so `orbit 0 = 1`, …, `orbit (p−1) = p`). -/
theorem orbit_eq (p : Nat) : ∀ k, k < p → orbit p k = k + 1
  | 0,     _  => rfl
  | k + 1, hk => by
      have hkp : k < p := Nat.lt_of_succ_lt hk
      show next p (orbit p k) = (k + 1) + 1
      rw [orbit_eq p k hkp]
      show (if k + 1 < p then (k + 1) + 1 else 1) = (k + 1) + 1
      rw [if_pos hk]

/-- The orbit closes after exactly `p` steps: `orbit p = 1`.  At step
    `p−1` the orbit is at `p`, and `next p = 1` (the wrap). -/
theorem orbit_wrap (p : Nat) (hp : 2 ≤ p) : orbit p p = 1 := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
  have hp1 : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hp0
  have hlt : p - 1 < p := Nat.sub_lt hp0 (by decide)
  have hprev : orbit p (p - 1) = p := by
    rw [orbit_eq p (p - 1) hlt, hp1]
  have key : orbit p ((p - 1) + 1) = 1 := by
    show next p (orbit p (p - 1)) = 1
    rw [hprev]
    show (if p < p then p + 1 else 1) = 1
    rw [if_neg (Nat.lt_irrefl p)]
  rwa [hp1] at key

/-- Each orbit step is one `R`-edge: `R (orbit k) (orbit (k+1))`.  The
    first is `start`; each next edge is the previous one pushed through
    `next` on both sides by `transl`. -/
theorem edge (p : Nat) (hp : 2 ≤ p)
    (R : Nat → Nat → Prop)
    (transl : ∀ x y, R x y → R (next p x) (next p y))
    (start : R 1 2) :
    ∀ k, R (orbit p k) (orbit p (k + 1))
  | 0 => by
      have h1p : (1 : Nat) < p := hp
      show R 1 (if 1 < p then 1 + 1 else 1)
      rw [if_pos h1p]
      exact start
  | k + 1 => transl (orbit p k) (orbit p (k + 1)) (edge p hp R transl start k)

/-- Chain the edges from `1`: `R (orbit 0) (orbit (k+1))` for every `k`. -/
theorem reach (p : Nat) (hp : 2 ≤ p)
    (R : Nat → Nat → Prop)
    (trans  : ∀ x y z, R x y → R y z → R x z)
    (transl : ∀ x y, R x y → R (next p x) (next p y))
    (start : R 1 2) :
    ∀ k, R (orbit p 0) (orbit p (k + 1))
  | 0 => edge p hp R transl start 0
  | k + 1 =>
      trans (orbit p 0) (orbit p (k + 1)) (orbit p (k + 1 + 1))
        (reach p hp R trans transl start k)
        (edge p hp R transl start (k + 1))

/-- **Folding the line into a circle destroys order.**  No relation on
    the circle `1, 2, …, p` can be irreflexive, chainable,
    `next`-preserving, and put `1` below `2`.  Walking `next` from `1`
    gives `1 < 2 < … < p < 1`; chaining lands back on `1`, so `1 < 1`,
    which `irrefl` forbids.

    Needs `2 ≤ p` so the circle has at least two points. -/
theorem no_wrapping_order (p : Nat) (hp : 2 ≤ p)
    (R : Nat → Nat → Prop)
    (irrefl : ∀ x, ¬ R x x)
    (trans  : ∀ x y z, R x y → R y z → R x z)
    (transl : ∀ x y, R x y → R (next p x) (next p y))
    (start  : R 1 2) :
    False := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
  have hp1 : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hp0
  -- reach to step p: R (orbit 0) (orbit p)
  have hloop : R (orbit p 0) (orbit p ((p - 1) + 1)) :=
    reach p hp R trans transl start (p - 1)
  rw [hp1, orbit_wrap p hp] at hloop
  -- orbit 0 = 1, so this is R 1 1
  exact irrefl 1 hloop

end E213.Meta.Nat.NoOrderModP
