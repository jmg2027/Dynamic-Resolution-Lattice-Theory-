import E213.Meta.Nat.AddMod213

/-!
# NoOrderModP — wrapping around mod p destroys left-to-right order

A left-to-right order needs a bottom and no loops.  On a line (ℕ, ℤ)
that is fine.  On a circle (mod p) adding 1 eventually returns to where
you started, so "keeps going up" would have to come back down — there
is no consistent up.

This file makes that exact.  Work with the numbers `0,1,…,p−1`
(the residues mod p) and a relation `R x y` standing for "`x` is below
`y`".  Suppose `R`

* never says a thing is below itself (`irrefl`),
* is preserved by chaining (`trans`),
* is preserved when you add 1 to both sides, taken mod p (`transl`),
* puts 0 below 1 (`start`).

Then there is no such `R`: the result is `False` (`no_wrapping_order`).

Why: adding 1 walks the single edges `0 < 1 < 2 < … < p−1 < 0`.
Chaining them from the start gives `R (0 % p) (p % p)`.  But `p % p`
and `0 % p` are the same residue, so this says `R (0 % p) (0 % p)` —
a thing below itself, which `irrefl` forbids.

This is the exact price of wrapping.  You can fold the line into a
circle to make every power solvable (discrete logs always exist mod p),
but you lose the order the line had.  The companion fact is that ℤ
DOES carry such an order, precisely because ℤ does not wrap
(`Int213.OrderMul` sign trichotomy).

All decls ∅-axiom.  The only mod facts used are the PURE
`AddMod213.mod_self` (`n % n = 0`) and `AddMod213.zero_mod`
(`0 % n = 0`); everything else is bare induction.
-/

namespace E213.Meta.Nat.NoOrderModP

open E213.Meta.Nat.AddMod213 (mod_self zero_mod mod_add_mod)

/-- One edge of the circle: from "0 is below 1" and "add 1 keeps the
    order", `R (k % p) ((k+1) % p)` for every `k`.  Walk by induction
    on `k`: the base edge is `start`; each next edge is the previous
    one with 1 added to both sides.

    `transl` hands back `R ((k%p + 1) % p) (((k+1)%p + 1) % p)`;
    `mod_add_mod` (needs `0 < p`) says "adding inside a `% p` is the
    same as adding outside", which turns both sides into the form
    `R ((k+1) % p) ((k+1+1) % p)` we want. -/
theorem edge (p : Nat) (hp : 0 < p)
    (R : Nat → Nat → Prop)
    (transl : ∀ x y, R x y → R ((x + 1) % p) ((y + 1) % p))
    (start : R (0 % p) (1 % p)) :
    ∀ k, R (k % p) ((k + 1) % p)
  | 0 => start
  | k + 1 => by
      have h := transl (k % p) ((k + 1) % p) (edge p hp R transl start k)
      rw [mod_add_mod hp k 1, mod_add_mod hp (k + 1) 1] at h
      exact h

/-- Chain the edges from 0: `R (0 % p) ((k+1) % p)` for every `k`.
    Start at the first edge `R (0 % p) (1 % p)`, then glue on one more
    edge at a time with `trans`. -/
theorem reach (p : Nat) (hp : 0 < p)
    (R : Nat → Nat → Prop)
    (trans  : ∀ x y z, R x y → R y z → R x z)
    (transl : ∀ x y, R x y → R ((x + 1) % p) ((y + 1) % p))
    (start : R (0 % p) (1 % p)) :
    ∀ k, R (0 % p) ((k + 1) % p)
  | 0 => start
  | k + 1 =>
      trans (0 % p) ((k + 1) % p) ((k + 1 + 1) % p)
        (reach p hp R trans transl start k)
        (edge p hp R transl start (k + 1))

/-- **Wrapping destroys order.**  No relation on the residues mod p can
    be an irreflexive, chainable, add-1-preserving order that puts 0
    below 1.  Adding 1 walks `0 < 1 < … < p−1 < 0` and chaining lands
    back on 0, giving `0 < 0`, which `irrefl` forbids.

    Needs `2 ≤ p` so the circle has at least two points (the claim "0
    below 1" needs `0 ≠ 1` mod p). -/
theorem no_wrapping_order (p : Nat) (hp : 2 ≤ p)
    (R : Nat → Nat → Prop)
    (irrefl : ∀ x, ¬ R x x)
    (trans  : ∀ x y z, R x y → R y z → R x z)
    (transl : ∀ x y, R x y → R ((x + 1) % p) ((y + 1) % p))
    (start  : R (0 % p) (1 % p)) :
    False := by
  -- p ≥ 2 means p = (p-1) + 1, so the chain reaches index p-1 giving
  -- `R (0 % p) ((p-1+1) % p) = R (0 % p) (p % p)`.
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
  have hp1 : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hp0
  have hloop : R (0 % p) (((p - 1) + 1) % p) :=
    reach p hp0 R trans transl start (p - 1)
  rw [hp1] at hloop
  -- p % p = 0 = 0 % p, so this is `R (0 % p) (0 % p)`.
  rw [mod_self p] at hloop
  rw [(zero_mod p).symm] at hloop
  exact irrefl (0 % p) hloop

end E213.Meta.Nat.NoOrderModP
