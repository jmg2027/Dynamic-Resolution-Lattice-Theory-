import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# PairPow — pair exponents: slot fibers transport, they do not vanish

Slot accounting for `x^(c,d) = (a,b)`
(`theory/math/numbersystems/slot_arithmetic.md` "Ontology"): a
pair-slot's two naturals are **one orbit coordinate** (the
cross-equation class — the only part the answer depends on) plus
**one fiber coordinate** (position along the orbit).  Counting raw
naturals over-counts by the fibers: `x^(n,n+1) = (a,b)` has 3 raw
naturals but 1 effective slot (the RHS orbit), and
`x^(n,n+2) = (m+1,m)` has 0 — both orbits fixed, so its solution is a
*constant* of the pair-slot layer.

"The fiber does not matter" is a theorem, not a convention, and the
proof shows something better: the fiber **transports**.  With the
subtraction-free pair exponent
`pairPow p q c d := (p^d·q^c, q^d·p^c)` ("(p/q)^(d−c)"):

* `pairPow_fiber` — riding the exponent orbit (`(c,d) ↦ (c+k,d+k)`,
  a +-fiber move) lands the value on its own ×-fiber: the results are
  cross-multiplication related.  The exponent's +-riding becomes the
  value's ×-riding.
* `pairPow_id` — at the identity orbit (`(n,n+1)`) the value is the
  base pair itself up to ×-riding:
  `pairPow p q n (n+1) = ((pq)ⁿ·p, (pq)ⁿ·q)` cross-relates to
  `(p,q)`.  Hence every solution of `x^(n,n+1) = (a,b)` is ×-related
  to `(a,b)` — two naturals represent all cases.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Slots.PairPow

open E213.Meta.Nat.PureNat (pow_add)

private theorem mul_left_comm_nat (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  rw [← E213.Tactic.NatHelper.mul_assoc a b c, Nat.mul_comm a b,
      E213.Tactic.NatHelper.mul_assoc b a c]

private theorem quad_swap (x y z w : Nat) :
    (x * y) * (z * w) = (x * w) * (y * z) := by
  rw [E213.Tactic.NatHelper.mul_assoc x y (z * w), Nat.mul_comm z w,
      mul_left_comm_nat y w z,
      ← E213.Tactic.NatHelper.mul_assoc x w (y * z)]

/-- Pair exponent on a ratio pair, subtraction-free:
    `(p,q)^(c,d) := (p^d·q^c, q^d·p^c)` — "(p/q) to the power d−c"
    with every inverse absorbed into the pair axes. -/
def pairPow (p q c d : Nat) : Nat × Nat := (p ^ d * q ^ c, q ^ d * p ^ c)

/-- ★★★★ **The exponent's +-fiber becomes the value's ×-fiber**:
    riding the exponent orbit `(c,d) ↦ (c+k, d+k)` produces a value
    cross-multiplication related to the original.  The inert slot
    does not vanish — it transports into redundancy the value already
    carries. -/
theorem pairPow_fiber (p q c d k : Nat) :
    (pairPow p q c d).1 * (pairPow p q (c + k) (d + k)).2
    = (pairPow p q (c + k) (d + k)).1 * (pairPow p q c d).2 := by
  show (p ^ d * q ^ c) * (q ^ (d + k) * p ^ (c + k))
     = (p ^ (d + k) * q ^ (c + k)) * (q ^ d * p ^ c)
  rw [quad_swap (p ^ d) (q ^ c) (q ^ (d + k)) (p ^ (c + k)),
      quad_swap (p ^ (d + k)) (q ^ (c + k)) (q ^ d) (p ^ c),
      ← pow_add p d (c + k), ← pow_add q c (d + k),
      ← pow_add p (d + k) c, ← pow_add q (c + k) d,
      Nat.add_assoc d k c, Nat.add_comm k c,
      Nat.add_assoc c k d, Nat.add_comm k d]

/-- ★★★★ **The identity orbit returns the base up to ×-riding**:
    `pairPow p q n (n+1)` cross-relates to `(p, q)` for every `n` —
    the solution of `x^(n,n+1) = (a,b)` is `(a,b)` itself, all fiber
    positions landing on one ×-orbit.  Two naturals represent all
    cases; the third was a fiber coordinate. -/
theorem pairPow_id (p q n : Nat) :
    p * (pairPow p q n (n + 1)).2 = (pairPow p q n (n + 1)).1 * q := by
  show p * (q ^ (n + 1) * p ^ n) = (p ^ (n + 1) * q ^ n) * q
  calc p * (q ^ (n + 1) * p ^ n)
      = (q ^ (n + 1) * p ^ n) * p := Nat.mul_comm _ _
    _ = q ^ (n + 1) * (p ^ n * p) :=
        E213.Tactic.NatHelper.mul_assoc _ _ _
    _ = q ^ (n + 1) * p ^ (n + 1) := by rw [← Nat.pow_succ p n]
    _ = p ^ (n + 1) * q ^ (n + 1) := Nat.mul_comm _ _
    _ = p ^ (n + 1) * (q ^ n * q) := by rw [Nat.pow_succ q n]
    _ = (p ^ (n + 1) * q ^ n) * q :=
        (E213.Tactic.NatHelper.mul_assoc _ _ _).symm

end E213.Lib.Math.NumberSystems.Slots.PairPow
