import E213.Lib.Math.Combinatorics.Handshake
import E213.Meta.Nat.AddMod213

/-!
# Odd-degree count is even — the textbook handshake corollary  (∅-axiom, PURE)

A finite simple graph has an **even number of odd-degree vertices**.

We count the odd-degree vertices by `oddDegCount G n := Σ_{v<n} (deg G v % 2)`:
each odd-degree vertex contributes `1` (its degree mod 2), each even-degree vertex
contributes `0`, so the sum **is** the number of odd-degree vertices.

The proof rests on the reusable **parity-of-a-sum** lemma
`sumTo_mod_two`: the parity of a sum equals the parity of the sum of the parities,
`Σ f % 2 = Σ (f · % 2) % 2`.  Applied to `f = deg G`:

  `oddDegCount G n % 2 = Σ_{v<n} deg G v % 2 = degSum G n % 2`,

and `degSum G n = 2 · edgeCount G n` (the handshake `= 2·|E|`, already in
`Handshake.lean`), so `degSum G n % 2 = 0`.  Hence `2 ∣ oddDegCount G n`.
-/

namespace E213.Lib.Math.Combinatorics.OddDegreeCount

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.Combinatorics.Handshake
  (SimpleGraph deg degSum edgeCount degree_sum_eq_two_mul_edges
   K3 Star3 P3)
open E213.Meta.Nat.AddMod213 (add_mod dvd_of_mod_eq_zero)
open E213.Tactic.NatHelper (mul_mod_right)

/-! ## §1 — parity of a sum (reusable) -/

/-- **Parity of a sum**: `Σ_{v<n} f v % 2 = Σ_{v<n} (f v % 2) % 2`.

    The parity of a sum is the sum of the parities, mod 2.  Proved by induction on
    `n` via `sumTo_succ` + `AddMod213.add_mod` (split the top term's parity, fold the
    inductive hypothesis back in). -/
theorem sumTo_mod_two : ∀ (n : Nat) (f : Nat → Nat),
    sumTo n f % 2 = sumTo n (fun v => f v % 2) % 2
  | 0, _ => rfl
  | n + 1, f => by
    show (sumTo n f + f n) % 2 = (sumTo n (fun v => f v % 2) + f n % 2) % 2
    -- split both sides' top term off via add_mod, then use IH on the block sums
    rw [add_mod (by decide) (sumTo n f) (f n)]
    rw [add_mod (by decide) (sumTo n (fun v => f v % 2)) (f n % 2)]
    rw [sumTo_mod_two n f]
    -- right block: (f n % 2) % 2 = f n % 2
    show (sumTo n (fun v => f v % 2) % 2 + f n % 2) % 2
        = (sumTo n (fun v => f v % 2) % 2 + f n % 2 % 2) % 2
    rw [E213.Meta.Nat.AddMod213.mod_mod (f n) 2]

/-! ## §2 — odd-degree vertex count -/

/-- The number of odd-degree vertices among `v < n`: `Σ_{v<n} (deg G v % 2)`.

    Each term `deg G v % 2` is the **indicator** of "`v` has odd degree" (it is `1`
    when `deg G v` is odd, `0` when even), so this sum directly counts the
    odd-degree vertices. -/
def oddDegCount (G : SimpleGraph) (n : Nat) : Nat :=
  sumTo n (fun v => deg G n v % 2)

/-- The odd-degree count's parity equals the degree sum's parity:
    `oddDegCount G n % 2 = degSum G n % 2`. -/
theorem oddDegCount_mod_two (G : SimpleGraph) (n : Nat) :
    oddDegCount G n % 2 = degSum G n % 2 :=
  (sumTo_mod_two n (fun v => deg G n v)).symm

/-- The degree sum is even as a `% 2 = 0` statement:
    `degSum G n % 2 = 0` (from the handshake `= 2·|E|`). -/
theorem degSum_mod_two (G : SimpleGraph) (n : Nat) : degSum G n % 2 = 0 := by
  rw [degree_sum_eq_two_mul_edges G n]
  exact mul_mod_right 2 (edgeCount G n)

/-- ★★★ **`odd_degree_count_even`** — the handshake corollary in its textbook form:
    a finite simple graph has an **even number of odd-degree vertices**.
    `2 ∣ Σ_{v<n} (deg G v % 2)`.

    Explicit-witness divisibility via `dvd_of_mod_eq_zero` (no `decide`-on-dvd
    propext leak): `oddDegCount G n % 2 = degSum G n % 2 = 0`. -/
theorem odd_degree_count_even (G : SimpleGraph) (n : Nat) :
    2 ∣ oddDegCount G n :=
  dvd_of_mod_eq_zero ((oddDegCount_mod_two G n).trans (degSum_mod_two G n))

/-! ## §3 — concrete smokes (axiom-clean `decide` on closed graphs)

`deg G v % 2` is the odd-degree indicator, so `oddDegCount` is literally the count
of odd-degree vertices:

* `K3`   — all three vertices have degree `2` (even): `0` odd-degree vertices.
* `Star3`— center degree `3`, three leaves degree `1`: `4` odd-degree vertices.
* `P3`   — path ends degree `1`, middle degree `2`: `2` odd-degree vertices.

All counts even. -/

theorem K3_oddDegCount_smoke : oddDegCount K3 3 = 0 := by decide

theorem Star3_oddDegCount_smoke : oddDegCount Star3 4 = 4 := by decide

theorem P3_oddDegCount_smoke : oddDegCount P3 3 = 2 := by decide

end E213.Lib.Math.Combinatorics.OddDegreeCount
