import E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat

/-!
# ZeckendorfCarry — the golden (Fibonacci-base) odometer carry `011 → 100`

The binary odometer (`Theory/Raw/Odometer`) carries in base `2` (`1 + 1 = 10`).  The residue's
*own* base is not `2` but the Fibonacci spiral (the `P = [[2,1],[1,1]]` orbit, `φ`): the
**Zeckendorf / golden adic**, place values `fib 2, fib 3, fib 4, … = 1, 2, 3, 5, 8, …`, digits
`∈ {0,1}` with *no two consecutive 1s*.  Its carry is `011 → 100` — the Fibonacci recurrence
`fib (i+4) = fib (i+2) + fib (i+3)` lifting one rung of the spiral, the residue unit `+1` made a
base change ("2의 결과가 3": `fib 2 + fib 3 = fib 4`, i.e. `1 + 2 = 3`).

This file states that carry as a **value-preserving** rewrite on Fibonacci-base digit lists: two
consecutive `1`s at rungs `(i, i+1)` rewrite to a single `1` carried into rung `i+2` (incrementing
whatever digit sits there), with the Zeckendorf value unchanged (`fibValFrom_carry`) — because the
rung weights satisfy the Fibonacci recurrence (`zeck_carry_weight`).  The companion law —
admissibility, *no two consecutive 1s* — is the Cassini `W = ±1` / `det P = 1` digit law
(`FibCassiniNat.fib_cassini_norm`), the µF floor written in digits.

Honest scope: the golden adic is **Ostrowski(φ) = Zeckendorf** (a known numeration); the 213
reading is that its carry IS the residue unit `+1` and its base IS the self-pointing spiral.  All
∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ZeckendorfCarry

open E213.Lib.Math.Algebra.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.NumberSystems.Real213.FibCassiniNat (fib_cassini_norm)

/-- The Fibonacci recurrence — the carry identity (rung `n+2` is the sum of `n+1` and `n`). -/
theorem fib_rec (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

/-- ★★ **The golden carry preserves value at the weights.**  `fib (i+2) + fib (i+3) = fib (i+4)`:
    two consecutive Zeckendorf rungs `i, i+1` sum to the next rung `i+2` — the `011 → 100` carry
    is the Fibonacci recurrence, the residue unit `+1` lifting one rung of the spiral. -/
theorem zeck_carry_weight (i : Nat) : fib (i + 2) + fib (i + 3) = fib (i + 4) := by
  rw [show fib (i + 4) = fib (i + 3) + fib (i + 2) from fib_rec (i + 2)]
  exact Nat.add_comm _ _

/-- The Zeckendorf value of a Fibonacci-base digit list (rung `0` of the list weighted by
    `fib (i+2)`; the next rung by `fib (i+3)`; …). -/
def fibValFrom (i : Nat) : List Nat → Nat
  | []      => 0
  | d :: ds => d * fib (i + 2) + fibValFrom (i + 1) ds

/-- The Zeckendorf value of a digit list (rung `j` weighted by `fib (j+2)`). -/
def fibVal (ds : List Nat) : Nat := fibValFrom 0 ds

/-- Cons-unfolding of `fibValFrom` (equation lemma). -/
theorem fibValFrom_cons (i d : Nat) (ds : List Nat) :
    fibValFrom i (d :: ds) = d * fib (i + 2) + fibValFrom (i + 1) ds := rfl

/-- ★★★ **The golden odometer carry `011 → 100` preserves value** (at any rung `i`).  Two
    consecutive `1`-digits at rungs `i, i+1` rewrite to a single `1` carried into rung `i+2`
    (incrementing whatever digit sits there), with the Zeckendorf value unchanged — the carry is
    the Fibonacci recurrence (`zeck_carry_weight`) realised on digit lists.  This is the residue
    unit `+1` lifting one rung of the spiral, the golden-adic odometer step. -/
theorem fibValFrom_carry (i d : Nat) (rest : List Nat) :
    fibValFrom i (1 :: 1 :: d :: rest) = fibValFrom i (0 :: 0 :: (d + 1) :: rest) := by
  show 1 * fib (i + 2) + (1 * fib (i + 3) + (d * fib (i + 4) + fibValFrom (i + 3) rest))
     = 0 * fib (i + 2) + (0 * fib (i + 3) + ((d + 1) * fib (i + 4) + fibValFrom (i + 3) rest))
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_add, Nat.zero_add,
      E213.Meta.Nat.PureNat.add_mul, Nat.one_mul, ← Nat.add_assoc, zeck_carry_weight i,
      ← Nat.add_assoc, Nat.add_comm (fib (i + 4)) (d * fib (i + 4))]

/-- ★★★ **The golden-adic odometer carry, bundled.**  The residue's own base — the Fibonacci
    spiral — carries `011 → 100`:

    1. **the carry weight law** — `fib (i+2) + fib (i+3) = fib (i+4)` at every rung
       (`zeck_carry_weight`): the Fibonacci recurrence, the `+1` lifting one spiral rung;
    2. **value-preservation** — the `011 → 100` rewrite leaves the Zeckendorf value unchanged
       (`fibValFrom_carry`): the odometer step is exact;
    3. **the ground instance** — `fib 2 + fib 3 = fib 4`, i.e. `1 + 2 = 3` ("2의 결과가 3");
    4. **admissibility = Cassini** — no two consecutive `1`s is the Cassini `W = ±1` / `det P = 1`
       digit law (`fib_cassini_norm`), the µF floor written in digits.

    The variable-base (Fibonacci) companion of the binary odometer (`Theory/Raw/Odometer`): same
    residue unit `+1`, the residue's own spiral base.  ∅-axiom. -/
theorem golden_adic_carry :
    (∀ i, fib (i + 2) + fib (i + 3) = fib (i + 4))
    ∧ (∀ (i d : Nat) (rest : List Nat),
        fibValFrom i (1 :: 1 :: d :: rest) = fibValFrom i (0 :: 0 :: (d + 1) :: rest))
    ∧ (fib 2 + fib 3 = fib 4)
    ∧ (∀ n, fib (2 * n + 2) * fib (2 * n + 2) + 1
        = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1)) :=
  ⟨zeck_carry_weight, fibValFrom_carry, by decide, fib_cassini_norm⟩

end E213.Lib.Math.NumberSystems.Real213.ZeckendorfCarry
