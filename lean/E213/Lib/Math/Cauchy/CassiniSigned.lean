import E213.Lib.Math.Cauchy.CasoratianSigned
import E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock

/-!
# CassiniSigned — the residue floor's cross-determinant is the depth-0 signed Casoratian

`DepthFloorDetOne` named the depth-0 floor by its *magnitude*: the Cassini cross-determinant
`|W| = 1` of the `P = [[2,1],[1,1]]` / φ orbit.  `CasoratianSigned` showed any Casoratian
carries two readings — a magnitude (Converge/Escape) and a **sign** (the ℕ-pair axis,
Oscillate, period 2).  This file applies that to the floor itself: the Fibonacci Cassini
identity

    fib(n+2)·fib(n) − fib(n+1)² = (−1)ⁿ⁺¹

is the **simplest signed Casoratian** — magnitude `1` (already at the floor, depth 0,
Converge) with sign `(−1)ⁿ` (Oscillate).  In ℕ-pair form (`a − b = (a, b)`, negation = swap)
the whole identity is

    `cassini_pair` :  npairEquiv (fib(n+2)·fib(n), fib(n+1)²)  (iterNeg (n+1) (1, 0))

— the Cassini pair equals the unit pair `(1, 0)` toggled `n+1` times: the floor value `±1`
with its alternating sign carried entirely by the axis-swap, ∅-axiom over ℕ (no `ℤ`).  The
step `cassini_step` (`fib(n+3)·fib(n+1) + fib(n+2)·fib(n) = fib(n+2)² + fib(n+1)²`) is the
subtraction-free Fibonacci identity behind `Wₙ = −Wₙ₋₁`; it is the `c₂ = c₀ = 1` instance of
`CasoratianSigned.casoratian_signed`, where the swap is forced (the floor is the pure
alternation).  So the residue's algebraic floor (φ, `det P = 1`) is depth 0 on the magnitude
axis and period-2 Oscillate on the sign axis — the two trivial-floor readings of the one
self-pointing.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.CassiniSigned

open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lens.Number.Nat213.Tower.NatPairToInt (npairEquiv npairEquiv_trans)
open E213.Lib.Math.Cauchy.CasoratianSigned (neg casPair iterNeg neg_congr)
open E213.Tactic.NatHelper (add_mul)

/-- ★★ **The alternating-Cassini step, subtraction-free.**  `fib(n+3)·fib(n+1) +
    fib(n+2)·fib(n) = fib(n+2)² + fib(n+1)²` — the Fibonacci identity behind `Wₙ₊₁ = −Wₙ`,
    in `npairEquiv` form: the Cassini pair at `n+1` is the **swap** of the pair at `n`.  The
    `c₂ = c₀ = 1` floor instance of `casoratian_signed`. -/
theorem cassini_step (n : Nat) :
    npairEquiv (casPair (fib (n+3) * fib (n+1)) (fib (n+2) * fib (n+2)))
               (neg (casPair (fib (n+2) * fib n) (fib (n+1) * fib (n+1)))) := by
  show fib (n+3) * fib (n+1) + fib (n+2) * fib n
     = fib (n+2) * fib (n+2) + fib (n+1) * fib (n+1)
  have r2 : fib (n+2) = fib (n+1) + fib n := rfl
  have r3 : fib (n+3) = fib (n+2) + fib (n+1) := rfl
  rw [r3, r2,
      add_mul (fib (n+1) + fib n) (fib (n+1)) (fib (n+1)),
      Nat.mul_add (fib (n+1) + fib n) (fib (n+1)) (fib n),
      Nat.add_assoc ((fib (n+1) + fib n) * fib (n+1)) (fib (n+1) * fib (n+1))
        ((fib (n+1) + fib n) * fib n),
      Nat.add_comm (fib (n+1) * fib (n+1)) ((fib (n+1) + fib n) * fib n),
      ← Nat.add_assoc ((fib (n+1) + fib n) * fib (n+1)) ((fib (n+1) + fib n) * fib n)
        (fib (n+1) * fib (n+1))]

/-- ★★★ **The Fibonacci Cassini cross-determinant is the depth-0 signed Casoratian.**
    `npairEquiv (fib(n+2)·fib(n), fib(n+1)²) (iterNeg (n+1) (1, 0))` — the Cassini pair equals
    the unit `(1,0)` (value `+1`) toggled `n+1` times, i.e. `(−1)ⁿ⁺¹`.  Magnitude `1` (the
    `det P = 1` floor, Converge depth 0) with the sign carried entirely by the period-2 axis
    swap (Oscillate).  ∅-axiom over ℕ — the residue floor's `±1` with its sign, no `ℤ`. -/
theorem cassini_pair : ∀ n,
    npairEquiv (casPair (fib (n+2) * fib n) (fib (n+1) * fib (n+1))) (iterNeg (n+1) (1, 0))
  | 0     => by show fib 2 * fib 0 + 1 = fib 1 * fib 1 + 0; rfl
  | n + 1 => npairEquiv_trans (cassini_step n) (neg_congr (cassini_pair n))

end E213.Lib.Math.Cauchy.CassiniSigned
