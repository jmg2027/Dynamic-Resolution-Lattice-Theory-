import E213.Research.ZI

/-!
# Research: `ZI.mul` commutativity (first step toward R3)

Proves `u * v = v * u` for Gaussian integers, without Mathlib's
`ring` tactic — using only `Int.mul_comm` and `Int.add_comm`.

The integral-domain property (no zero divisors) is deferred to
`ZIDomain2.lean` since it requires the Diophantus identity
`|uv|² = |u|² · |v|²`, which is a polynomial identity that is
non-trivial to prove without `ring`.
-/

namespace E213.Research.ZI

/-- Commutativity of Gaussian multiplication, manually. -/
theorem mul_comm (u v : ZI) : u * v = v * u := by
  apply ext
  · -- real part: u.re*v.re - u.im*v.im = v.re*u.re - v.im*u.im
    show u.re * v.re - u.im * v.im = v.re * u.re - v.im * u.im
    rw [Int.mul_comm u.re v.re, Int.mul_comm u.im v.im]
  · -- imag part: u.re*v.im + u.im*v.re = v.re*u.im + v.im*u.re
    show u.re * v.im + u.im * v.re = v.re * u.im + v.im * u.re
    rw [Int.mul_comm u.re v.im, Int.mul_comm u.im v.re, Int.add_comm]

end E213.Research.ZI
