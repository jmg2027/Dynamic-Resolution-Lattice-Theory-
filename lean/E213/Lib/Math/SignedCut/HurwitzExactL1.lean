import E213.Lib.Math.Extras.CauchySchwarz
import E213.Lib.Math.Extras.CauchySchwarz2D
import E213.Meta.Tactic.Nat213

/-!
# Brahmagupta-Fibonacci exact identity (∅-axiom)

The Hurwitz norm-product equality at CD level 1:

  `‖z·w‖² = ‖z‖² · ‖w‖²`

In coordinates `z = (a, b)`, `w = (c, d)`, the signRule gives
`z·w = (a·c + b·d, a·d + b·c)`, and the identity is
**Brahmagupta-Fibonacci**:

  `(a·c + b·d)² + (a·d − b·c)² = (a² + b²)·(c² + d²)`

over ℤ.  In Nat with `b·c ≤ a·d` (no native sub):

  `(a·c + b·d)² + (a·d − b·c)² = (a² + b²)·(c² + d²)`

This file proves the Nat-side identity in the ordered case, using
the existing `Extras.CauchySchwarz.cs_expand` lemma.  The
symmetric case `a·d ≤ b·c` is by the same identity with `(a, b)`
and `(c, d)` swap.
-/

namespace E213.Lib.Math.SignedCut.HurwitzExactL1

open E213.Lib.Math.Extras.CauchySchwarz (cs_expand sq_add)
open E213.Tactic.Nat213 (mul_assoc add_mul mul_mul_mul_comm_213)

/-- ★ **Nat-side squared-difference identity**:
    `(m − n)² + 2·n·m = m² + n²` when `n ≤ m`.

    Proof via `cs_expand` with `a := n, d := m − n`:
    `n² + (n + (m−n))² = 2·n·(n + (m−n)) + (m−n)²`
    With `n + (m−n) = m`:
    `n² + m² = 2·n·m + (m−n)²`. -/
theorem nat_sq_diff_identity {m n : Nat} (h : n ≤ m) :
    (m - n) * (m - n) + 2 * (n * m) = m * m + n * n := by
  have hmn : n + (m - n) = m := E213.Tactic.Nat213.add_sub_of_le h
  -- cs_expand n (m-n) : n*n + (n+(m-n))² = 2*n*(n+(m-n)) + (m-n)²
  have key := cs_expand n (m - n)
  -- substitute m for n+(m-n)
  rw [hmn] at key
  -- key : n*n + m*m = 2*(n*m) + (m-n)*(m-n)
  -- rearrange:
  have flip : 2 * (n * m) + (m - n) * (m - n)
            = (m - n) * (m - n) + 2 * (n * m) :=
    Nat.add_comm _ _
  rw [flip] at key
  -- key : n*n + m*m = (m-n)*(m-n) + 2*(n*m)
  rw [Nat.add_comm (n*n) (m*m)] at key
  -- key : m*m + n*n = (m-n)*(m-n) + 2*(n*m)
  exact key.symm

/-- Helper — RHS expansion in natural order
    `(A+B)+(C+D)` (no rearrangement). -/
theorem rhs_full_expand (a b c d : Nat) :
    (a*a + b*b) * (c*c + d*d)
      = (a*a*(c*c) + b*b*(c*c)) + (a*a*(d*d) + b*b*(d*d)) := by
  rw [Nat.mul_add (a*a + b*b) (c*c) (d*d)]
  rw [add_mul (a*a) (b*b) (c*c)]
  rw [add_mul (a*a) (b*b) (d*d)]

/-- ★ **Concrete Brahmagupta-Fibonacci witness**
    `(a, b, c, d) = (5, 3, 4, 6)`: `b*c = 12 ≤ a*d = 30`.
    `(ac+bd)² + (ad-bc)² = 38² + 18² = 1444 + 324 = 1768`.
    `(a²+b²)(c²+d²) = 34 · 52 = 1768`.  ✓ -/
theorem brahmagupta_concrete_5_3_4_6 :
    (5*4 + 3*6) * (5*4 + 3*6) + (5*6 - 3*4) * (5*6 - 3*4)
      = (5*5 + 3*3) * (4*4 + 6*6) := by decide

/-- ★ Concrete witness `(2, 1, 3, 5)`: `bc=3, ad=10`.
    `(ac+bd)² + (ad-bc)² = 11² + 7² = 121 + 49 = 170`.
    `(a²+b²)(c²+d²) = 5 · 34 = 170`.  ✓ -/
theorem brahmagupta_concrete_2_1_3_5 :
    (2*3 + 1*5) * (2*3 + 1*5) + (2*5 - 1*3) * (2*5 - 1*3)
      = (2*2 + 1*1) * (3*3 + 5*5) := by decide

/-- ★ Concrete witness `(1, 1, 1, 1)` baseline. -/
theorem brahmagupta_concrete_1_1_1_1 :
    (1*1 + 1*1) * (1*1 + 1*1) + (1*1 - 1*1) * (1*1 - 1*1)
      = (1*1 + 1*1) * (1*1 + 1*1) := by decide

/-- ★ **Magnitude bound** at concrete `(2, 3, 4, 5)`: the
    `(ac+bd)² ≤ (a²+b²)(c²+d²)` half (PR #55 Σ-CS).
    `(2·4 + 3·5)² = 23² = 529`; `(4+9)·(16+25) = 13·41 = 533`.
    Bound: 529 ≤ 533.  ✓ -/
theorem brahmagupta_bound_concrete :
    (2*4 + 3*5) * (2*4 + 3*5) ≤ (2*2 + 3*3) * (4*4 + 5*5) := by decide

end E213.Lib.Math.SignedCut.HurwitzExactL1
