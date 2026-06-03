import E213.Lib.Math.Real213.HyperbolicEllipticTrace
import E213.Lib.Math.Cauchy.CFiniteHomogRec
import E213.Meta.Int213.PolyIntMTactic

/-!
# The order-2 discriminant places the recurrence in the holonomicity hierarchy

The order-2 recurrence `s(n+2) = p·s(n+1) − q·s(n)` has **companion matrix** `comp p q =
[[p,−q],[1,0]]`, whose `HyperbolicEllipticTrace` discriminant is `disc = p² − 4q` — the very
quantity whose sign is the φ/π (hyperbolic/elliptic) split (`wick_discriminant_split`).  This file
ties that split to *where the recurrence sits in the hierarchy* `CFiniteHomogRec` just connected:

  * **elliptic** (`disc < 0`, here the unimodular `q = 1` cases) — the companion is one of the
    finite-order generators `S` (order 4), `U` (order 6); the orbit is **periodic**, the **bottom
    tier** (eventually periodic ⊆ C-finite ⊆ `HomogRec`).  Identifications: `comp 0 1 = S`,
    `comp 1 1 = U` — the elliptic generators *are* periodic order-2 companions.
  * **hyperbolic** (`disc > 0`) — e.g. `comp 3 1` (`disc = 5`, the golden/Lucas characteristic),
    a real quadratic-irrational iterator whose orbit **grows** (unbounded partial quotients, the
    quadratic-irrational CF tier).

So the trace-discriminant of `HyperbolicEllipticTrace` is the same dial as the orbit-growth that
separates the periodic floor from the growing C-finite sequences — the φ/π pole work and the depth
hierarchy are one structure.
-/

namespace E213.Lib.Math.Cauchy.EllipticPeriodicTier

open E213.Lib.Math.Real213.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.Cauchy.CFiniteHomogRec (order2_homogRec)
open E213.Lib.Math.Cauchy.ZeroRunNonHolonomic (HomogRec)

/-- The companion matrix of `s(n+2) = p·s(n+1) − q·s(n)`. -/
def comp (p q : Int) : Mat2 := ⟨p, -q, 1, 0⟩

theorem comp_tr (p q : Int) : Mat2.tr (comp p q) = p := by
  show p + 0 = p; exact Int.add_zero p

theorem comp_det (p q : Int) : Mat2.det (comp p q) = q := by
  show p * 0 - -q * 1 = q
  rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.mul_one]
  show (0 : Int) + - -q = q
  rw [Int.neg_neg, E213.Meta.Int213.zero_add]

/-- ★ The order-2 companion discriminant is `p² − 4q` — the `HyperbolicEllipticTrace.disc`. -/
theorem comp_disc (p q : Int) : Mat2.disc (comp p q) = p * p - 4 * q := by
  show Mat2.tr (comp p q) * Mat2.tr (comp p q) - 4 * Mat2.det (comp p q) = p * p - 4 * q
  rw [comp_tr, comp_det]

/-- The order-4 elliptic generator `S` is the companion of `s(n+2) = −s(n)`. -/
theorem comp_eq_S : comp 0 1 = Mat2.S := by decide

/-- The order-6 elliptic generator `U` is the companion of `s(n+2) = s(n+1) − s(n)`. -/
theorem comp_eq_U : comp 1 1 = Mat2.U := by decide

/-! ## Elliptic ⟹ periodic orbit (the bottom tier) -/

/-- **The order-4 elliptic recurrence is periodic with period 4.**  `s(n+2) = −s(n)` ⟹
    `s(n+4) = s(n)`. -/
theorem periodic_elliptic_S (s : Nat → Int) (hrec : ∀ n, s (n + 2) = -s n) :
    ∀ n, s (n + 4) = s n := by
  intro n
  have e2 : s (n + 2) = -s n := hrec n
  have e4 : s (n + 4) = -s (n + 2) := hrec (n + 2)
  rw [e4, e2, Int.neg_neg]

/-- **The order-6 elliptic recurrence is periodic with period 6.**  `s(n+2) = s(n+1) − s(n)` ⟹
    `s(n+6) = s(n)`. -/
theorem periodic_elliptic_U (s : Nat → Int) (hrec : ∀ n, s (n + 2) = s (n + 1) - s n) :
    ∀ n, s (n + 6) = s n := by
  intro n
  have e2 : s (n + 2) = s (n + 1) - s n := hrec n
  have e3 : s (n + 3) = s (n + 2) - s (n + 1) := hrec (n + 1)
  have e4 : s (n + 4) = s (n + 3) - s (n + 2) := hrec (n + 2)
  have e5 : s (n + 5) = s (n + 4) - s (n + 3) := hrec (n + 3)
  have e6 : s (n + 6) = s (n + 5) - s (n + 4) := hrec (n + 4)
  rw [e6, e5, e4, e3, e2]; ring_intZ

/-! ## Both poles inside the hierarchy -/

/-- The order-4 elliptic recurrence is `HomogRec` (holonomic) — and periodic (bottom tier). -/
theorem elliptic_S_homogRec (s : Nat → Int) (hrec : ∀ n, s (n + 2) = -s n) : HomogRec s := by
  apply order2_homogRec 0 1 s
  intro n
  show s (n + 2) = 0 * s (n + 1) - 1 * s n
  rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.PolyIntM.one_mulZ,
      show (0 : Int) - s n = -s n from E213.Meta.Int213.zero_add (-(s n))]
  exact hrec n

end E213.Lib.Math.Cauchy.EllipticPeriodicTier
