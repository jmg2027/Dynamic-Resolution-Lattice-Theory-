import E213.Lib.Math.NumberSystems.Real213.HyperbolicEllipticTrace
import E213.Lib.Math.Cauchy.CFiniteHomogRec
import E213.Lib.Math.Cauchy.NewtonGregory
import E213.Lib.Math.Cauchy.PolyDepthMonotone
import E213.Meta.Int213.Order
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

open E213.Lib.Math.NumberSystems.Real213.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.Cauchy.CFiniteHomogRec (order2_homogRec)
open E213.Lib.Math.Cauchy.ZeroRunNonHolonomic (HomogRec)
open E213.Lib.Math.Cauchy.NewtonGregory (diffZ liftKZ polyDepthZ)
open E213.Lib.Math.Cauchy.PolyDepthMonotone (EvStrictMonoZ evStrictMonoZ_ge)
open E213.Meta.Int213.Order

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

/-! ## The parabolic rung: `disc = 0` ⟺ polynomial depth 1 (linear)

The middle discriminant sign — `disc = 0`, the companion `comp 2 1` — is the recurrence
`s(n+2) = 2·s(n+1) − s(n)`, i.e. `Δ²s = 0`: exactly the degree-1 (linear) polynomials, the
`polyDepthZ 1` floor.  So the discriminant trichotomy `<0 / =0 / >0` reads off the hierarchy
directly: *elliptic* periodic (bottom), *parabolic* linear-polynomial (the depth-1 floor of the
generating ring), *hyperbolic* growing (quadratic-irrational CF). -/

/-- The parabolic companion has zero discriminant. -/
theorem parabolic_comp_disc : Mat2.disc (comp 2 1) = 0 := by rw [comp_disc]; decide

/-- ★★★ **Parabolic ⟺ linear.**  `s(n+2) = 2·s(n+1) − s(n)` (the `disc = 0` order-2 recurrence,
    `Δ²s = 0`) holds for all `n` **iff** `s` has polynomial depth `1` — i.e. `s` is a degree-≤1
    polynomial (`finite_depthZ_iff`).  The parabolic point of the φ/π discriminant *is* the
    depth-1 floor of the generating ring. -/
theorem parabolic_iff_depth1 (s : Nat → Int) :
    (∀ n, s (n + 2) = 2 * s (n + 1) - s n) ↔ polyDepthZ 1 s := by
  constructor
  · intro hrec
    have h2 : ∀ n, liftKZ 1 s (n + 1) = liftKZ 1 s n := fun n => by
      show s (n + 2) - s (n + 1) = s (n + 1) - s n
      rw [hrec n]; ring_intZ
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [h2 n, ih]
  · intro hpd n
    have e' : s (n + 2) - s (n + 1) = s (n + 1) - s n := (hpd (n + 1)).trans (hpd n).symm
    have step : s (n + 2) = (s (n + 2) - s (n + 1)) + s (n + 1) :=
      (E213.Meta.Int213.sub_add_cancel_int (s (n + 2)) (s (n + 1))).symm
    rw [e'] at step
    rw [step]; ring_intZ

/-! ## The hyperbolic rung: `disc > 0` ⟹ strictly increasing orbit (growth)

`comp 3 1` (`disc = 5`, the golden/Lucas characteristic) is hyperbolic; the recurrence
`s(n+2) = 3·s(n+1) − s(n)` with positive increasing seed grows strictly — the opposite of the
elliptic periodic floor, and the unbounded-partial-quotient (quadratic-irrational) CF tier. -/

/-- ★★★ **Hyperbolic ⟹ strictly increasing.**  `s(n+2) = 3·s(n+1) − s(n)` with `0 < s 0 < s 1`
    is strictly increasing everywhere (`EvStrictMonoZ 0 s`).  Invariant `0 < s n ∧ s n < s(n+1)`:
    `s(n+2) − s(n+1) = 2·s(n+1) − s(n) > 0` because `s(n) < s(n+1) ≤ 2·s(n+1)`. -/
theorem hyperbolic_strictMono (s : Nat → Int) (hrec : ∀ n, s (n + 2) = 3 * s (n + 1) - s n)
    (h0 : 0 < s 0) (h01 : s 0 < s 1) : EvStrictMonoZ 0 s := by
  have aux : ∀ n, 0 < s n ∧ s n < s (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h01⟩
    | succ n ih =>
      obtain ⟨hpos, hlt⟩ := ih
      have hpos1 : 0 < s (n + 1) := lt_trans hpos hlt
      have hdouble : s (n + 1) ≤ 2 * s (n + 1) := by
        apply le_of_sub_nonneg
        rw [show 2 * s (n + 1) - s (n + 1) = s (n + 1) by ring_intZ]
        exact nonneg_of_le_zero (le_of_lt hpos1)
      have hlt2 : s n < 2 * s (n + 1) := lt_of_lt_of_le hlt hdouble
      have hstep : s (n + 1) < s (n + 2) := by
        apply lt_of_sub_pos
        rw [hrec n, show 3 * s (n + 1) - s n - s (n + 1) = 2 * s (n + 1) - s n by ring_intZ]
        exact sub_pos_of_lt hlt2
      exact ⟨hpos1, hstep⟩
  intro n _; exact (aux n).2

/-- The hyperbolic orbit grows at least linearly: `s 0 + i ≤ s i` for all `i` — hence **unbounded**
    (the quadratic-irrational CF tier, opposite the elliptic periodic floor). -/
theorem hyperbolic_grows (s : Nat → Int) (hrec : ∀ n, s (n + 2) = 3 * s (n + 1) - s n)
    (h0 : 0 < s 0) (h01 : s 0 < s 1) : ∀ i, s 0 + Int.ofNat i ≤ s i := by
  intro i
  have h := evStrictMonoZ_ge (hyperbolic_strictMono s hrec h0 h01) i
  rwa [Nat.zero_add] at h

/-! ## Order 3: the discriminant trichotomy does NOT lift — root-location, not sign

At order 2 the discriminant `tr²−4` *is* the dial (elliptic/parabolic/hyperbolic = periodic/linear/
growing).  At order 3 this **breaks**.  The order-3 recurrence `s(n+3)=a·s(n+2)+b·s(n+1)+c·s(n)` has
characteristic cubic `x³−a·x²−b·x−c` with cubic discriminant `Δ₃`; but `Δ₃`'s sign only splits
*3-real-roots* (`>0`) from *1-real+2-complex* (`<0`) — it does **not** classify periodicity.  Both the
periodic `(0,0,1)` (`x³−1`, period 3) and the **growing Tribonacci** `(1,1,1)` (dominant real root
≈1.839) have `Δ₃ < 0` (−27 and −44, `cubic_disc_witnesses`).  The real periodicity dial at order 3 is
**root-location** — all roots on the unit circle, i.e. the char poly is a product of cyclotomics
(Kronecker), with necessary condition `|c| = 1` (the unimodular `SL₃` floor, mirroring order-2 `q=±1`).
So the order-2 discriminant's classifying power is *special to order 2*, where `tr²−4` couples the
additive (trace) and multiplicative (det) folds; above it, the discriminant degenerates to a coarse
real/complex split and the finer cyclotomic data takes over.  (Per the repo's category-error guard:
"elliptic-*analog*" = periodic cyclotomic orbit, NOT an elliptic curve.) -/

/-- The cubic discriminant of the order-3 characteristic polynomial `x³ − a·x² − b·x − c`. -/
def cubic_disc (a b c : Int) : Int :=
  -18 * a * b * c - 4 * a * a * a * c + a * a * b * b + 4 * b * b * b - 27 * c * c

/-- ★★ **`Δ₃`'s sign does not classify periodicity.**  The periodic `(0,0,1)` (`x³−1`, period 3),
    the period-4 `(1,−1,1)`, the period-6 `(2,−2,1)`, and the **growing** Tribonacci `(1,1,1)` all
    have `Δ₃ < 0` — so the order-2 elliptic/hyperbolic sign-split fails to lift to order 3. -/
theorem cubic_disc_witnesses :
    cubic_disc 0 0 1 = -27 ∧ cubic_disc 1 (-1) 1 = -16
    ∧ cubic_disc 2 (-2) 1 = -3 ∧ cubic_disc 1 1 1 = -44 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★ **Order-3 elliptic-analog, period 4.**  `s(n+3)=s(n+2)−s(n+1)+s(n)` ⟹ `s(n+4)=s(n)`.
    Char poly `(x−1)(x²+1)` — roots `1, i, −i`, all roots of unity (the cyclotomic/periodic floor),
    `Δ₃ = −16 < 0` (same sign class as growing Tribonacci: periodicity is root-location, not sign). -/
theorem periodic_elliptic_order3_p4 (s : Nat → Int)
    (hrec : ∀ n, s (n + 3) = s (n + 2) - s (n + 1) + s n) : ∀ n, s (n + 4) = s n := by
  intro n
  have e3 : s (n + 3) = s (n + 2) - s (n + 1) + s n := hrec n
  have e4 : s (n + 4) = s (n + 3) - s (n + 2) + s (n + 1) := hrec (n + 1)
  rw [e4, e3]; ring_intZ

/-- ★★★ **Order-3 elliptic-analog, period 6.**  `s(n+3)=2·s(n+2)−2·s(n+1)+s(n)` ⟹ `s(n+6)=s(n)`.
    Char poly `(x−1)(x²−x+1)` — roots `1` and the primitive 6th roots of unity, `Δ₃ = −3 < 0`. -/
theorem periodic_elliptic_order3_p6 (s : Nat → Int)
    (hrec : ∀ n, s (n + 3) = 2 * s (n + 2) - 2 * s (n + 1) + s n) : ∀ n, s (n + 6) = s n := by
  intro n
  have e3 : s (n + 3) = 2 * s (n + 2) - 2 * s (n + 1) + s n := hrec n
  have e4 : s (n + 4) = 2 * s (n + 3) - 2 * s (n + 2) + s (n + 1) := hrec (n + 1)
  have e5 : s (n + 5) = 2 * s (n + 4) - 2 * s (n + 3) + s (n + 2) := hrec (n + 2)
  have e6 : s (n + 6) = 2 * s (n + 5) - 2 * s (n + 4) + s (n + 3) := hrec (n + 3)
  rw [e6, e5, e4, e3]; ring_intZ

end E213.Lib.Math.Cauchy.EllipticPeriodicTier
