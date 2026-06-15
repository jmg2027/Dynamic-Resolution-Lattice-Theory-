import E213.Lib.Math.NumberTheory.DiffPowDvd

/-!
# Geometric series closed form `(r−1)·Σ rᵏ = rⁿ⁺¹ − 1` (∅-axiom)

The elementary integer geometric-series identity `(r−1)·Σ_{k=0}^{n} rᵏ = r^{n+1} − 1`
(`geom_sum`), by induction on `n`, with the powers-of-two specialization
`Σ_{k=0}^{n} 2ᵏ = 2^{n+1} − 1` (`pow_two_sum`).

Genuinely absent at the elementary-Int layer: the corpus "geometric series" work
(`GeomSeriesIdentity`, `CutGeomSeries`, …) is all at the Real213-cut convergence
layer (`cutSum`/`cutPow` → `1/(1−x)`), not this closed-form algebraic identity.
`ipow` is reused from `DiffPowDvd`; the Int partial sum `sumZ` is local.  ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.GeometricSeries

open E213.Lib.Math.NumberTheory.DiffPowDvd (ipow ipow_zero ipow_succ)

/-- Local Int-valued partial sum `Σ_{k<n} f k`. -/
def sumZ : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumZ n f + f n

@[simp] theorem sumZ_zero (f : Nat → Int) : sumZ 0 f = 0 := rfl
theorem sumZ_succ (n : Nat) (f : Nat → Int) :
    sumZ (n + 1) f = sumZ n f + f n := rfl

/-- ★ **Geometric series**: `(r − 1) · Σ_{k=0}^{n} rᵏ = r^{n+1} − 1`. -/
theorem geom_sum (r : Int) (n : Nat) :
    (r - 1) * sumZ (n + 1) (fun k => ipow r k) = ipow r (n + 1) - 1 := by
  induction n with
  | zero =>
      show (r - 1) * (0 + ipow r 0) = ipow r 0 * r - 1
      show (r - 1) * (0 + 1) = 1 * r - 1
      ring_intZ
  | succ n ih =>
      have expand :
          (r - 1) * sumZ (n + 2) (fun k => ipow r k)
            = (r - 1) * sumZ (n + 1) (fun k => ipow r k)
              + (r - 1) * ipow r (n + 1) := by
        show (r - 1) * (sumZ (n + 1) (fun k => ipow r k) + ipow r (n + 1))
            = (r - 1) * sumZ (n + 1) (fun k => ipow r k)
              + (r - 1) * ipow r (n + 1)
        ring_intZ
      rw [expand, ih]
      show (ipow r (n + 1) - 1) + (r - 1) * ipow r (n + 1)
          = ipow r (n + 1) * r - 1
      ring_intZ

/-- **Powers of two**: `Σ_{k=0}^{n} 2ᵏ = 2^{n+1} − 1` (from `geom_sum 2 n`). -/
theorem pow_two_sum (n : Nat) :
    sumZ (n + 1) (fun k => ipow 2 k) = ipow 2 (n + 1) - 1 := by
  have h := geom_sum 2 n
  have h1 : (2 - 1 : Int) * sumZ (n + 1) (fun k => ipow 2 k)
      = sumZ (n + 1) (fun k => ipow 2 k) := by
    show (2 - 1 : Int) * sumZ (n + 1) (fun k => ipow 2 k)
        = sumZ (n + 1) (fun k => ipow 2 k)
    ring_intZ
  exact Eq.trans h1.symm h

/-- Smoke: `Σ_{k<4} 2ᵏ = 1 + 2 + 4 + 8 = 15`. -/
theorem smoke_sum_lt_four : sumZ 4 (fun k => ipow 2 k) = 15 := by decide

end E213.Lib.Math.NumberTheory.GeometricSeries
