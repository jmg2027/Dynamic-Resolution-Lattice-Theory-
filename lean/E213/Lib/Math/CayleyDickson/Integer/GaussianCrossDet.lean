import E213.Lib.Math.CayleyDickson.Integer.ZIAlgebra213
import E213.Lib.Math.CayleyDickson.Integer.ZIUnits
import E213.Meta.Algebra213.Core

/-!
# GaussianCrossDet — the ℤ[i]-convergent cross-determinant rotates with order 4

The 2-axis-companion to `EisensteinCrossDet` (order 6).  Over the **square** lattice
`ℤ[i]`, the cross-determinant of a convergent recurrence with unit coefficient `q = i`
rotates by `μ = −i` (a primitive **4th** root of unity), period `4 = |ℤ[i]^×|`.  Between
`ℤ` (rotation order 2, `W = ±1`) and `ℤ[ω]` (order 6, `EisensteinCrossDet`), this fills the
middle rung of the axis spectrum `{2,4,6}`.

  * `cassini_ring` / `crossDet_step` — the Cassini engine `W_{n+1} = −q·W_n` over `ℤ[i]`
    (pure `CommRing213` API, the `i`-Fibonacci analog of the Eisenstein one).
  * ★★★ `gaussian_floor_rotation` — `W` rotates by `μ = −i`, `μ⁴ = 1`, orbit returns at
    step 4 and visits all 4 units.

All zero-axiom.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.GaussianCrossDet

open E213.Lib.Math.CayleyDickson.Integer.ZI (ZI units4 units4_length)
open E213.Meta.Algebra213 (Ring213 CommRing213)
open E213.Meta.Algebra213.Ring213
  (add_mul mul_add mul_assoc add_comm neg_add mul_neg neg_neg add_4_swap_mid
   neg_add_cancel_self zero_add)
open E213.Meta.Algebra213.CommRing213 (mul_comm)

/-! ## §1 — the Cassini engine over ℤ[i] -/

theorem cancel_lemma {α} [Ring213 α] (A B C : α) : A + B + -(A + C) = B + -C := by
  rw [neg_add, add_4_swap_mid A B (-A) (-C), add_comm A (-A), neg_add_cancel_self, zero_add]

/-- The Cassini ring identity over `ℤ[i]`: `(p·x + q·y)·z − x·(p·z + q·w) = q·(y·z − x·w)`. -/
theorem cassini_ring (p q x y z w : ZI) :
    (p*x + q*y)*z - x*(p*z + q*w) = q*(y*z - x*w) := by
  show (p*x + q*y)*z + -(x*(p*z + q*w)) = q*(y*z + -(x*w))
  have hE1 : p*x*z = x*(p*z) := by rw [mul_comm p x, mul_assoc]
  have hE2 : q*y*z = q*(y*z) := by rw [mul_assoc]
  have hE3 : x*(q*w) = q*(x*w) := by rw [← mul_assoc, mul_comm x q, mul_assoc]
  calc (p*x + q*y)*z + -(x*(p*z + q*w))
      = x*(p*z) + q*(y*z) + -(x*(p*z) + q*(x*w)) := by rw [add_mul, mul_add, hE1, hE2, hE3]
    _ = q*(y*z) + -(q*(x*w)) := cancel_lemma _ _ _
    _ = q*(y*z) + q*(-(x*w)) := by rw [← mul_neg]
    _ = q*(y*z + -(x*w)) := by rw [← mul_add]

theorem qmul_antisym (q X Y : ZI) : q * (Y - X) = -(q * (X - Y)) := by
  show q * (Y + -X) = -(q * (X + -Y))
  have h : Y + -X = -(X + -Y) := by rw [neg_add, neg_neg, add_comm Y (-X)]
  rw [h, mul_neg]

/-- The cross-determinant of `ℤ[i]`-convergents. -/
def crossDet (a d : Nat → ZI) (n : Nat) : ZI :=
  a (n+1) * d n - a n * d (n+1)

/-- ★★ **The Cassini engine over `ℤ[i]`.**  `W_{n+1} = −q·W_n`. -/
theorem crossDet_step (a d : Nat → ZI) (p q : ZI)
    (ha : ∀ n, a (n+2) = p * a (n+1) + q * a n)
    (hd : ∀ n, d (n+2) = p * d (n+1) + q * d n) (n : Nat) :
    crossDet a d (n+1) = -(q * crossDet a d n) := by
  show a (n+2) * d (n+1) - a (n+1) * d (n+2)
     = -(q * (a (n+1) * d n - a n * d (n+1)))
  rw [ha n, hd n, cassini_ring p q (a (n+1)) (a n) (d (n+1)) (d n)]
  exact qmul_antisym q (a (n+1) * d n) (a n * d (n+1))

/-! ## §2 — the i-Fibonacci witness and the order-4 rotation -/

/-- A second-order `ℤ[i]`-recurrence `s_{n+2} = p·s_{n+1} + q·s_n` from seeds. -/
def gfib (p q s0 s1 : ZI) : Nat → ZI
  | 0   => s0
  | 1   => s1
  | n+2 => p * gfib p q s0 s1 (n+1) + q * gfib p q s0 s1 n

theorem gfib_rec (p q s0 s1 : ZI) (n : Nat) :
    gfib p q s0 s1 (n+2) = p * gfib p q s0 s1 (n+1) + q * gfib p q s0 s1 n := rfl

/-- The `i`-Fibonacci numerator/denominator: `s_{n+2} = s_{n+1} + i·s_n` (`q = i`). -/
def aGFib : Nat → ZI := gfib ⟨1, 0⟩ ⟨0, 1⟩ ⟨0, 0⟩ ⟨1, 0⟩
def dGFib : Nat → ZI := gfib ⟨1, 0⟩ ⟨0, 1⟩ ⟨1, 0⟩ ⟨0, 0⟩

/-- The cross-determinant rotation step: multiplication by `μ = ⟨0,−1⟩ = −i`. -/
theorem gaussian_cross_step (n : Nat) :
    crossDet aGFib dGFib (n+1) = (⟨0, -1⟩ : ZI) * crossDet aGFib dGFib n := by
  rw [crossDet_step aGFib dGFib ⟨1, 0⟩ ⟨0, 1⟩
        (fun m => gfib_rec ⟨1, 0⟩ ⟨0, 1⟩ ⟨0, 0⟩ ⟨1, 0⟩ m)
        (fun m => gfib_rec ⟨1, 0⟩ ⟨0, 1⟩ ⟨1, 0⟩ ⟨0, 0⟩ m) n,
      show (⟨0, -1⟩ : ZI) = -(⟨0, 1⟩ : ZI) from by decide,
      E213.Meta.Algebra213.Ring213.neg_mul]

/-- ★★★ **The Gaussian floor rotates with order `4 = |ℤ[i]^×|`.**  The cross-determinant is
    multiplied each step by `μ = −i` (`gaussian_cross_step`), `μ⁴ = 1`, the orbit returning
    at step 4; the unit group it walks has order 4.  The square-lattice middle rung between
    `ℤ` (order 2) and `ℤ[ω]` (order 6). -/
theorem gaussian_floor_rotation :
    (∀ n, crossDet aGFib dGFib (n+1) = (⟨0, -1⟩ : ZI) * crossDet aGFib dGFib n)
    ∧ ((⟨0, -1⟩ : ZI) * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩ = ⟨1, 0⟩)
    ∧ (crossDet aGFib dGFib 4 = crossDet aGFib dGFib 0)
    ∧ units4.length = 4 :=
  ⟨gaussian_cross_step, by decide, by decide, units4_length⟩

end E213.Lib.Math.CayleyDickson.Integer.GaussianCrossDet
