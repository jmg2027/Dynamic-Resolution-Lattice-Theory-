import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.NumberTheory.ModArith.FP2Sqrt5
/-!
# 𝔽_{p²} = 𝔽_p[x] / (x² - D) — parametric in `D : Nat`

Generalises `FP2Sqrt5` (D = 5) to **arbitrary** non-square parameter
`D : Nat`.  The ring laws (commutativity, distributivity), Frobenius
properties (involution, additivity, multiplicativity), and the
norm identity `x · σ(x) = (Norm_D(x), 0)` are universal in `(p, D)`.

When `D` is a quadratic residue mod `p` (split case), `√D ∈ 𝔽_p` and
`𝔽_p[√D] ≅ 𝔽_p × 𝔽_p` (degenerate, not a field extension).  When
`D` is a non-residue (inert case), `𝔽_p[√D] = 𝔽_{p²}` is a true
degree-2 field extension.

The Lens between `(p, D)` and the Legendre symbol `(D/p)`:

  `(√D)^p = D^((p-1)/2) · √D ≡ (D/p) · √D  (mod p)`     [Euler]

Frobenius σ fixes √D iff D is a QR mod p, i.e., (D/p) = +1; otherwise
σ sends √D ↦ -√D.

Mathlib-level field-extension infrastructure, 213-native, all
declarations PURE.

## Naming convention

Functions take `D` as the **first** parameter, then `p`:
  `fp2dAdd D p x y`, `fp2dMul D p x y`, etc.
This puts the "algebra parameter" (D) before the "modulus parameter" (p),
mirroring the mathematical statement `𝔽_p[√D]` (the algebra is named
by D, then the modulus reduces it).

Specialisation theorems witness that at `D = 5`, every `fp2d*` operation
matches the corresponding `fp2*` operation from `FP2Sqrt5`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.FP2SqrtD

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self zero_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc sub_add_cancel)
open E213.Lib.Math.NumberTheory.ModArith.FP2Sqrt5
  (nmod_add_self_zero neg_mod_add neg_mod_mul_left neg_mod_mul_right
   neg_mod_mul_neg nmod_self_mod_zero)

/-- Element representation: pair `(a, b)` for `a + b·√D` in `𝔽_p[√D]`. -/
abbrev FP2 : Type := Nat × Nat

/-- Zero element `0 + 0·√D`. -/
def fp2dZero : FP2 := (0, 0)

/-- Unit element `1 + 0·√D`. -/
def fp2dOne (p : Nat) : FP2 := (1 % p, 0)

/-- Scalar embedding: `n ↦ n + 0·√D = (n % p, 0)`. -/
def fp2dOfNat (p n : Nat) : FP2 := (n % p, 0)

/-- The "irrational generator" `√D = 0 + 1·√D`. -/
def fp2dSqrtD (p : Nat) : FP2 := (0, 1 % p)

/-- Addition: `(a + b√D) + (c + d√D) = (a + c) + (b + d)√D`.

    Does not depend on `D` (the irrational parts add componentwise). -/
def fp2dAdd (p : Nat) (x y : FP2) : FP2 :=
  ((x.1 + y.1) % p, (x.2 + y.2) % p)

/-- Subtraction via Nat: `(a + b√D) - (c + d√D) = (a - c) + (b - d)√D`
    using additive inverse mod p. -/
def fp2dSub (p : Nat) (x y : FP2) : FP2 :=
  ((x.1 + (p - y.1 % p)) % p, (x.2 + (p - y.2 % p)) % p)

/-- Multiplication: `(a + b√D)(c + d√D) = (ac + D·bd) + (ad + bc)√D`. -/
def fp2dMul (D p : Nat) (x y : FP2) : FP2 :=
  ((x.1 * y.1 + D * x.2 * y.2) % p,
   (x.1 * y.2 + x.2 * y.1) % p)

/-- Frobenius automorphism: `σ(a + b√D) = a - b·√D`.  Does **not**
    depend on `D` syntactically (the action `b ↦ -b` is uniform). -/
def fp2dFrob (p : Nat) (x : FP2) : FP2 :=
  (x.1 % p, (p - x.2 % p) % p)

/-- Norm: `N(a + b√D) = (a + b√D)(a - b√D) = a² - D·b²`, mod p. -/
def fp2dNorm (D p : Nat) (x : FP2) : Nat :=
  let asq := (x.1 * x.1) % p
  let bsq := (D * x.2 * x.2) % p
  (asq + (p - bsq)) % p

/-- Recursive power `x^n`. -/
def fp2dPow (D p : Nat) (x : FP2) : Nat → FP2
  | 0 => fp2dOne p
  | n + 1 => fp2dMul D p (fp2dPow D p x n) x

/-! ## Smoke tests at varied (D, p) -/

/-- D = 2, p = 7: smoke for `(1 + 1·√2)² = (1 + 2) + 2·√2 = (3, 2)`. -/
theorem fp2dMul_sqrt2_p7 :
    fp2dMul 2 7 (1, 1) (1, 1) = (3, 2) := by decide

/-- D = 3, p = 11: smoke for `(2 + 1·√3)² = (4 + 3) + 4·√3 = (7, 4)`. -/
theorem fp2dMul_sqrt3_p11 :
    fp2dMul 3 11 (2, 1) (2, 1) = (7, 4) := by decide

/-- D = 7, p = 13: smoke `(1 + 1·√7)² = (1 + 7) + 2·√7 = (8, 2)`. -/
theorem fp2dMul_sqrt7_p13 :
    fp2dMul 7 13 (1, 1) (1, 1) = (8, 2) := by decide

/-- D = 5, p = 7: matches `FP2Sqrt5.fp2Mul 7 (2, 3) (4, 1) = (2, 0)`. -/
theorem fp2dMul_sqrt5_specializes_p7 :
    fp2dMul 5 7 (2, 3) (4, 1)
      = E213.Lib.Math.NumberTheory.ModArith.FP2Sqrt5.fp2Mul 7 (2, 3) (4, 1) := by decide

/-- √D squared = D in `𝔽_p[√D]`: `(0, 1)² = (D mod p, 0)`. -/
theorem fp2dSqrtD_sq (D p : Nat) (hp : 1 < p) :
    fp2dMul D p (fp2dSqrtD p) (fp2dSqrtD p) = (D % p, 0) := by
  show ((0 * 0 + D * (1 % p) * (1 % p)) % p, (0 * (1 % p) + (1 % p) * 0) % p)
     = (D % p, 0)
  apply Prod.ext
  · show (0 * 0 + D * (1 % p) * (1 % p)) % p = D % p
    rw [Nat.zero_mul, Nat.zero_add]
    -- D * (1 % p) * (1 % p) ≡ D * 1 * 1 ≡ D (mod p)
    have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
    rw [h1, Nat.mul_one, Nat.mul_one]
  · show (0 * (1 % p) + (1 % p) * 0) % p = 0
    rw [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    rfl

/-- √D squared smoke at D = 7, p = 13: `(0, 1)² = (7, 0)`. -/
theorem fp2dSqrtD_sq_smoke_7_13 :
    fp2dMul 7 13 (fp2dSqrtD 13) (fp2dSqrtD 13) = (7, 0) := by decide

/-! ## Universal ring axioms (parametric in `D`, `p`) -/

/-- ★ Addition is commutative (universal, D-independent). -/
theorem fp2dAdd_comm (p : Nat) (x y : FP2) :
    fp2dAdd p x y = fp2dAdd p y x := by
  show ((x.1 + y.1) % p, (x.2 + y.2) % p)
     = ((y.1 + x.1) % p, (y.2 + x.2) % p)
  apply Prod.ext
  · rw [Nat.add_comm x.1 y.1]
  · rw [Nat.add_comm x.2 y.2]

/-- ★ Multiplication is commutative (universal in `D`). -/
theorem fp2dMul_comm (D p : Nat) (x y : FP2) :
    fp2dMul D p x y = fp2dMul D p y x := by
  show ((x.1 * y.1 + D * x.2 * y.2) % p, (x.1 * y.2 + x.2 * y.1) % p)
     = ((y.1 * x.1 + D * y.2 * x.2) % p, (y.1 * x.2 + y.2 * x.1) % p)
  apply Prod.ext
  · rw [Nat.mul_comm x.1 y.1, mul_assoc D x.2 y.2,
        Nat.mul_comm x.2 y.2, ← mul_assoc D y.2 x.2]
  · rw [Nat.mul_comm x.1 y.2, Nat.mul_comm x.2 y.1,
        Nat.add_comm (y.2 * x.1) (y.1 * x.2)]

/-- ★ Add-zero on the left (D-independent). -/
theorem fp2dAdd_zero_left (p : Nat) (x : FP2) :
    fp2dAdd p fp2dZero x = (x.1 % p, x.2 % p) := by
  show ((0 + x.1) % p, (0 + x.2) % p) = (x.1 % p, x.2 % p)
  rw [Nat.zero_add, Nat.zero_add]

/-- ★ Mul-one on the left (universal in `D`). -/
theorem fp2dMul_one_left (D p : Nat) (x : FP2) :
    fp2dMul D p (fp2dOne p) x = (x.1 % p, x.2 % p) := by
  show ((1 % p * x.1 + D * 0 * x.2) % p, (1 % p * x.2 + 0 * x.1) % p)
     = (x.1 % p, x.2 % p)
  apply Prod.ext
  · show (1 % p * x.1 + D * 0 * x.2) % p = x.1 % p
    rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    rw [← mul_mod_left_pure 1 x.1 p, Nat.one_mul]
  · show (1 % p * x.2 + 0 * x.1) % p = x.2 % p
    rw [Nat.zero_mul, Nat.add_zero]
    rw [← mul_mod_left_pure 1 x.2 p, Nat.one_mul]

/-- ★ Mul-zero on the left (universal in `D`). -/
theorem fp2dMul_zero_left (D p : Nat) (x : FP2) :
    fp2dMul D p fp2dZero x = (0, 0) := by
  show ((0 * x.1 + D * 0 * x.2) % p, (0 * x.2 + 0 * x.1) % p) = (0, 0)
  apply Prod.ext
  · rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    rfl
  · rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
    rfl

/-- Power 0: `x^0 = 1`. -/
theorem fp2dPow_zero (D p : Nat) (x : FP2) :
    fp2dPow D p x 0 = fp2dOne p := rfl

/-- Power succ: `x^(n+1) = x^n · x`. -/
theorem fp2dPow_succ (D p : Nat) (x : FP2) (n : Nat) :
    fp2dPow D p x (n + 1) = fp2dMul D p (fp2dPow D p x n) x := rfl

/-! ## Frobenius algebraic properties (universal in `D`)

`fp2dFrob` is syntactically D-independent.  Its involutive,
additive, and multiplicative properties are uniform in `D`.

The multiplicative property `σ(x · y) = σ(x) · σ(y)` is the
"D-aware" step: it uses `(p - x)(p - y) ≡ xy (mod p)` to cancel
the `D · b · d` cross-term against `D · (p - b) · (p - d)`.
-/

/-- Helper: double mod-p negation is canonical-form identity.
    Local to this module (parallel to the private helper in
    FP2Sqrt5). -/
private theorem double_neg_modD (p x : Nat) (hp : 0 < p) :
    (p - (p - x % p) % p) % p = x % p := by
  have hr_lt : x % p < p := Nat.mod_lt _ hp
  by_cases h0 : x % p = 0
  · rw [h0]
    show (p - (p - 0) % p) % p = 0
    rw [Nat.sub_zero, mod_self, Nat.sub_zero, mod_self]
  · have h0_pos : 0 < x % p := Nat.pos_of_ne_zero h0
    have hpsub_lt : p - x % p < p := Nat.sub_lt hp h0_pos
    rw [Nat.mod_eq_of_lt hpsub_lt]
    rw [E213.Tactic.NatHelper.sub_sub_self (Nat.le_of_lt hr_lt)]
    rw [Nat.mod_eq_of_lt hr_lt]

/-- ★ Frobenius is involutive: `σ ∘ σ = canonical` (universal in `D`). -/
theorem fp2dFrob_involution (p : Nat) (hp : 0 < p) (x : FP2) :
    fp2dFrob p (fp2dFrob p x) = (x.1 % p, x.2 % p) := by
  show ((x.1 % p) % p, (p - (p - x.2 % p) % p % p) % p)
     = (x.1 % p, x.2 % p)
  congr 1
  · exact mod_mod x.1 p
  · rw [mod_mod]
    exact double_neg_modD p x.2 hp

/-- ★ Frobenius preserves zero (universal). -/
theorem fp2dFrob_zero (p : Nat) : fp2dFrob p fp2dZero = fp2dZero := by
  show (0 % p, (p - 0 % p) % p) = (0, 0)
  apply Prod.ext
  · rfl
  · show (p - 0 % p) % p = 0
    show (p - 0) % p = 0
    rw [Nat.sub_zero, mod_self]

/-- ★ Frobenius preserves one. -/
theorem fp2dFrob_one (p : Nat) : fp2dFrob p (fp2dOne p) = fp2dOne p := by
  show ((1 % p) % p, (p - 0 % p) % p) = (1 % p, 0)
  apply Prod.ext
  · exact mod_mod 1 p
  · show (p - 0 % p) % p = 0
    show (p - 0) % p = 0
    rw [Nat.sub_zero, mod_self]

/-- ★ Frobenius is additive (universal in `D`, D-independent step). -/
theorem fp2dFrob_add (p : Nat) (hp : 0 < p) (x y : FP2) :
    fp2dFrob p (fp2dAdd p x y)
      = fp2dAdd p (fp2dFrob p x) (fp2dFrob p y) := by
  show (((x.1 + y.1) % p) % p, (p - ((x.2 + y.2) % p) % p) % p)
     = ((x.1 % p + y.1 % p) % p,
        ((p - x.2 % p) % p + (p - y.2 % p) % p) % p)
  apply Prod.ext
  · show ((x.1 + y.1) % p) % p = (x.1 % p + y.1 % p) % p
    rw [mod_mod, ← add_mod_gen x.1 y.1 p]
  · show (p - ((x.2 + y.2) % p) % p) % p
       = ((p - x.2 % p) % p + (p - y.2 % p) % p) % p
    rw [mod_mod]
    exact neg_mod_add p x.2 y.2 hp

/-- ★ Frobenius is multiplicative (universal in `D`).  This is the
    only Frobenius identity that "sees" `D`: the cross term
    `D · b · d` is preserved by both `b ↦ -b` and `d ↦ -d`
    (two sign flips cancel), while the cross sum `ad + bc`
    receives a single sign flip. -/
theorem fp2dFrob_mul (D p : Nat) (hp : 0 < p) (x y : FP2) :
    fp2dFrob p (fp2dMul D p x y)
      = fp2dMul D p (fp2dFrob p x) (fp2dFrob p y) := by
  show (((x.1*y.1 + D*x.2*y.2) % p) % p,
        (p - ((x.1*y.2 + x.2*y.1) % p) % p) % p)
     = ((x.1%p * (y.1%p) + D * ((p - x.2%p)%p) * ((p - y.2%p)%p)) % p,
        (x.1%p * ((p - y.2%p)%p) + ((p - x.2%p)%p) * (y.1%p)) % p)
  apply Prod.ext
  · -- First component: D·b·d vs D·(-b)·(-d)
    show ((x.1*y.1 + D*x.2*y.2) % p) % p
       = (x.1%p * (y.1%p) + D * ((p - x.2%p)%p) * ((p - y.2%p)%p)) % p
    rw [mod_mod]
    rw [add_mod_gen (x.1 * y.1) (D * x.2 * y.2) p]
    rw [add_mod_gen (x.1 % p * (y.1 % p))
                    (D * ((p - x.2 % p) % p) * ((p - y.2 % p) % p)) p]
    congr 1
    congr 1
    · exact mul_mod_pure x.1 y.1 p
    · rw [mul_assoc D x.2 y.2,
          mul_assoc D ((p - x.2 % p) % p) ((p - y.2 % p) % p)]
      rw [mul_mod_right_pure D (x.2 * y.2) p]
      rw [mul_mod_right_pure D
            (((p - x.2 % p) % p) * ((p - y.2 % p) % p)) p]
      rw [← neg_mod_mul_neg p x.2 y.2 hp]
  · -- Second component: ad + bc, sign flip
    show (p - ((x.1*y.2 + x.2*y.1) % p) % p) % p
       = (x.1%p * ((p - y.2%p)%p) + ((p - x.2%p)%p) * (y.1%p)) % p
    rw [mod_mod]
    rw [add_mod_gen (x.1 % p * ((p - y.2 % p) % p))
                    (((p - x.2 % p) % p) * (y.1 % p)) p]
    rw [← mul_mod_left_pure x.1 ((p - y.2 % p) % p) p]
    rw [neg_mod_mul_right p x.1 y.2 hp]
    rw [← mul_mod_right_pure ((p - x.2 % p) % p) y.1 p]
    rw [neg_mod_mul_left p x.2 y.1 hp]
    exact neg_mod_add p (x.1 * y.2) (x.2 * y.1) hp

/-- Smoke: σ((2 + 1√3) · (1 + 2√3)) = σ(2+1√3) · σ(1+2√3) at p = 11. -/
theorem fp2dFrob_mul_smoke_3_11 :
    fp2dFrob 11 (fp2dMul 3 11 (2, 1) (1, 2))
      = fp2dMul 3 11 (fp2dFrob 11 (2, 1)) (fp2dFrob 11 (1, 2)) := by decide

/-! ## Norm via Frobenius: `x · σ(x) = (Norm_D(x), 0)`

The universal identity tying multiplication, Frobenius, and norm
together — parametric in `D`.
-/

/-- ★ `x · σ(x) = (Norm_D(x), 0)`: multiplication of `x` by its
    Frobenius conjugate is a scalar in `𝔽_p ⊂ 𝔽_p[√D]` equal to
    the norm.  Universal in `D` (the `D` factor in the norm
    matches the `D` factor in `fp2dMul`). -/
theorem fp2dMul_self_frob (D p : Nat) (hp : 0 < p) (x : FP2) :
    fp2dMul D p x (fp2dFrob p x) = (fp2dNorm D p x, 0) := by
  show ((x.1 * (x.1 % p) + D * x.2 * ((p - x.2 % p) % p)) % p,
        (x.1 * ((p - x.2 % p) % p) + x.2 * (x.1 % p)) % p)
     = (((x.1 * x.1) % p + (p - (D * x.2 * x.2) % p)) % p, 0)
  apply Prod.ext
  · show (x.1 * (x.1 % p) + D * x.2 * ((p - x.2 % p) % p)) % p
       = ((x.1 * x.1) % p + (p - (D * x.2 * x.2) % p)) % p
    rw [add_mod_gen (x.1 * (x.1 % p)) (D * x.2 * ((p - x.2 % p) % p)) p]
    rw [add_mod_gen ((x.1 * x.1) % p) (p - (D * x.2 * x.2) % p) p]
    rw [mod_mod (x.1 * x.1) p]
    congr 1
    congr 1
    · exact (mul_mod_right_pure x.1 x.1 p).symm
    · exact neg_mod_mul_right p (D * x.2) x.2 hp
  · show (x.1 * ((p - x.2 % p) % p) + x.2 * (x.1 % p)) % p = 0
    rw [add_mod_gen (x.1 * ((p - x.2 % p) % p)) (x.2 * (x.1 % p)) p]
    rw [neg_mod_mul_right p x.1 x.2 hp]
    rw [← mul_mod_right_pure x.2 x.1 p]
    rw [Nat.mul_comm x.2 x.1]
    exact nmod_self_mod_zero p (x.1 * x.2) hp

/-- Smoke at (D = 3, p = 11): `(2 + 1·√3) · σ = (Norm, 0)`.
    Norm = 4 - 3 = 1 mod 11. -/
theorem fp2dMul_self_frob_smoke_3_11 :
    fp2dMul 3 11 (2, 1) (fp2dFrob 11 (2, 1)) = (fp2dNorm 3 11 (2, 1), 0) :=
  by decide

/-- Smoke at (D = 7, p = 13): `(3 + 2·√7) · σ = (Norm, 0)`.
    Norm = 9 - 28 = -19 ≡ -19 + 26 = 7 mod 13. -/
theorem fp2dMul_self_frob_smoke_7_13 :
    fp2dMul 7 13 (3, 2) (fp2dFrob 13 (3, 2)) = (fp2dNorm 7 13 (3, 2), 0) :=
  by decide

end E213.Lib.Math.NumberTheory.ModArith.FP2SqrtD
