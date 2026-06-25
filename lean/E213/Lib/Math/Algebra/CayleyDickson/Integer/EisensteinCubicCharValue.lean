import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Meta.Int213.PolyIntMTactic

/-!
# The cubic character's value is exactly `1`, `ω`, or `ω²` (rung 3c-value, ∅-axiom)

★★★★★ `cube_one_value` : in `ℤ[ω]/(d)` with `‖d‖² = p` prime, anything cubing to `1` is one of the
three cube roots of unity:

  `y³ ≡ 1 (mod d)  ⟹  y ≡ 1  ∨  y ≡ ω  ∨  y ≡ ω²  (mod d)`.

Combined with `EisensteinCubicChar.char_cubes_to_one` (the half-power `χ(α) = α^m` cubes to `1`), the
capstone `cubic_char_value` reads the cubic character **exactly into `μ₃ = {1, ω, ω²}`** — closing the
value-group leg of `(·/d)₃` left open at rung 3b ("cubes to 1" → "*is* one of the three").

## The two ingredients

1. **The factorization** `cubic_factor` (∅-axiom ring identity, `ext` + `ring_intZ` on each component
   after expanding the Eisenstein multiplication; the cube-root relation `ω²+ω+1=0`, `ω³=1` is baked
   into the numeric components `ω=⟨0,1⟩`, `ω²=⟨-1,-1⟩`):

     `y³ − 1 = (y − 1)·((y − ω)·(y − ω²))`.

2. **The integral domain** `EisensteinPrime.residue_no_zero_divisors` (`d` prime ⟹ `ℤ[ω]/(d)` has no
   zero divisors).  `y³ ≡ 1` means `d ∣ (y−1)(y−ω)(y−ω²)`; applying the no-zero-divisors law twice
   across the triple product forces one factor `≡ 0 (mod d)`, i.e. `y ≡ 1, ω,` or `ω²`.

No excluded middle (the domain law is itself a constructive disjunction).  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharValue

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime (residue_no_zero_divisors)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (char_cubes_to_one)
open E213.Meta.Algebra213.Ring213 (add_zero)

/-! ## §0 — component projections of the Eisenstein arithmetic (all `rfl`, for `ring_intZ`) -/

private theorem mul_re (u v : ZOmega) : (u * v).re = u.re * v.re - u.im * v.im := rfl
private theorem mul_im (u v : ZOmega) : (u * v).im = u.re * v.im + u.im * v.re - u.im * v.im := rfl
private theorem add_re (u v : ZOmega) : (u + v).re = u.re + v.re := rfl
private theorem add_im (u v : ZOmega) : (u + v).im = u.im + v.im := rfl
private theorem neg_re (u : ZOmega) : (-u).re = -u.re := rfl
private theorem neg_im (u : ZOmega) : (-u).im = -u.im := rfl
private theorem Omega_re : Omega.re = 0 := rfl
private theorem Omega_im : Omega.im = 1 := rfl
private theorem Omega2_re : Omega2.re = -1 := rfl
private theorem Omega2_im : Omega2.im = -1 := rfl
private theorem ofInt_re (n : Int) : (ofInt n).re = n := rfl
private theorem ofInt_im (n : Int) : (ofInt n).im = 0 := rfl

/-- **The cubic factorization** `y³ − 1 = (y − 1)·((y − ω)·(y − ω²))` in `ℤ[ω]`.  `ext` to the two
    integer components, expand the Eisenstein product, fold the zero/double-negation constants
    (`Int.neg_zero`/`add_zero`/`neg_neg`, all ∅-axiom), then `ring_intZ`.  The cube-root relation
    `ω² + ω + 1 = 0` is carried by the numeric coordinates of `ω, ω²`. -/
theorem cubic_factor (y : ZOmega) :
    y * y * y + -(ofInt 1) = (y + -(ofInt 1)) * ((y + -Omega) * (y + -Omega2)) := by
  apply ext <;>
    simp only [mul_re, mul_im, add_re, add_im, neg_re, neg_im,
      Omega_re, Omega_im, Omega2_re, Omega2_im, ofInt_re, ofInt_im,
      Int.neg_zero, Int.add_zero, Int.neg_neg] <;>
    ring_intZ

/-! ## §1 — `ModEq · 0` bookkeeping (`ModEq d x 0 = d ∣ x`, since `x + -0 = x`) -/

private theorem hz0 : (-(0 : ZOmega)) = 0 := by decide

/-- `ModEq d (a + -b) 0 ⟹ ModEq d a b` — both are `d ∣ (a + -b)` (the `-0` drops). -/
private theorem modEq_of_sub_zero {d a b : ZOmega} (h : ModEq d (a + -b) 0) : ModEq d a b := by
  have h2 : d ∣ ((a + -b) + -0) := h
  rw [hz0, add_zero] at h2
  exact h2

/-- `d ∣ x ⟹ ModEq d x 0` — package a divisibility as a `ModEq · 0`. -/
private theorem modEq_zero_of_dvd {d x : ZOmega} (h : d ∣ x) : ModEq d x 0 := by
  show d ∣ (x + -0)
  rw [hz0, add_zero]; exact h

/-! ## §2 — the value lands in `μ₃` -/

/-- ★★★★★ **A cube root of unity in `ℤ[ω]/(d)` is `1`, `ω`, or `ω²`.**  For `‖d‖² = p` prime,
    `y³ ≡ 1 (mod d)` forces `y ≡ 1 ∨ y ≡ ω ∨ y ≡ ω² (mod d)`.  `cubic_factor` turns `d ∣ (y³ − 1)`
    into `d ∣ (y−1)·((y−ω)·(y−ω²))`; `residue_no_zero_divisors` applied twice splits the triple
    product.  ∅-axiom. -/
theorem cube_one_value {d y : ZOmega} {p : Nat}
    (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p) (hp1 : 1 < p) (hd : d.normSq = (p : Int))
    (hcube : ModEq d (y * y * y) (ofInt 1)) :
    ModEq d y (ofInt 1) ∨ ModEq d y Omega ∨ ModEq d y Omega2 := by
  have hdvd : d ∣ ((y + -(ofInt 1)) * ((y + -Omega) * (y + -Omega2))) := by
    have h1 : d ∣ (y * y * y + -(ofInt 1)) := hcube
    rwa [cubic_factor y] at h1
  rcases residue_no_zero_divisors hpr hp1 hd (modEq_zero_of_dvd hdvd) with hA | hBC
  · exact Or.inl (modEq_of_sub_zero hA)
  · rcases residue_no_zero_divisors hpr hp1 hd hBC with hO | hO2
    · exact Or.inr (Or.inl (modEq_of_sub_zero hO))
    · exact Or.inr (Or.inr (modEq_of_sub_zero hO2))

/-- ★★★★★ **The cubic character is `μ₃`-valued** — for the residue prime `d` (`‖d‖² = p ≡ 1 mod 3`),
    the half-power `χ(α) = α^m` (`m = (p−1)/3`, `3m = m+m+m`) of **any** `α ∈ ℤ[ω]` is congruent mod
    `d` to exactly one of `1, ω, ω²`:

      `χ(α) ≡ 1  ∨  χ(α) ≡ ω  ∨  χ(α) ≡ ω²  (mod d)`.

    `char_cubes_to_one` gives `χ(α)³ ≡ 1`; `cube_one_value` reads off the value.  This closes the
    value-group leg of the cubic character `(·/d)₃`.  ∅-axiom. -/
theorem cubic_char_value {α d : ZOmega} {x : Int} {m p : Nat}
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (hp1 : 1 < p) (hd : d.normSq = (p : Int))
    (hred : ModEq d α (ofInt (α.re + α.im * x)))
    (hferm : d.normSq ∣ ((α.re + α.im * x) ^ (m + m + m) - 1)) :
    ModEq d (pow α m) (ofInt 1) ∨ ModEq d (pow α m) Omega ∨ ModEq d (pow α m) Omega2 :=
  cube_one_value hpr hp1 hd (char_cubes_to_one hred hferm)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharValue
