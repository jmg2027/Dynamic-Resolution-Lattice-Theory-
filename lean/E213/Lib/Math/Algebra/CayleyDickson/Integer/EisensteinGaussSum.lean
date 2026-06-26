import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatRing213

/-!
# The cubic Gauss sum `g(χ) = Σ_t χ_ω(t)·ζ^t` in the group ring (∅-axiom)

The Gauss sum and its conjugate as **coefficient functions** in the free group ring `R[C_p]`
(`EisensteinGroupRing`):

  `gauss(t)      = χ_ω(t)`            (coefficient of `ζ^t` in `g(χ)`),
  `gaussConj(k)  = conj χ_ω((p−k)%p)` (coefficient of `ζ^k` in `conj g(χ) = Σ_t χ̄_ω(t)ζ^{−t}`).

Toward the norm identity `g·conj g = p·1 − N` whose `e_1`-coefficient gives `N(J)=p`.  This file sets up
the definitions and the **diagonal index simplification** `conv_diag_index` (the `k=0` convolution term
reduces to `χ_ω(i)·conj χ_ω(i)`), with the pure `ℕ`-helpers it needs.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega chiOmega_mul_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex (chiOmega_ne_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (ofInt_add)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sumRange_succ sum_congr)
open E213.Meta.Nat.AddMod213 (mod_self)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel nat_add_sub_self_right)
open E213.Meta.Algebra213.Ring213 (zero_mul add_zero)

/-- **Pure `p − (p − i) = i`** for `i ≤ p` (`Nat.sub_sub_self` is `propext`-dirty). -/
private theorem sub_sub_self_pure {i p : Nat} (h : i ≤ p) : p - (p - i) = i := by
  have key : i + (p - i) = p := by rw [Nat.add_comm]; exact nat_sub_add_cancel h
  calc p - (p - i) = (i + (p - i)) - (p - i) := by rw [key]
    _ = i := nat_add_sub_self_right i (p - i)

/-- The `k=0` convolution index collapses to the diagonal: `(p − (0 + p − i)%p)%p = i` for `i < p`. -/
theorem conv_diag_index {p i : Nat} (hi : i < p) : (p - (0 + p - i) % p) % p = i := by
  rw [Nat.zero_add]
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    rw [Nat.sub_zero, mod_self, Nat.sub_zero, mod_self]
  · have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    rw [Nat.mod_eq_of_lt (Nat.sub_lt hp hpos), sub_sub_self_pure (Nat.le_of_lt hi),
        Nat.mod_eq_of_lt hi]

/-- The cubic Gauss sum coefficient function: `g(χ) = Σ_t χ_ω(t)·ζ^t`, coefficient `χ_ω(t)` at `ζ^t`. -/
def gauss (p m x : Nat) : Nat → ZOmega := fun t => chiOmega p m x t

/-- The conjugate Gauss sum coefficient function: `conj g(χ) = Σ_t χ̄_ω(t)·ζ^{−t}`, coefficient
    `conj χ_ω((p−k)%p)` at `ζ^k`. -/
def gaussConj (p m x : Nat) : Nat → ZOmega := fun k => conj (chiOmega p m x ((p - k) % p))

/-- ★★★ **The diagonal convolution term** — for `i < p`, the `k=0` term `gauss(i)·gaussConj((0+p−i)%p)`
    equals `χ_ω(i)·conj χ_ω(i)`.  `conv_diag_index` collapses the double `mod`.  ∅-axiom. -/
theorem gauss_diag_term {p m x i : Nat} (hi : i < p) :
    gauss p m x i * gaussConj p m x ((0 + p - i) % p) = chiOmega p m x i * conj (chiOmega p m x i) := by
  show chiOmega p m x i * conj (chiOmega p m x ((p - (0 + p - i) % p) % p))
     = chiOmega p m x i * conj (chiOmega p m x i)
  rw [conv_diag_index hi]

/-- **The diagonal sum counts the units** — `Σ_{i<n} χ_ω(i)·conj χ_ω(i) = ↑(n−1)` for `n ≤ p`: the
    `i=0` term is `0`, each `0<i<n≤p` term is `1` (`chiOmega_mul_conj` + `chiOmega_ne_zero`), so the
    sum is the count `n−1`.  ∅-axiom. -/
private theorem diag_count (p m x : Nat) : ∀ n, n ≤ p →
    sumRange (fun i => chiOmega p m x i * conj (chiOmega p m x i)) n = ofInt (((n - 1 : Nat)) : Int)
  | 0, _ => rfl
  | n + 1, hn => by
      rw [sumRange_succ, diag_count p m x n (Nat.le_of_succ_le hn)]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩]
        show ofInt ((0 : Nat) : Int) + (0 : ZOmega) * conj (0 : ZOmega) = ofInt (((0 : Nat)) : Int)
        rw [zero_mul, add_zero]
      · have hnp : n < p := Nat.lt_of_succ_le hn
        rw [chiOmega_mul_conj p m x n (chiOmega_ne_zero p m x n hpos hnp), ofInt_add]
        show ofInt ((((n - 1 : Nat)) : Int) + 1) = ofInt (((n : Nat)) : Int)
        have hc : (((n - 1 : Nat)) : Int) + 1 = ((n : Nat) : Int) := by
          rw [show (1 : Int) = (((1 : Nat)) : Int) from rfl,
              show (((n - 1 : Nat)) : Int) + (((1 : Nat)) : Int) = ((((n - 1) + 1 : Nat)) : Int) from rfl,
              nat_sub_add_cancel hpos]
        rw [hc]

/-- ★★★★ **The `k=0` (diagonal) coefficient of `g·conj g`** — `(g ⋆ conj g)(0) = ↑(p−1)`.  The double
    `mod` collapses to the diagonal (`gauss_diag_term`); the sum counts the `p−1` units (`diag_count`).
    This is the `e_0`-coefficient `p−1` of `g·conj g = p·1 − N`.  ∅-axiom. -/
theorem gauss_conj_zero (p m x : Nat) :
    conv p (gauss p m x) (gaussConj p m x) 0 = ofInt (((p - 1 : Nat)) : Int) := by
  show sumRange (fun i => gauss p m x i * gaussConj p m x ((0 + p - i) % p)) p
     = ofInt (((p - 1 : Nat)) : Int)
  rw [sum_congr p (fun i hi => gauss_diag_term hi)]
  exact diag_count p m x p (Nat.le_refl p)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum
