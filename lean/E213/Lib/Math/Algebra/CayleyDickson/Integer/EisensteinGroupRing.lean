import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum

/-!
# The group ring `ℤ[ω][C_p]` for the cubic Gauss sum (∅-axiom, Phase A3 / route b)

The additive-character carrier the Gauss sum `g(χ) = Σ_t χ_ω(t)·ζ^t` lives in.  Rather than build the
cyclotomic quotient `ℤ[ζ_p]`, we work in the **free group ring** `R[C_p]` (`R = ℤ[ω]`, `C_p = ℤ/p`):
an element is a **coefficient function** `Nat → ℤ[ω]` (index read mod `p`), the basis is `ζ^i = e_i`,
and multiplication is **convolution**

  `(f ⋆ g)(k) = Σ_{i<p} f(i)·g((k − i) mod p)`   (`conv`).

To stay ∅-axiom we never compare *elements* (function equality would need `funext`, which is
`Quot`-backed); **every identity is a coefficient equation** `(… )(k) = …`.  This file gives `conv` and
its bilinearity (`conv_add_right`, `conv_scalar_left`) — the algebra for `g(χ)·conj g(χ) = p·1 − N` and
the `e_1`-coefficient extraction giving `N(J)=p` (`research-notes/frontiers/higher_reciprocity_roadmap.md`,
A3 route b).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sum_add sum_mul_left sum_congr)
open E213.Meta.Algebra213.Ring213 (mul_add add_mul)

/-- Convolution in the group ring `R[C_p]`: `(f ⋆ g)(k) = Σ_{i<p} f(i)·g((k − i) mod p)`.
    (`(k + p − i) % p = (k − i) mod p` for `i < p ≤ k + p`, stays in `ℕ`.) -/
def conv (p : Nat) (f g : Nat → ZOmega) (k : Nat) : ZOmega :=
  sumRange (fun i => f i * g ((k + p - i) % p)) p

/-- ★★★ **Right-additivity of convolution** — `f ⋆ (g + h) = f ⋆ g + f ⋆ h` (coefficientwise).
    `mul_add` termwise, then `sum_add`. -/
theorem conv_add_right (p : Nat) (f g h : Nat → ZOmega) (k : Nat) :
    conv p f (fun j => g j + h j) k = conv p f g k + conv p f h k := by
  show sumRange (fun i => f i * (g ((k + p - i) % p) + h ((k + p - i) % p))) p
     = sumRange (fun i => f i * g ((k + p - i) % p)) p
       + sumRange (fun i => f i * h ((k + p - i) % p)) p
  rw [← sum_add]
  exact sum_congr p (fun i _ => mul_add (f i) (g ((k + p - i) % p)) (h ((k + p - i) % p)))

/-- ★★★ **Left-additivity of convolution** — `(f + g) ⋆ h = f ⋆ h + g ⋆ h` (coefficientwise).
    `add_mul` termwise, then `sum_add`.  The sibling of `conv_add_right`; together they give the
    bilinearity used to expand `(A+B) ⋆ (A+B)` in the norm identity `N ⋆ N = p · N`. -/
theorem conv_add_left (p : Nat) (f g h : Nat → ZOmega) (k : Nat) :
    conv p (fun i => f i + g i) h k = conv p f h k + conv p g h k := by
  show sumRange (fun i => (f i + g i) * h ((k + p - i) % p)) p
     = sumRange (fun i => f i * h ((k + p - i) % p)) p
       + sumRange (fun i => g i * h ((k + p - i) % p)) p
  rw [← sum_add]
  exact sum_congr p (fun i _ => add_mul (f i) (g i) (h ((k + p - i) % p)))

/-- ★★★ **Left scalar pull** — `(c · f) ⋆ g = c · (f ⋆ g)` (coefficientwise).  `mul_assoc` termwise,
    then `sum_mul_left`. -/
theorem conv_scalar_left (p : Nat) (c : ZOmega) (f g : Nat → ZOmega) (k : Nat) :
    conv p (fun i => c * f i) g k = c * conv p f g k := by
  show sumRange (fun i => c * f i * g ((k + p - i) % p)) p
     = c * sumRange (fun i => f i * g ((k + p - i) % p)) p
  rw [← sum_mul_left]
  exact sum_congr p (fun i _ =>
    E213.Meta.Algebra213.Ring213.mul_assoc c (f i) (g ((k + p - i) % p)))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
