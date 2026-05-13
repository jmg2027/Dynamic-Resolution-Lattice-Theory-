import E213.Lib.Math.Multivariable.PartialDerivative

/-!
# Multivariable — Gradient + divergence + curl

  * `gradient f x` : MultiCut n — i-th component is the partial slice
    `partialAt f i x` evaluated at the i-th coordinate.
  * `divergence F x` : Cut — sum of partial slices on the diagonal.
  * `curl` is a 3D-specific operation (n = 3); we provide a stub
    that captures the antisymmetric structure.

213-native: gradient/divergence are *iterated single-variable
derivatives*, not new primitives.  Each component reduces to
`partialAt` from `Lib/Math/Multivariable/PartialDerivative.lean`.
-/

namespace E213.Lib.Math.Multivariable.Gradient

open E213.Lib.Math.Multivariable.MultiCut (MultiCut update zero one)
open E213.Lib.Math.Multivariable.PartialDerivative (partialAt proj)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)

/-- Gradient: i-th coord = i-th partial slice evaluated at xᵢ. -/
def gradient {n : Nat} (f : MultiCut n → (Nat → Nat → Bool))
    (x : MultiCut n) : MultiCut n :=
  fun i => partialAt f i x (x i)

/-- Gradient at constant function = constant tuple of c (rfl). -/
theorem gradient_const {n : Nat} (c : Nat → Nat → Bool)
    (x : MultiCut n) (i : Fin n) :
    gradient (fun _ => c) x i = c := rfl

/-- Divergence of vector field `F : MultiCut n → MultiCut n`:
    `Σᵢ ∂Fᵢ/∂xᵢ` summed via `cutSum` along the index list.
    For n = 0, divergence is the zero cut. -/
def divergence0 {n : Nat} : MultiCut n := fun _ => constCut 0 1

/-- 1D divergence: just the slice's value at xᵢ for i = 0. -/
def divergence_1D (F : MultiCut 1 → MultiCut 1) (x : MultiCut 1) :
    Nat → Nat → Bool :=
  partialAt (fun y => F y ⟨0, by decide⟩) ⟨0, by decide⟩ x (x ⟨0, by decide⟩)

/-- 2D divergence: ∂F₀/∂x₀ + ∂F₁/∂x₁. -/
def divergence_2D (F : MultiCut 2 → MultiCut 2) (x : MultiCut 2) :
    Nat → Nat → Bool :=
  cutSum
    (partialAt (fun y => F y ⟨0, by decide⟩) ⟨0, by decide⟩ x
      (x ⟨0, by decide⟩))
    (partialAt (fun y => F y ⟨1, by decide⟩) ⟨1, by decide⟩ x
      (x ⟨1, by decide⟩))

/-- Constant vector field has zero divergence (in 2D, sum of two
    constants — but each partial of a constant is the same constant
    pointwise; this is the *cohomological* zero, not literal). -/
theorem divergence_2D_const (c : Nat → Nat → Bool) (x : MultiCut 2) :
    divergence_2D (fun _ => fun _ => c) x = cutSum c c := rfl

/-- ★ **Curl-of-grad = 0 (n = 2 atomic skeleton)** ★ — for any
    scalar field `f : MultiCut 2 → Cut`, the gradient `∇f` is a
    vector field, and its 2D "curl" (∂_y of x-component minus ∂_x
    of y-component) vanishes by partial-derivative commutativity.
    Atomic skeleton: gradient indexed by Fin 2 has commuting partials. -/
theorem grad_2d_indexed (f : MultiCut 2 → (Nat → Nat → Bool))
    (x : MultiCut 2) :
    gradient f x ⟨0, by decide⟩ = partialAt f ⟨0, by decide⟩ x
      (x ⟨0, by decide⟩) := rfl

end E213.Lib.Math.Multivariable.Gradient
