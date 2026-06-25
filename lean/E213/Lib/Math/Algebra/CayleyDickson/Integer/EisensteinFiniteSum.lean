import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaAlgebra213

/-!
# Finite sums in `ℤ[ω]` — the substrate for Gauss / Jacobi character sums (∅-axiom)

`sumRange f n = Σ_{k=0}^{n-1} f k` for a `ZOmega`-valued sequence `f`, with the linearity toolkit
(`sum_add`, `sum_mul_left`, `sum_congr`, `sum_zero_fun`).  This is the generic finite-sum machinery the
specialised geometric sum (`RootOfUnityOrthogonality.geomSum`) is an instance of, and the algebraic
base for the **Gauss sum** `g(χ) = Σ χ(t)ζ^t` and **Jacobi sum** `J(χ,χ) = Σ χ(t)χ(1−t)` of cubic
reciprocity.  All lemmas are clean ring inductions, ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Meta.Algebra213.Ring213 (add_assoc add_comm add_zero zero_add add_4_swap_mid mul_add mul_zero)

/-- `Σ_{k=0}^{n-1} f k` (left fold, `n = 0` empty). -/
def sumRange (f : Nat → ZOmega) : Nat → ZOmega
  | 0     => 0
  | n + 1 => sumRange f n + f n

@[simp] theorem sumRange_zero (f : Nat → ZOmega) : sumRange f 0 = 0 := rfl
theorem sumRange_succ (f : Nat → ZOmega) (n : Nat) :
    sumRange f (n + 1) = sumRange f n + f n := rfl

/-- The zero sequence sums to `0`. -/
theorem sum_zero_fun (n : Nat) : sumRange (fun _ => (0 : ZOmega)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, ih, add_zero]

/-- **Additivity** — `Σ (f + g) = Σ f + Σ g`. -/
theorem sum_add (f g : Nat → ZOmega) (n : Nat) :
    sumRange (fun k => f k + g k) n = sumRange f n + sumRange g n := by
  induction n with
  | zero => show (0 : ZOmega) = 0 + 0; rw [add_zero]
  | succ n ih =>
      show sumRange (fun k => f k + g k) n + (f n + g n) = (sumRange f n + f n) + (sumRange g n + g n)
      rw [ih, add_4_swap_mid]

/-- **Left scalar factor** — `Σ (c · f) = c · Σ f`. -/
theorem sum_mul_left (c : ZOmega) (f : Nat → ZOmega) (n : Nat) :
    sumRange (fun k => c * f k) n = c * sumRange f n := by
  induction n with
  | zero => show (0 : ZOmega) = c * 0; rw [mul_zero]
  | succ n ih =>
      show sumRange (fun k => c * f k) n + c * f n = c * (sumRange f n + f n)
      rw [ih, mul_add]

/-- **Congruence** — sequences agreeing on `[0, n)` have equal sums. -/
theorem sum_congr {f g : Nat → ZOmega} (n : Nat) (h : ∀ k, k < n → f k = g k) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumRange_succ, sumRange_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
          h n (Nat.lt_succ_self n)]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
