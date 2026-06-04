import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order

/-!
# PolyRoot/FactorTheorem — the factor theorem over `ℤ` (synthetic division)

Toward Lagrange's root bound ("a degree-`d` polynomial over `ℤ/p` has `≤ d` roots") — the
classical input gating the Eisenstein split converse.

A polynomial is a coefficient list `[a₀, …, aₙ]` (head = constant), evaluated by Horner.
The synthetic-division quotient `quot r` by `(X − r)` (using only `+`, `×`) has degree one
lower (`quot_length`), and the **factor identity** holds over `ℤ`:

  `eval f x − eval f r = (x − r) · eval (quot r f) x`.

  * `eval`, `quot` — evaluation and synthetic-division quotient.
  * `quot_length` — `(quot r f).length = f.length − 1`.
  * ★★★ `factor_eval` — the factor identity (induction on the coefficient list).
  * `eval_cons`, `eval_nil` — evaluation unfolding.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PolyRoot

/-- Horner evaluation of a coefficient list (head = constant term). -/
def eval : List Int → Int → Int
  | [], _ => 0
  | a :: as, x => a + x * eval as x

theorem eval_nil (x : Int) : eval [] x = 0 := rfl
theorem eval_cons (a : Int) (as : List Int) (x : Int) :
    eval (a :: as) x = a + x * eval as x := rfl

/-- Synthetic-division quotient of `f` by `(X − r)` — degree one lower (head = constant). -/
def quot (r : Int) : List Int → List Int
  | [] => []
  | [_] => []
  | a :: b :: bs => eval (b :: bs) r :: quot r (b :: bs)

/-- `(quot r f).length = f.length − 1`. -/
theorem quot_length (r : Int) : ∀ f : List Int, (quot r f).length = f.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b :: bs => by
    show (eval (b :: bs) r :: quot r (b :: bs)).length = (b :: bs).length + 1 - 1
    rw [List.length_cons, quot_length r (b :: bs)]
    rfl

/-- ★★★ **The factor identity.**  `eval f x − eval f r = (x − r) · eval (quot r f) x` over `ℤ`. -/
theorem factor_eval (r : Int) : ∀ (f : List Int) (x : Int),
    eval f x - eval f r = (x - r) * eval (quot r f) x := by
  intro f
  induction f with
  | nil =>
    intro x
    show (0 : Int) - 0 = (x - r) * 0
    rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.Order.sub_zero]
  | cons a as ih =>
    cases as with
    | nil =>
      intro x
      show (a + x * eval [] x) - (a + r * eval [] r) = (x - r) * 0
      rw [eval_nil, eval_nil, E213.Meta.Int213.PolyIntM.mul_zeroZ,
          E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.PolyIntM.mul_zeroZ]
      exact E213.Meta.Int213.Order.sub_self_zero (a + 0)
    | cons b bs =>
      intro x
      show (a + x * eval (b :: bs) x) - (a + r * eval (b :: bs) r)
         = (x - r) * (eval (b :: bs) r + x * eval (quot r (b :: bs)) x)
      have hax : eval (b :: bs) x
          = eval (b :: bs) r + (x - r) * eval (quot r (b :: bs)) x := by
        rw [← ih x]; ring_intZ
      rw [hax]; ring_intZ

end E213.Lib.Math.NumberTheory.PolyRoot
