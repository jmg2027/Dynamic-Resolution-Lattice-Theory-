import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order

/-!
# PolyRoot/FactorTheorem — the factor theorem over `ℤ` (synthetic division)

Toward Lagrange's root bound ("a degree-`d` polynomial over `ℤ/p` has `≤ d` roots") — the
single classical input gating the Eisenstein split converse (`p ≡ 1 mod 3 ⟹ ∃ x, p ∣ x²+x+1`).

A polynomial is a coefficient list `[a₀, a₁, …, aₙ]` (head = constant term), evaluated by
Horner.  Synthetic division by `(X − r)` (`quot r`) uses only `+` and `×` (no division), and
the **factor identity** holds over `ℤ`:

  `eval f x − eval f r = (x − r) · eval (quot r f) x`.

So if `r` is a root (`eval f r = 0`), `eval f x = (x − r) · eval (quot r f) x` — the factor
`(X − r)` divides `f`, and `quot r f` has one lower degree.

  * `eval`, `quot` — evaluation and synthetic-division quotient.
  * ★★★ `factor_eval` — the factor identity (by induction on the coefficient list).

(Note: this `quot` keeps the list length — its top coefficient is a spurious `0` — so the
root-bound induction tracks an *effective degree* separately.)

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PolyRoot

/-- Horner evaluation of a coefficient list (head = constant term). -/
def eval : List Int → Int → Int
  | [], _ => 0
  | a :: as, x => a + x * eval as x

/-- Synthetic-division quotient of `f` by `(X − r)` (head = constant term). -/
def quot (r : Int) : List Int → List Int
  | [] => []
  | _ :: as => eval as r :: quot r as

/-- ★★★ **The factor identity.**  `eval f x − eval f r = (x − r) · eval (quot r f) x` over
    `ℤ`, by induction on the coefficient list.  (When `r` is a root, `(X − r) ∣ f`.) -/
theorem factor_eval (r : Int) : ∀ (f : List Int) (x : Int),
    eval f x - eval f r = (x - r) * eval (quot r f) x := by
  intro f
  induction f with
  | nil =>
    intro x
    show (0 : Int) - 0 = (x - r) * 0
    rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.Order.sub_zero]
  | cons a as ih =>
    intro x
    show (a + x * eval as x) - (a + r * eval as r)
       = (x - r) * (eval as r + x * eval (quot r as) x)
    have hax : eval as x = eval as r + (x - r) * eval (quot r as) x := by
      rw [← ih x]; ring_intZ
    rw [hax]; ring_intZ

end E213.Lib.Math.NumberTheory.PolyRoot
