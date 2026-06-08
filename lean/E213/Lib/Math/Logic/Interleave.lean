import E213.Lib.Math.Logic.Omniscience

/-!
# Reverse Mathematics 213 — GB-cont4 infrastructure: even/odd interleave + first-true

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`), toward **selection from LLPO**
(the headline open piece — tightening the König child-selection cost from LPO to LLPO).

To apply the even/odd `LLPO` to a *pair* of streams, one needs to interleave them into one
stream whose even part is the first and odd part is the second.  The obvious encoding via
`n / 2` / `n % 2` pulls `propext` in this Mathlib-free kernel; this file gives a **div/mod-
free** structural interleave (recursing two steps at a time) with the exact extraction
equations `il_even`/`il_odd`, plus the `ftrue` (rising-edge / first-true) machinery and the
back-conversion `ftrue_all_false`.  These are the reusable, ∅-axiom building blocks the
`selection ⟸ LLPO` proof sits on (the remaining crux is the monotone at-most-one argument;
see `books/math/reverse-math-213.md`).
-/

namespace E213.Lib.Math.Logic

/-- Div/mod-free even/odd interleave: `interleave a b (2k) = a k`, `(2k+1) = b k`.
    Recurses two indices at a time, shifting both streams. -/
def interleave (a b : Nat → Bool) : Nat → Bool
  | 0     => a 0
  | 1     => b 0
  | n + 2 => interleave (fun k => a (k + 1)) (fun k => b (k + 1)) n

/-- The even part is the first stream. -/
theorem il_even : ∀ k (a b : Nat → Bool), interleave a b (2 * k) = a k
  | 0,     _, _ => rfl
  | k + 1, a, b => il_even k (fun j => a (j + 1)) (fun j => b (j + 1))

/-- The odd part is the second stream. -/
theorem il_odd : ∀ k (a b : Nat → Bool), interleave a b (2 * k + 1) = b k
  | 0,     _, _ => rfl
  | k + 1, a, b => il_odd k (fun j => a (j + 1)) (fun j => b (j + 1))

/-- The rising-edge stream of `f`: `true` exactly where `f` turns from `false` to `true`. -/
def ftrue (f : Nat → Bool) : Nat → Bool
  | 0     => f 0
  | n + 1 => f (n + 1) && !(f n)

theorem and_self_true : ∀ b : Bool, (b && true) = b
  | false => rfl
  | true  => rfl

/-- If `f` never has a rising edge, it is everywhere false (by induction — no monotonicity
    needed): the back-conversion from `∀ ftrue f = false` to `∀ f = false`. -/
theorem ftrue_all_false (f : Nat → Bool) (h : ∀ k, ftrue f k = false) : ∀ n, f n = false
  | 0     => h 0
  | n + 1 =>
    have ih : f n = false := ftrue_all_false f h n
    have hnot : (!(f n)) = true := congrArg (fun x => !x) ih
    (and_self_true (f (n + 1))).symm.trans
      ((congrArg (fun x => f (n + 1) && x) hnot).symm.trans (h (n + 1)))

end E213.Lib.Math.Logic
