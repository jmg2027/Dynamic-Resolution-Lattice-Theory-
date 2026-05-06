import E213.Term.Tactic.Nat213

/-!
# Polynomial213 — coefficient-array reflection (∅-axiom)

Closes Wallis/Pell-style polynomial identities (one variable over Nat)
without `omega`.  Identities like
  `(4k+1)·4(k+1)² + 1 = (4k+5)·(2k+1)²`
become a single `rfl` after both sides are encoded as `Poly`.

Strict ∅-axiom: avoids propext, Quot.sound, Classical.

(Lives at Math layer, not Kernel, to allow `rw` in soundness proofs.)
-/

namespace E213.Polynomial213

/-- Coefficient array.  `cs[i]` = coefficient of `x^i`.
    `[]` represents the zero polynomial. -/
abbrev Poly := List Nat

/-- Horner evaluation: `eval [a,b,c] x = a + x*(b + x*c)`. -/
def eval : Poly → Nat → Nat
  | [],      _ => 0
  | c :: cs, x => c + x * eval cs x

/-- Constant polynomial. -/
def C (c : Nat) : Poly := [c]

/-- The variable `X`. -/
def X : Poly := [0, 1]

/-- Coefficient-wise addition; pads the shorter list with 0s.
    Pattern matches first arg first, then second — gives unambiguous
    reduction even when one side is a variable. -/
def add : Poly → Poly → Poly
  | [],      q  => q
  | a :: as, q  => match q with
                   | []      => a :: as
                   | b :: bs => (a + b) :: add as bs

/-- Scale every coefficient. -/
def scale (k : Nat) : Poly → Poly
  | []       => []
  | c :: cs  => (k * c) :: scale k cs

/-- Shift by one: multiply by X (prepend 0). -/
def shift (p : Poly) : Poly := 0 :: p

/-- Polynomial multiplication = repeated `add (scale ... shift)`. -/
def mul : Poly → Poly → Poly
  | [],       _ => []
  | a :: as, q => add (scale a q) (shift (mul as q))

/-- Strip trailing zeros to canonical form. -/
def trim : Poly → Poly
  | []       => []
  | c :: cs  =>
    let cs' := trim cs
    match cs' with
    | []       => if c = 0 then [] else [c]
    | _ :: _   => c :: cs'

end E213.Polynomial213
