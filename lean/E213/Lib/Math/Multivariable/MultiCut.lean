import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Real213.CutSum

/-!
# Multivariable — `MultiCut n` (n-dimensional point)

An n-dimensional point in 213 is a tuple of n cuts:

  `MultiCut n := Fin n → Cut`

This file: vector arithmetic + canonical points + `update`.

213-native: no real ℝⁿ needed; just `Fin n` indexing.  All operations
are pointwise on `Cut`s (= `Nat → Nat → Bool`), which means
addition, scaling, etc. all reduce to existing Real213 operations.
-/

namespace E213.Lib.Math.Multivariable.MultiCut

open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Real213.CutSum (cutSum)

/-- An n-dimensional point: tuple of n cuts. -/
abbrev MultiCut (n : Nat) := Fin n → (Nat → Nat → Bool)

/-- Constant point: every coordinate is `c`. -/
def constMC (n : Nat) (c : Nat → Nat → Bool) : MultiCut n :=
  fun _ => c

/-- Origin (every coordinate is 0/1). -/
def zero (n : Nat) : MultiCut n := constMC n (constCut 0 1)

/-- All-ones point. -/
def one (n : Nat) : MultiCut n := constMC n (constCut 1 1)

/-- Update i-th coordinate. -/
def update {n : Nat} (x : MultiCut n) (i : Fin n) (c : Nat → Nat → Bool) :
    MultiCut n :=
  fun j => if i = j then c else x j

/-- Vector addition: pointwise `cutSum`. -/
def multiAdd {n : Nat} (x y : MultiCut n) : MultiCut n :=
  fun i => cutSum (x i) (y i)

/-- Zero is identity for multiAdd at coordinate `i` (rfl-after-cutSum). -/
theorem multiAdd_zero_left_at {n : Nat} (x : MultiCut n) (i : Fin n)
    (m k : Nat) :
    multiAdd (zero n) x i m k = cutSum (constCut 0 1) (x i) m k := rfl

/-- `update` of `i` with `c` at index `i` returns `c`. -/
theorem update_self {n : Nat} (x : MultiCut n) (i : Fin n)
    (c : Nat → Nat → Bool) :
    update x i c i = c := by
  show (if i = i then c else x i) = c
  rw [if_pos rfl]

/-- Origin is the constMC at zero (rfl). -/
theorem zero_eq_const : zero 5 = constMC 5 (constCut 0 1) := rfl

/-- 1-cube origin — all coordinates 0/1. -/
theorem zero_at_index (i : Fin 5) :
    zero 5 i = constCut 0 1 := rfl

/-- 1-cube top — all coordinates 1/1. -/
theorem one_at_index (i : Fin 5) :
    one 5 i = constCut 1 1 := rfl

end E213.Lib.Math.Multivariable.MultiCut
