import E213.Math.Tactic.IntSquare

open E213.Tactic

example (a : Int) : 0 ≤ a * a := by int_square
example (a : Int) : a * a = 0 ↔ a = 0 := by int_square
example (b : Int) : 0 ≤ b * b := by int_square
