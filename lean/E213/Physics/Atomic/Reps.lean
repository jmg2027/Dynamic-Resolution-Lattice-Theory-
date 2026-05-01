import E213.Physics.Atomic.Expr

/-!
# Phase 4 — Atomic Representations summary

For each physical integer N:
  ∃ e : Expr,  eval e = N  ∧  complexity e ≤ K(N)

K(N) being *small* = expressible *compactly* as atomic.
Compare with average description length ~ log N for random integer N.

## Key theorems

  6 = NS·NT          complexity = 1
  8 = NS² - 1         complexity = 2 (mul + sub)
  10 = d·NT          complexity = 1
  12 = 2·NS·NT       complexity = 2 (or NT·NS·NT, ...)
  13 = NS²+NT²       complexity = 3
  16 = NT⁴            complexity = 1 (pow)
  24 = d²-1          complexity = 2
  25 = d²             complexity = 1
  60 = d²·NT + d·NT  complexity = 4
  137 = ?            (Phase 1 5-term sum, complexity ~ 5-6)
-/

namespace E213.Physics.Atomic.Reps

open E213.Physics.Atomic.Expr

/-- 6 = NS·NT, complexity = 1. -/
def six_expr : Expr := .mul .NSc .NTc

theorem six_eval : eval six_expr = 6 := by decide

theorem six_complexity : complexity six_expr ≤ 1 := by decide

/-- 8 = NT³.  complexity = 1. -/
def eight_expr : Expr := .pow .NTc 3

theorem eight_eval : eval eight_expr = 8 := by decide
theorem eight_complexity : complexity eight_expr ≤ 1 := by decide

/-- 8 = NS² - (NS - NT) alternative.  Complex form. -/
def eight_expr_alt : Expr := .sub (.pow .NSc 2) (.sub .NSc .NTc)

theorem eight_alt_eval : eval eight_expr_alt = 8 := by decide
theorem eight_alt_complexity : complexity eight_expr_alt ≤ 3 := by decide

/-- 10 = d·NT.  complexity = 1. -/
def ten_expr : Expr := .mul .dc .NTc

theorem ten_eval : eval ten_expr = 10 := by decide
theorem ten_complexity : complexity ten_expr ≤ 1 := by decide

/-- 16 = NT^4.  complexity = 1. -/
def sixteen_expr : Expr := .pow .NTc 4

theorem sixteen_eval : eval sixteen_expr = 16 := by decide
theorem sixteen_complexity : complexity sixteen_expr ≤ 1 := by decide

/-- 25 = d^2.  complexity = 1. -/
def twentyfive_expr : Expr := .pow .dc 2

theorem twentyfive_eval : eval twentyfive_expr = 25 := by decide
theorem twentyfive_complexity : complexity twentyfive_expr ≤ 1 := by decide

/-- 12 = NT·NS·NT (= 2·NS·NT).  complexity = 2. -/
def twelve_expr : Expr := .mul .NTc (.mul .NSc .NTc)

theorem twelve_eval : eval twelve_expr = 12 := by decide
theorem twelve_complexity : complexity twelve_expr ≤ 2 := by decide

/-- 24 = d² - 1.  No 1 const, use NS - NT.  complexity = 3. -/
def twentyfour_expr : Expr := .sub (.pow .dc 2) (.sub .NSc .NTc)

theorem twentyfour_eval : eval twentyfour_expr = 24 := by decide
theorem twentyfour_complexity : complexity twentyfour_expr ≤ 3 := by decide

/-- 13 = NS² + NT².  complexity = 3. -/
def thirteen_expr : Expr := .add (.pow .NSc 2) (.pow .NTc 2)

theorem thirteen_eval : eval thirteen_expr = 13 := by decide
theorem thirteen_complexity : complexity thirteen_expr ≤ 3 := by decide

/-- 60 = d²·NT + d·NT.  complexity = 5. -/
def sixty_expr : Expr := .add (.mul (.pow .dc 2) .NTc) (.mul .dc .NTc)

theorem sixty_eval : eval sixty_expr = 60 := by decide
theorem sixty_complexity : complexity sixty_expr ≤ 5 := by decide

/-- 192 = (NS²-1)·(d²-1) = NT³·(d²-(NS-NT)).  complexity ~ 5. -/
def oneNinetytwo_expr : Expr :=
  .mul (.pow .NTc 3) (.sub (.pow .dc 2) (.sub .NSc .NTc))

theorem oneNinetytwo_eval : eval oneNinetytwo_expr = 192 := by decide
theorem oneNinetytwo_complexity : complexity oneNinetytwo_expr ≤ 5 := by decide

end E213.Physics.Atomic.Reps
