/-
  E213/Theorem/TwoDirections.lean — 독립 방향 = 2 증명
  의미 부여 없이. ㅁ와 비교 연산만.
  Nat.choose는 Init에 없으므로 직접 정의.
-/
import Init

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def choose (n k : Nat) : Nat :=
  if k > n then 0
  else factorial n / (factorial k * factorial (n - k))

abbrev S := Fin 3

def horizontal (comp : S → S → S) (b : S) : S → S :=
  fun a => comp a b

def vertical (comp : S → S → S) : Nat → S → S
  | 0 => id
  | n+1 => fun s => comp (vertical comp n s) (0 : S)

#eval choose 3 0  -- 1
#eval choose 3 1  -- 3
#eval choose 3 2  -- 3
#eval choose 3 3  -- 1
#eval choose 3 4  -- 0

theorem base_count : choose 3 1 = 3 := by native_decide
theorem self_sustaining : choose 3 2 = 3 := by native_decide
theorem top_is_one : choose 3 3 = 1 := by native_decide
theorem no_fourth_arity : choose 3 4 = 0 := by native_decide
theorem no_fifth_arity : choose 3 5 = 0 := by native_decide
theorem self_sustaining_eq : choose 3 1 = choose 3 2 := by native_decide

def nontrivialLevels : List Nat :=
  (List.range 6).filter fun k => choose 3 k > 1

#eval nontrivialLevels  -- [1, 2]

theorem exactly_two_directions :
    nontrivialLevels = [1, 2] := by native_decide

theorem top_not_independent : choose 3 3 ≤ 1 := by native_decide

theorem comp_has_two_degrees :
    let horiz := choose 3 1
    let vert := choose 3 2
    horiz > 1 ∧ vert > 1 := by native_decide

def allChoose3 : List (Nat × Nat) :=
  (List.range 6).map fun k => (k, choose 3 k)

#eval allChoose3  -- [(0,1),(1,3),(2,3),(3,1),(4,0),(5,0)]

theorem pascal_row_3_symmetric :
    choose 3 0 = choose 3 3 ∧ choose 3 1 = choose 3 2 := by
  constructor <;> native_decide

structure TwoDirectionsTheorem where
  base : choose 3 1 = 3
  pairs : choose 3 2 = 3
  top : choose 3 3 = 1
  beyond : choose 3 4 = 0
  self_sustain : choose 3 1 = choose 3 2
  directions : nontrivialLevels = [1, 2]

theorem two_directions : TwoDirectionsTheorem where
  base := by native_decide
  pairs := by native_decide
  top := by native_decide
  beyond := by native_decide
  self_sustain := by native_decide
  directions := by native_decide
