import E213.Firmware.Axiom
import E213.Firmware.Closure

/-
  sorry 종류 분류기.
  depth로 sorry의 종류를 자동 판정.
  depth ≤ 2: 종류 1 (해소 가능).
  depth ≤ 100(ω): 종류 2 (API 확장 필요).
  depth > 100: 종류 3 (원리적 한계).
-/

inductive SorryKind where
  | solvable    -- 종류 1: depth ≤ 2. native_decide로 해소.
  | needsAPI    -- 종류 2: depth ω. HV API 확장 필요.
  | impossible  -- 종류 3: depth > ε₀. 새 공리 필요.
  deriving DecidableEq, Repr

def classifySorry (depth : Nat) : SorryKind :=
  if depth ≤ 2 then .solvable
  else if depth ≤ 100 then .needsAPI
  else .impossible

-- ═══ Obj의 depth로 분류 ═══

def classifyObj (o : Obj) : SorryKind := classifySorry o.depth

-- 테스트:
#eval classifyObj (.gen 0)                          -- solvable (d=0)
#eval classifyObj (.mul (.gen 0) (.gen 1))          -- solvable (d=1)
#eval classifyObj (.mul (.mul (.gen 0) (.gen 1)) (.gen 2)) -- solvable (d=2)

-- 깊은 Obj:
def deepObj : Nat → Obj
  | 0 => .gen 0
  | n+1 => .mul (deepObj n) (.gen 0)

#eval classifyObj (deepObj 3)   -- needsAPI (d=3)
#eval classifyObj (deepObj 50)  -- needsAPI (d=50)

-- ═══ 수학 문제의 분류 ═══

-- 문제를 depth로 인코딩하여 분류.
structure MathProblem where
  name : String
  depth : Nat
  deriving Repr

def classify (p : MathProblem) : SorryKind := classifySorry p.depth

def problems : List MathProblem := [
  ⟨"pairs(3)=3", 0⟩,
  ⟨"Lagrange(finite)", 2⟩,
  ⟨"Goldbach(n=100)", 1⟩,
  ⟨"Goldbach(∀n)", 100⟩,
  ⟨"Continuity(ε-δ)", 100⟩,
  ⟨"Con(PA)", 200⟩
]

#eval problems.map fun p => (p.name, classify p)
-- [("pairs(3)=3", solvable), ("Lagrange", solvable),
--  ("Goldbach(100)", solvable), ("Goldbach(∀)", needsAPI),
--  ("Continuity", needsAPI), ("Con(PA)", impossible)]

-- ═══ 분류 정리 ═══

theorem solvable_at_2 : classifySorry 2 = .solvable := by native_decide
theorem needs_at_3 : classifySorry 3 = .needsAPI := by native_decide
theorem impossible_at_200 : classifySorry 200 = .impossible := by native_decide

-- solvable 범위에서는 sorry가 필요 없어야 함.
-- needsAPI 범위에서는 HV 확장으로 해소 가능.
-- impossible 범위에서는 sorry가 불가피.
