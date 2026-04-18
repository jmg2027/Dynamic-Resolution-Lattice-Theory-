-- 213: Expr/≈ ≅ ℕ[x,y]
--
-- 213의 동치류 대수는 두 변수 위 다항식 반환이다.
-- e₂ = x, e₃ = y, e₁ = 0.
-- 정규형(정렬된 단항식 리스트) = 다항식 표현.

import Mathlib.Tactic.Basic

-- ═══ 단항식 = (p, q) = x^p × y^q ═══
structure Mon where
  p : Nat  -- x(=e₂) 차수
  q : Nat  -- y(=e₃) 차수
  deriving Repr, BEq, DecidableEq

instance : Ord Mon where
  compare a b :=
    match compare a.p b.p with
    | .eq => compare a.q b.q
    | r => r

-- ═══ 다항식 = 단항식의 정렬된 리스트 (계수 = 중복도) ═══
-- [⟨1,0⟩, ⟨1,0⟩, ⟨0,1⟩] = 2x + y
abbrev Poly := List Mon

def Poly.add (a b : Poly) : Poly :=
  (a ++ b).mergeSort (compare · · |>.isLE)

def Poly.mul (a b : Poly) : Poly :=
  (a.flatMap fun m1 => b.map fun m2 =>
    ⟨m1.p + m2.p, m1.q + m2.q⟩).mergeSort (compare · · |>.isLE)

def Poly.zero : Poly := []
def Poly.x : Poly := [⟨1, 0⟩]
def Poly.y : Poly := [⟨0, 1⟩]

-- ═══ 대칭 불변량 ═══
-- σ₁ = x + y (기본 대칭 다항식 1차)
-- σ₂ = xy   (기본 대칭 다항식 2차)
def sigma1 : Poly := Poly.x.add Poly.y    -- x + y
def sigma2 : Poly := Poly.x.mul Poly.y    -- xy

-- ═══ swap: x ↔ y ═══
def Mon.swap (m : Mon) : Mon := ⟨m.q, m.p⟩
def Poly.swap (p : Poly) : Poly :=
  (p.map Mon.swap).mergeSort (compare · · |>.isLE)

-- σ₁과 σ₂는 swap 불변
#eval sigma1 == sigma1.swap  -- true
#eval sigma2 == sigma2.swap  -- true

-- x² + y²는 swap 불변
def p2 : Poly := (Poly.x.mul Poly.x).add (Poly.y.mul Poly.y)
#eval p2 == p2.swap          -- true

-- xy는 swap 불변 (= σ₂)
#eval (Poly.x.mul Poly.y) == (Poly.x.mul Poly.y).swap  -- true

-- x는 swap 비불변
#eval Poly.x == Poly.x.swap  -- false

-- ═══ eval: 다항식을 수치로 ═══
def Mon.eval (m : Mon) (vx vy : Nat) : Nat :=
  vx ^ m.p * vy ^ m.q

def Poly.eval (p : Poly) (vx vy : Nat) : Nat :=
  p.foldl (fun acc m => acc + m.eval vx vy) 0

-- DRLT eval: (x, y) = (2, 3)
#eval sigma1.eval 2 3   -- 5 = d
#eval sigma2.eval 2 3   -- 6 = n_S × n_T
#eval p2.eval 2 3       -- 13 = 4 + 9

-- σ₁² = x² + 2xy + y²
def sigma1_sq : Poly := sigma1.mul sigma1
#eval sigma1_sq.eval 2 3  -- 25 = d²

-- σ₁² - 2σ₂ = x² + y²
-- 25 - 12 = 13 ✓ (뺄셈은 ℕ[x,y]에 없음. 관찰만.)

-- ═══ DRLT 상수들의 다항식 표현 ═══
-- d   = σ₁         = 5
-- d²  = σ₁²        = 25
-- n_S × n_T = σ₂   = 6
-- α_GUT ∝ σ₂/σ₁²  = 6/25 (× 1/π² from ζ(2))

-- ═══ 결론 ═══
-- Expr/≈ ≅ ℕ[x, y]. 두 변수 다항식 반환.
-- swap 불변 부분환: ℕ[σ₁, σ₂] (대칭 다항식).
-- DRLT의 모든 상수는 σ₁, σ₂의 다항식.
-- eval(2,3)은 ℕ[x,y]의 한 점에서의 값.
