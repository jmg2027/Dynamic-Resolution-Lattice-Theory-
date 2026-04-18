import E213.Firmware.Axiom

/-
  약점 탐지기.
  Malicious.lean에서 발견된 약점을 자동 검출.
  1. rel이 구분을 보존하는가? (constRel 공격 방어.)
  2. relify 후 원소가 다른가? (축소 탐지.)
  3. chain이 주기적인가? (유한 공간 탐지.)
-/

-- ═══ 약점 1: 구분 보존 검사 ═══

-- rel이 "좋은" 연산인가? relify 후에도 세 원소가 다른가?
def preservesDistinction (rel : Nat → Nat → Nat)
    (t : Triple Nat) : Bool :=
  let r := relify rel t
  r.x != r.y && r.x != r.z && r.y != r.z

-- 좋은 rel:
#eval preservesDistinction (· + ·) ⟨0, 1, 2⟩  -- true ✓
#eval preservesDistinction (· * ·) ⟨2, 3, 5⟩  -- true ✓
#eval preservesDistinction Nat.xor ⟨5, 3, 7⟩  -- ?

-- 나쁜 rel:
#eval preservesDistinction (fun a _ => a) ⟨1, 2, 3⟩  -- false ✗
#eval preservesDistinction (fun _ _ => 0) ⟨1, 2, 3⟩  -- false ✗
#eval preservesDistinction (· * ·) ⟨0, 1, 2⟩         -- false ✗ (0때문)

-- ═══ 약점 2: 축소 탐지 ═══

-- chain k번 후에도 구분 보존?
def chainPreserves (rel : Nat → Nat → Nat)
    (t : Triple Nat) (k : Nat) : Bool :=
  let r := chain rel t k
  r.x != r.y && r.x != r.z && r.y != r.z

-- 덧셈: 보존.
#eval (List.range 5).map (chainPreserves (· + ·) ⟨1, 2, 3⟩)
-- [true, true, true, true, true]

-- 곱셈 (0 포함): 축소.
#eval (List.range 5).map (chainPreserves (· * ·) ⟨0, 1, 2⟩)
-- [true, false, ...]

-- min: 축소.
#eval (List.range 5).map (chainPreserves Nat.min ⟨1, 2, 3⟩)
-- [true, false, false, ...]

-- ═══ 약점 3: 주기 탐지 ═══

-- chain이 주기적인가? (유한 공간에서 필연.)
def findPeriod (rel : Nat → Nat → Nat)
    (t : Triple Nat) (maxK : Nat) : Option Nat :=
  let t0 := (t.x, t.y, t.z)
  (List.range maxK).findSome? fun k =>
    let tk := chain rel t (k + 1)
    if (tk.x, tk.y, tk.z) == t0 then some (k + 1) else none

#eval findPeriod (fun a b => (a + b) % 3) ⟨0, 1, 2⟩ 20  -- some 2
#eval findPeriod (fun a b => (a + b) % 5) ⟨0, 1, 2⟩ 20  -- some 4
#eval findPeriod (fun a b => (a + b) % 7) ⟨0, 1, 2⟩ 50  -- some ?
#eval findPeriod (· + ·) ⟨1, 2, 3⟩ 100                   -- none (ℕ 무한)

-- ═══ 종합 건강 검사 ═══

structure HealthCheck where
  rel_name : String
  preserves : Bool     -- 구분 보존?
  chain_stable : Bool  -- chain 5번 후에도 보존?
  period : Option Nat  -- 주기 (none = 무한)
  deriving Repr

def checkHealth (name : String) (rel : Nat → Nat → Nat)
    (t : Triple Nat) : HealthCheck :=
  ⟨name, preservesDistinction rel t,
   (List.range 5).all (chainPreserves rel t),
   findPeriod rel t 20⟩

#eval [checkHealth "add" (·+·) ⟨1,2,3⟩, checkHealth "mul0" (·*·) ⟨0,1,2⟩,
       checkHealth "const" (fun a _ => a) ⟨1,2,3⟩, checkHealth "mod3" (fun a b => (a+b)%3) ⟨0,1,2⟩]
