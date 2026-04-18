-- 213: 3 고유 공리의 완전 독립성 증명
import Init

-- ═══ 모델 1: A8 독립 ═══
-- Bool, or, const true, e1=true
theorem m1_a8_fails : (true || false) ≠ false := by decide
theorem m1_a9_holds (x : Bool) : true = true := rfl
theorem m1_a12_holds (a b c : Bool) :
    true = (true || true) := by decide

-- ═══ 모델 2: A9 독립 ═══
-- Bool, or, or, e1=false
theorem m2_a8_holds (x : Bool) : (false || x) = x := by
  cases x <;> rfl
theorem m2_a9_fails : (false || true) ≠ false := by decide
theorem m2_a12_holds (a b c : Bool) :
    (a || (b || c)) = ((a || b) || (a || c)) := by
  cases a <;> cases b <;> cases c <;> rfl

-- ═══ 모델 3: A12 독립 ═══
-- 3원소 {z, a, b}
inductive T3 where | z | a | b
  deriving Repr, BEq, DecidableEq

open T3

def t3_plus : T3 → T3 → T3  -- max (z < a < b)
  | z, x => x | x, z => x
  | a, a => a | a, b => b | b, a => b | b, b => b

def t3_times : T3 → T3 → T3  -- 비분배적
  | z, _ => z | _, z => z
  | a, a => b | a, b => a | b, a => a | b, b => b

-- A8: t3_plus z x = x
theorem m3_a8 (x : T3) : t3_plus z x = x := by cases x <;> rfl
-- A9: t3_times z x = z
theorem m3_a9 (x : T3) : t3_times z x = z := by cases x <;> rfl
-- A12 실패: a*(a∨b) ≠ a*a ∨ a*b
-- a*(max(a,b)) = a*b = a. max(a*a, a*b) = max(b, a) = b.
theorem m3_a12_fails : t3_times a (t3_plus a b) ≠
    t3_plus (t3_times a a) (t3_times a b) := by decide

-- ═══ 결론 ═══
-- {plus_e1, times_e1, distrib} 쌍별 독립. 증명 완료.
-- 모델 1: A9✓ A12✓ A8✗ (Bool, or, const)
-- 모델 2: A8✓ A12✓ A9✗ (Bool, or, or)
-- 모델 3: A8✓ A9✓ A12✗ (T3, max, custom)
-- 3은 환원 불가능.
