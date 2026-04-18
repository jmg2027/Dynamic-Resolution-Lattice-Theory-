/-
  Two13/Flat.lean — 213의 평탄 구현

  이 코드는 타입 매체에 쓰여 있다.
  Lean은 타입을 요구한다. 이것은 매체의 제약이다.
  213에서 타입은 213 자체이다. 따라서 하나뿐이다.
-/
import Init

-- ═══ 매체의 제약: 타입이 필요하다 ═══
-- 213의 모든 것은 E이다. 타입 구분 없음.
inductive E where
  | e1 : E    -- 1: 경계
  | e2 : E    -- 2: 구분
  | e3 : E    -- 3: 창발
  deriving Repr, BEq, DecidableEq

open E

-- ═══ 213 문자열 (매체: 순서 있는 목록) ═══
abbrev W := List E

-- ═══ 편의 표기: 213.md에서 가져옴 ═══

-- def + := a1b. 1이 사이에 있는 것.
def W.plus (a b : W) : W := a ++ [e1] ++ b

-- def × := ab. 1이 사이에 없는 것.
def W.mul (a b : W) : W := a ++ b

-- def 0 := 11. 경계 옆에 경계.
def W.zero : W := [e1, e1]

-- ═══ 순환 동치: 순서는 매체의 제약 ═══
-- [2,1,3] ≈ [1,3,2] ≈ [3,2,1]
def W.rotate : W → W
  | [] => []
  | h :: t => t ++ [h]

def W.rotateN : Nat → W → W
  | 0, w => w
  | n+1, w => W.rotateN n (W.rotate w)

def W.cycEq (a b : W) : Prop :=
  a.length = b.length ∧ ∃ k : Nat, W.rotateN k a = b

-- ═══ 213의 기본 단어들 ═══
def w1 : W := [e1]
def w2 : W := [e2]
def w3 : W := [e3]
def w213 : W := [e2, e1, e3]
def w231 : W := [e2, e3, e1]

-- ═══ 검증: 213.md의 주장들 ═══

-- "2+3 = 213"
-- def +에 의해: [2] + [3] = [2] ++ [1] ++ [3] = [2,1,3]
theorem plus_is_213 : w2.plus w3 = w213 := by native_decide

-- "0 = 11"
theorem zero_is_11 : W.zero = [e1, e1] := rfl

-- "213의 길이 = 3"
theorem w213_length : w213.length = 3 := by native_decide

-- 213의 순환들: 213 → 132 → 321 → 213
-- (231은 역방향 순환 = 반사. 순환≠반사.)
def w132 : W := [e1, e3, e2]
theorem rotation_213 : w213.rotate = w132 := by native_decide
theorem rotation_cycle : w213.rotate.rotate.rotate = w213 := by
  native_decide

-- ═══ +의 기본 성질 ═══

-- 결합법칙: (a+b)+c = a+(b+c)
-- 이건 List.append의 결합법칙에서 따라옴
theorem plus_assoc (a b c : W) :
    (a.plus b).plus c = a.plus (b.plus c) := by
  simp [W.plus, List.append_assoc]

-- ═══ 표시 ═══
def E.show : E → String
  | .e1 => "1"
  | .e2 => "2"
  | .e3 => "3"

def W.show (w : W) : String :=
  String.join (w.map E.show)

-- ═══ 테스트 ═══
#eval w213.show                           -- "213"
#eval (w2.plus w3).show                   -- "213"
#eval (w1.plus w2).show                   -- "112"
#eval W.zero.show                         -- "11"
#eval (W.zero.plus w2).show               -- "1112"
#eval w213.rotate.show                    -- "132"
#eval w213.rotate.rotate.show             -- "321"
#eval w213.rotate.rotate.rotate.show      -- "213"
