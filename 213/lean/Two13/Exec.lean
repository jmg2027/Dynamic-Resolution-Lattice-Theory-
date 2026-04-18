/-
  Two13/Exec.lean — 213 실행기

  Lean은 하드웨어. 213은 ISA.
  이 파일은 213을 정의하지 않는다. 실행한다.
-/
import Init

-- ═══ 기호: 매체가 213을 담는 그릇 ═══
inductive S where
  | s1 : S
  | s2 : S
  | s3 : S
  deriving Repr, BEq, DecidableEq

abbrev W := List S

-- ═══ 재작성 한 단계 ═══
def step : W → W
  | .s2 :: x :: .s1 :: y :: rest =>
    if x == y then .s1 :: rest
    else x :: .s1 :: y :: step rest
  | .s1 :: rest => .s1 :: step rest
  | .s3 :: rest => .s2 :: .s1 :: .s2 :: rest
  | other => other

-- ═══ 고정점까지 실행 ═══
def run (fuel : Nat) (w : W) : W :=
  match fuel with
  | 0 => w
  | n + 1 =>
    let w' := step w
    if w' == w then w
    else run n w'

-- ═══ 표시 ═══
def S.show : S → String
  | .s1 => "1"
  | .s2 => "2"
  | .s3 => "3"

def W.show (w : W) : String :=
  String.join (w.map S.show)

-- ═══ 테스트 ═══

-- 213 자체: [2,1,3] → ?
#eval (run 10 [.s2, .s1, .s3]).show

-- 같은 것 구분: [2,1,1,1,1] → ?
#eval (run 10 [.s2, .s1, .s1, .s1, .s1]).show

-- 자기적용: [3] → ?
#eval (run 10 [.s3]).show

-- 이중 자기적용: [3,3] → ?
#eval (run 10 [.s3, .s3]).show

-- 213의 213: [2,1,3,1,2,1,3] → ?
#eval (run 20 [.s2, .s1, .s3, .s1, .s2, .s1, .s3]).show

-- 순수 경계: [1,1,1] → ?
#eval (run 10 [.s1, .s1, .s1]).show
