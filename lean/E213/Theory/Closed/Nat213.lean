import E213.Theory.Closed.FoldRaw

/-!
# Theory.Closed.Nat213 — closed-universe Nat (Method A: Z=a, C=b)

자연수 = Raw 의 한쪽-증식 chain.  외부 `Nat` 안 빌리고 Raw 안에서.

Method A:
  - 0 = Raw.a
  - succ n = slashOrSelf n Raw.b   (즉 n 에 b 를 추가)
  - 1 = slash a b
  - 2 = slash (slash a b) b   (canonical form 처리됨)
  - ...

이 모듈은 가장 단순한 Method A 만.  일반 NumberingSystem 은 별도 모듈.
-/

namespace E213.Theory.Closed.Nat213

open E213.Theory E213.Theory.Closed

/-! ### Method A primitives -/

/-- 0 의 Raw 표현. -/
def zero : Raw := Raw.a

/-- successor — n 에 Raw.b 를 wrap. -/
def succ (n : Raw) : Raw := slashOrSelf n Raw.b

/-- Lean Nat 으로부터 Method A Raw chain 만들기 — 외부 Nat 사용 (편의용). -/
def numeral : Nat → Raw
  | 0     => zero
  | n + 1 => succ (numeral n)

theorem numeral_zero : numeral 0 = zero := rfl
theorem numeral_succ (n : Nat) : numeral (n + 1) = succ (numeral n) := rfl

end E213.Theory.Closed.Nat213

namespace E213.Theory.Closed.Nat213

open E213.Theory E213.Theory.Closed

/-! ### Projection back to external Nat (= leaves count) -/

/-- Method A Raw chain 의 외부 Nat 값 — leaves 수.
    `value (numeral n) = n + 1` (수학적으로 = leaves count). -/
def value (r : Raw) : Nat := Raw.fold 1 1 (· + ·) r

theorem value_zero : value zero = 1 := rfl
theorem value_a : value Raw.a = 1 := rfl
theorem value_b : value Raw.b = 1 := rfl

/-- `value (slashOrSelf n b) = value n + 1` (n ≠ b 가정 — Method A
    chain 내부에서 항상 성립). -/
theorem value_succ_of_ne (n : Raw) (h : n ≠ Raw.b) :
    value (succ n) = value n + 1 := by
  unfold succ value
  rw [slashOrSelf_of_ne h]
  -- (Raw.fold 1 1 (· + ·)) on slash 이 symmetric combine 이라 분해 가능
  show Raw.fold 1 1 (· + ·) (Raw.slash n Raw.b h) = _
  rw [Raw.fold_slash 1 1 (· + ·) (fun u v => Nat.add_comm u v) n Raw.b h]
  show Raw.fold 1 1 (· + ·) n + Raw.fold 1 1 (· + ·) Raw.b
     = Raw.fold 1 1 (· + ·) n + 1
  rfl

end E213.Theory.Closed.Nat213

namespace E213.Theory.Closed.Nat213

open E213.Theory E213.Theory.Internal E213.Theory.Closed

/-! ### Arithmetic (closed in Raw)

기존 `Theory/Nat213/Core.lean` 의 inductive `Nat213.add / mul` 을
closed-Raw 로 재구현.  output 도 Raw, 외부 type 의존 없음.

213-native naming: `Raw.a` 가 213 의 "1" (smallest positive nat).
이전에 `zero` 라고 부른 것 = 사실 `one`.  alias 추가. -/

/-- Alias: 213-native "1" — Raw.a 가 213 의 첫 양의 자연수. -/
abbrev one : Raw := zero  -- = Raw.a

/-- Method A chain 위 덧셈 (Tree-level structural recursion).  m의
    Tree 구조를 따라 succ 누적. -/
private def addAux (n : Raw) : Tree → Raw
  | .a => succ n
  | .b => n  -- valid Nat213 chain 에는 도달 불가; fallback
  | .slash x y =>
      if x = Tree.b then
        -- canonical (succ chain n≥2): b 가 왼쪽, 전임자가 오른쪽
        succ (addAux n y)
      else
        -- numeral 1 case (a 왼쪽, b 오른쪽) 또는 n≥2 의 후속
        succ (addAux n x)

/-- **Closed-Raw addition**: `add m n` — 양쪽 모두 Method A chain 가정,
    output 도 Method A chain. -/
def add (m n : Raw) : Raw := addAux n m.val

/-- `add` 는 left-arg 가 `one` (= Raw.a) 일 때 단순 succ. -/
theorem one_add (n : Raw) : add one n = succ n := rfl

end E213.Theory.Closed.Nat213

namespace E213.Theory.Closed.Nat213

open E213.Theory E213.Theory.Internal E213.Theory.Closed

/-! ### Multiplication (closed in Raw) -/

/-- Closed-Raw multiplication via Tree-structural recursion.
    `mul m n` = repeated `add n` invocations driven by m's chain. -/
private def mulAux (n : Raw) : Tree → Raw
  | .a => n  -- "1 · n = n"
  | .b => n  -- fallback for invalid Nat213
  | .slash x y =>
      if x = Tree.b then
        add n (mulAux n y)
      else
        add n (mulAux n x)

/-- `mul m n` — Method A chain 위 곱셈, output Method A chain. -/
def mul (m n : Raw) : Raw := mulAux n m.val

theorem one_mul (n : Raw) : mul one n = n := rfl

end E213.Theory.Closed.Nat213
