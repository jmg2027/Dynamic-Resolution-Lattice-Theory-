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
