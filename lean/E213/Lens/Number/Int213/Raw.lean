import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Int213.Raw — Raw-derived ℤ (Nat213.Raw 의 sign-extension)

`Lens.Number.Nat213.Raw` 는 ℕ₊ 를 closed-Raw chain (Method A) 으로
encode: `one := Raw.a`, `succ := slashOrSelf · Raw.b`, `add`/`mul`
모두 output codomain 이 Raw.  이 파일은 그 위에 부호와 0 을 도입한
정수 ℤ — 3-갈래 sum-type 인코딩:

  Int213 ::=  ofPos Raw    -- 양의 정수 (carrier: Method A chain 권장)
           |  zero         -- 0 (additive identity)
           |  ofNeg Raw    -- 음의 정수 (carrier: 부호 반전된 chain)

**Pure Raw-derived**: carriers 가 모두 `E213.Theory.Raw` —
inductive Peano 사본 (`Lens.Number.Nat213.Peano`) 안 빌림.
ergonomic Peano 표현은 parallel 한 별도 layer (필요시).

**0 의 출처**: 213 의 axiom 에 nullary atom 없음 — Raw 의 모든
element 는 leaves ≥ 1 (`Nat213.Peano.no_additive_identity_at_one`).
하지만 *additive group 의 inverse closure* 를 요구하면 0 은 합성으로
강제 출현 — `Int213.zero` 가 그것 (`add_neg_self : a + (-a) = 0`).
즉 Raw 영역에는 zero 없되, Int 같은 *structural extension* 에서는
inevitable.  (parallel: `Nat213/Tower/NatPairToInt` 가 ℕ×ℕ
diagonal quotient 으로 같은 ℤ 를 구성 — 이쪽은 quotient/projection
표현, 이 파일은 inductive Raw-carrier 표현.)

**Convention**: `ofPos r` 의 의미값 = `Nat213.Raw.value r`
(= leaves count of r).  Canonical Method A chain 위에서 well-defined;
non-chain Raw 도 (leaves count quotient 으로) carrier 허용.
Normalize 필요시 `Nat213.Raw.leavesCountRaw`.

∅-axiom; Mathlib/Classical 사용 0.
-/

namespace E213.Lens.Number.Int213.Raw

open E213.Theory (Raw)

/-! ### Nat213.Raw 단축 alias (carrier-side 연산만 가져옴) -/

/-- `Nat213.Raw.value` (Raw → 외부 Nat leaves count) 단축 alias. -/
private abbrev nrValue (r : Raw) : Nat := E213.Lens.Number.Nat213.Raw.value r

/-- `Nat213.Raw.numeral` (외부 Nat → Method A chain) 단축 alias.
    Off-by-one: numeral n = 양의 정수 (n+1) 의 chain. -/
private abbrev nrNumeral (n : Nat) : Raw := E213.Lens.Number.Nat213.Raw.numeral n

/-- `Nat213.Raw.one` (= Raw.a) 단축 alias. -/
private abbrev nrOne : Raw := E213.Lens.Number.Nat213.Raw.one

/-- `Nat213.Raw.add` (closed-Raw ℕ₊ addition) 단축 alias. -/
private abbrev nrAdd (m n : Raw) : Raw := E213.Lens.Number.Nat213.Raw.add m n

/-- `Nat213.Raw.mul` (closed-Raw ℕ₊ multiplication) 단축 alias. -/
private abbrev nrMul (m n : Raw) : Raw := E213.Lens.Number.Nat213.Raw.mul m n

/-! ### Int213 datatype -/

/-- 213-native inductive ℤ — Raw-derived Nat213 의 부호·0 확장. -/
inductive Int213 : Type
  | ofPos : Raw → Int213
  | zero  : Int213
  | ofNeg : Raw → Int213

namespace Int213

/-! ### 상수 -/

/-- ℤ 의 1. -/
def one : Int213 := ofPos nrOne

/-- ℤ 의 -1. -/
def negOne : Int213 := ofNeg nrOne

/-! ### 부호 반전 -/

/-- 부호 반전. -/
def neg : Int213 → Int213
  | ofPos r => ofNeg r
  | zero    => zero
  | ofNeg r => ofPos r

theorem neg_zero : neg zero = zero := rfl

theorem neg_neg : ∀ a : Int213, neg (neg a) = a
  | ofPos _ => rfl
  | zero    => rfl
  | ofNeg _ => rfl

/-! ### mixed-sign cancellation helper

`cancel m n` = `value m - value n` 의 부호 있는 Int213.  Lean Nat 의
값 비교 + truncated subtraction 으로 분기.  Nat 은 boundary
(Nat213.Raw.value/numeral 이 이미 boundary layer 이므로 일관). -/

/-- `cancel m n` = `value m - value n` (부호 있는 정수). -/
def cancel (m n : Raw) : Int213 :=
  if nrValue m = nrValue n then zero
  else if nrValue m < nrValue n then
    ofNeg (nrNumeral (nrValue n - nrValue m - 1))
  else
    ofPos (nrNumeral (nrValue m - nrValue n - 1))

theorem cancel_self (r : Raw) : cancel r r = zero := by
  unfold cancel
  rw [if_pos rfl]

/-! ### 덧셈 -/

/-- 덧셈.  zero 가 양쪽 identity; 같은 부호면 `Nat213.Raw.add` 위임;
    반대 부호면 `cancel` 위임. -/
def add : Int213 → Int213 → Int213
  | zero,    b       => b
  | a,       zero    => a
  | ofPos m, ofPos n => ofPos (nrAdd m n)
  | ofNeg m, ofNeg n => ofNeg (nrAdd m n)
  | ofPos m, ofNeg n => cancel m n
  | ofNeg m, ofPos n => cancel n m

theorem zero_add : ∀ a : Int213, add zero a = a
  | ofPos _ => rfl
  | zero    => rfl
  | ofNeg _ => rfl

theorem add_zero : ∀ a : Int213, add a zero = a
  | ofPos _ => rfl
  | zero    => rfl
  | ofNeg _ => rfl

/-- ★★★ Additive inverse: `a + (-a) = 0`.  Nat213 에는 없던 성질
    (`Peano.no_additive_identity_at_one`); sign-확장이 비로소 inverse
    를 도입. -/
theorem add_neg_self : ∀ a : Int213, add a (neg a) = zero
  | ofPos r => cancel_self r
  | zero    => rfl
  | ofNeg r => cancel_self r

/-! ### 곱셈 -/

/-- 곱셈.  zero 가 absorbing; 부호 규칙:
    + · + = +,  ± · ∓ = -,  - · - = +. -/
def mul : Int213 → Int213 → Int213
  | zero,    _       => zero
  | _,       zero    => zero
  | ofPos m, ofPos n => ofPos (nrMul m n)
  | ofPos m, ofNeg n => ofNeg (nrMul m n)
  | ofNeg m, ofPos n => ofNeg (nrMul m n)
  | ofNeg m, ofNeg n => ofPos (nrMul m n)

theorem zero_mul : ∀ a : Int213, mul zero a = zero
  | ofPos _ => rfl
  | zero    => rfl
  | ofNeg _ => rfl

theorem mul_zero : ∀ a : Int213, mul a zero = zero
  | ofPos _ => rfl
  | zero    => rfl
  | ofNeg _ => rfl

/-- `one · a = a` — left multiplicative identity.  `Nat213.Raw.one_mul`
    이 rfl 이라 모든 branch rfl. -/
theorem one_mul : ∀ a : Int213, mul one a = a
  | ofPos _ => rfl
  | zero    => rfl
  | ofNeg _ => rfl

/-! ### 뺄셈 (Int213 에서는 closed — Nat213.Raw 에서 안 되던 것) -/

/-- 뺄셈 = add + neg.  `Nat213.Peano.no_closed_subtraction` 이
    Nat213 에서 닫혀있지 않다고 증명; Int213 의 sign-확장에서 비로소
    closed. -/
def sub (a b : Int213) : Int213 := add a (neg b)

theorem sub_self (a : Int213) : sub a a = zero := add_neg_self a

/-! ### 외부 Lean Int 로 projection (boundary layer) -/

/-- 외부 Lean `Int` 로 변환.  Boundary cast — 내부 Int213 algebra
    에서는 사용 안 함. -/
def toInt : Int213 → Int
  | zero    => 0
  | ofPos r => (nrValue r : Int)
  | ofNeg r => -(nrValue r : Int)

theorem toInt_zero : toInt zero = 0 := rfl
theorem toInt_one : toInt one = 1 := rfl
theorem toInt_negOne : toInt negOne = -1 := rfl

end Int213

end E213.Lens.Number.Int213.Raw
