import E213.Theory.Raw.API

/-!
# Lens.Number.Nat213.Raw — Method A 카타모피즘 (Z=a, C=b)

`Nat213` (= 양의 자연수) 의 canonical Raw-derived 표현.  Lens 의미:
**`Raw.fold one one add` 의 closed-Raw codomain catamorphism** —
출력 codomain 을 Raw 로 못박은 endomorphic fold
(`Theory.Raw.Endomorphic`).

자연수 = Raw 의 한쪽-증식 chain.  외부 `Nat` 안 빌리고 Raw 안에서.

Method A:
  - 0 = Raw.a
  - succ n = slashOrSelf n Raw.b   (즉 n 에 b 를 추가)
  - 1 = slash a b
  - 2 = slash (slash a b) b   (canonical form 처리됨)
  - ...

이 모듈은 가장 단순한 Method A 만.  일반 numbering system 은
`Lens.Number.Nat213.NumberingSystem`.  Inductive Peano 표현은
`Lens.Number.Nat213.Peano`; 두 표현 사이 동형은 `.Bridge`.
-/

namespace E213.Lens.Number.Nat213.Raw

open E213.Theory E213.Term.Internal E213.Theory.Raw.Endomorphic

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

/-! ### Arithmetic (closed in Raw)

`Lens/Number/Nat213/Peano.lean` 의 inductive `Nat213.add / mul` 을
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

/-! ### Key arithmetic laws — Layer 2 (inductive Nat213) 와 일치성 위한 핵심 lemma -/

/-- **add_succ_left**: `add (succ k) n = succ (add k n)` (k ≠ Raw.b 가정).
    inductive Nat213 의 `add (succ m) n = succ (add m n)` 의 closed-Raw 버전.

    canonical-form 분석: succ k 의 underlying Tree 는 cmp(k.val, .b) 에 따라
    `.slash k.val .b` 또는 `.slash .b k.val` — 두 layout 모두에서 addAux 의
    조건 분기가 같은 결과를 줌. -/
theorem add_succ_left (k n : Raw) (hk : k ≠ Raw.b) :
    add (succ k) n = succ (add k n) := by
  show addAux n (succ k).val = succ (addAux n k.val)
  unfold succ slashOrSelf
  rw [dif_neg hk]
  -- 목표: addAux n (Raw.slash k Raw.b hk).val = succ (addAux n k.val)
  show addAux n (Raw.slash k Raw.b hk).val = succ (addAux n k.val)
  unfold Raw.slash
  -- match cmp k.val .b 분기
  split <;> rename_i hcmp
  · -- cmp = lt: val = Tree.slash k.val .b
    show addAux n (Tree.slash k.val Tree.b) = succ (addAux n k.val)
    -- addAux 의 .slash 분기, x = k.val, y = .b
    show (if k.val = Tree.b then succ (addAux n Tree.b) else succ (addAux n k.val))
       = succ (addAux n k.val)
    rw [if_neg]
    -- 증명: k.val ≠ Tree.b — k ≠ Raw.b 로부터
    intro hkb
    apply hk
    apply Subtype.ext
    exact hkb
  · -- cmp = gt: val = Tree.slash .b k.val
    show addAux n (Tree.slash Tree.b k.val) = succ (addAux n k.val)
    show (if Tree.b = Tree.b then succ (addAux n k.val) else succ (addAux n Tree.b))
       = succ (addAux n k.val)
    rw [if_pos rfl]
  · -- cmp = eq: absurd (k = Raw.b 로 귀결)
    exfalso
    apply hk
    apply Subtype.ext
    exact Tree.cmp_eq_to_eq _ _ hcmp

/-- **mul_succ_left**: `mul (succ k) n = add n (mul k n)` (k ≠ Raw.b 가정).
    inductive Nat213 의 `mul (succ m) n = add n (mul m n)` 의 closed-Raw 버전. -/
theorem mul_succ_left (k n : Raw) (hk : k ≠ Raw.b) :
    mul (succ k) n = add n (mul k n) := by
  show mulAux n (succ k).val = add n (mulAux n k.val)
  unfold succ slashOrSelf
  rw [dif_neg hk]
  show mulAux n (Raw.slash k Raw.b hk).val = add n (mulAux n k.val)
  unfold Raw.slash
  split <;> rename_i hcmp
  · -- cmp = lt: val = .slash k.val .b
    show mulAux n (Tree.slash k.val Tree.b) = add n (mulAux n k.val)
    show (if k.val = Tree.b then add n (mulAux n Tree.b) else add n (mulAux n k.val))
       = add n (mulAux n k.val)
    rw [if_neg]
    intro hkb
    apply hk
    apply Subtype.ext
    exact hkb
  · -- cmp = gt: val = .slash .b k.val
    show mulAux n (Tree.slash Tree.b k.val) = add n (mulAux n k.val)
    show (if Tree.b = Tree.b then add n (mulAux n k.val) else add n (mulAux n Tree.b))
       = add n (mulAux n k.val)
    rw [if_pos rfl]
  · exfalso
    apply hk
    apply Subtype.ext
    exact Tree.cmp_eq_to_eq _ _ hcmp

/-! ### Lean-free value: Raw → Raw

기존 `value : Raw → Nat` 은 Lean Nat 를 사용 (boundary layer).
다음 정의는 출력도 Raw (Method A chain) — Lean 격리 layer 한 발 더 안쪽.

`leavesCountRaw r` = r 의 leaves 수를 Method A Nat213 chain 으로 인코딩.
즉 leavesCount(numeral n) = numeral n 자기 자신 (numeral n 은 n+1 leaves).

이게 "Lean 타입을 격리 레이어로만 사용" 의 시범:
  - 입력 Raw, 출력 Raw
  - 외부 Nat/Bool 의존 없음
  - 대신 Method A chain 표기 사용 -/

/-- Lean-free leaves count — 출력도 Raw (Method A chain). -/
def leavesCountRaw : Raw → Raw := Raw.fold one one add

theorem leavesCountRaw_a : leavesCountRaw Raw.a = one := rfl
theorem leavesCountRaw_b : leavesCountRaw Raw.b = one := rfl

/-- 동작 sanity — 처음 4개 numeral. -/
example : leavesCountRaw (numeral 0) = numeral 0 := rfl  -- "1" leaf
example : leavesCountRaw (numeral 1) = numeral 1 := rfl  -- "2" leaves
example : leavesCountRaw (numeral 2) = numeral 2 := rfl  -- "3" leaves
example : leavesCountRaw (numeral 3) = numeral 3 := rfl  -- "4" leaves

/-! ### Chain invariants — leavesCountRaw 분석을 위한 보조 -/

/-- 모든 Method A chain (numeral n) 은 Raw.b 와 다름.  Method A 의
    structural invariant. -/
theorem numeral_ne_b (n : Nat) : numeral n ≠ Raw.b := by
  induction n with
  | zero =>
      -- numeral 0 = zero = Raw.a ≠ Raw.b
      intro h
      exact Tree.noConfusion (congrArg Subtype.val h)
  | succ k ih =>
      -- numeral (k+1) = succ (numeral k) = slashOrSelf (numeral k) Raw.b
      show succ (numeral k) ≠ Raw.b
      unfold succ slashOrSelf
      rw [dif_neg ih]
      intro h
      have hval : (Raw.slash (numeral k) Raw.b ih).val = Raw.b.val :=
        congrArg Subtype.val h
      unfold Raw.slash at hval
      split at hval
      · exact Tree.noConfusion hval
      · exact Tree.noConfusion hval
      · rename_i hcmp
        exact ih (Subtype.ext (Tree.cmp_eq_to_eq _ _ hcmp))

/-! ### leavesCountRaw 의 step lemma + chain identity -/

/-- **Step**: `leavesCountRaw (succ r) = succ (leavesCountRaw r)` for r ≠ Raw.b.
    canonical-form 분석: succ r 의 underlying Tree 가 cmp(r.val, .b) 에 따라
    `.slash r.val .b` (cmp=lt) 또는 `.slash .b r.val` (cmp=gt) — 양쪽
    모두 fold 결과가 `succ (leavesCountRaw r)` 와 일치. -/
theorem leavesCountRaw_succ (r : Raw) (h : r ≠ Raw.b) :
    leavesCountRaw (succ r) = succ (leavesCountRaw r) := by
  show Raw.fold one one add (succ r) = succ (Raw.fold one one add r)
  unfold succ slashOrSelf
  rw [dif_neg h]
  show Raw.fold one one add (Raw.slash r Raw.b h)
     = succ (Raw.fold one one add r)
  unfold Raw.fold Raw.slash
  split <;> rename_i hcmp
  · -- cmp = lt: val = Tree.slash r.val .b
    show Tree.fold one one add (Tree.slash r.val Tree.b)
       = succ (Tree.fold one one add r.val)
    show add (Tree.fold one one add r.val) (Tree.fold one one add Tree.b)
       = succ (Tree.fold one one add r.val)
    show add (Tree.fold one one add r.val) one
       = succ (Tree.fold one one add r.val)
    -- need: add x one = succ x for x = leavesCountRaw r
    -- one = Raw.a, so add x one = addAux one x.val = ... need x ≠ b
    -- For r = Raw.a (the only cmp=lt case), leavesCountRaw r = one ≠ b
    -- We just compute: x = one. add one one = succ one (rfl since one_add).
    have h_r_eq_a : r = Raw.a := by
      apply Subtype.ext
      cases hr : r.val with
      | a => rfl
      | b => exfalso; exact h (Subtype.ext hr)
      | slash _ _ =>
          -- r.val = slash → cmp(slash, b) = gt, but we're in cmp=lt branch
          rw [hr] at hcmp
          exact Ordering.noConfusion hcmp
    rw [h_r_eq_a]
    rfl
  · -- cmp = gt: val = Tree.slash .b r.val
    show Tree.fold one one add (Tree.slash Tree.b r.val)
       = succ (Tree.fold one one add r.val)
    show add (Tree.fold one one add Tree.b) (Tree.fold one one add r.val)
       = succ (Tree.fold one one add r.val)
    show add one (Tree.fold one one add r.val)
       = succ (Tree.fold one one add r.val)
    -- one_add: add one x = succ x by rfl
    rfl
  · -- cmp = eq: r = b, contradiction
    exfalso
    apply h
    apply Subtype.ext
    exact Tree.cmp_eq_to_eq _ _ hcmp

/-- **Chain identity**: leavesCountRaw 가 numeral chain 위에서 identity.
    Method A chain 들이 leaves-count quotient 의 canonical representative. -/
theorem leavesCountRaw_numeral (n : Nat) :
    leavesCountRaw (numeral n) = numeral n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      -- numeral (k+1) = succ (numeral k)
      show leavesCountRaw (succ (numeral k)) = succ (numeral k)
      rw [leavesCountRaw_succ _ (numeral_ne_b k), ih]

/-- **Numeral value**: `value (numeral n) = n + 1` — Method A chain n 이
    Lean Nat (n+1) 에 대응.  Real213 cut 우주로의 bridge 의 핵심. -/
theorem value_numeral (n : Nat) : value (numeral n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      -- value (numeral (k+1)) = value (succ (numeral k)) = value (numeral k) + 1
      show value (succ (numeral k)) = (k + 1) + 1
      rw [value_succ_of_ne _ (numeral_ne_b k), ih]

end E213.Lens.Number.Nat213.Raw
