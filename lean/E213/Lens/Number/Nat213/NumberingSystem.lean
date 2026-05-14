import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Nat213.NumberingSystem — meta pattern over (Z, C) choices

Method A (Z=a, C=b) 는 가장 단순한 numbering.  하지만 임의의 두 Raw
`Z ≠ C` 쌍은 또 다른 valid numbering 을 줌.  이 모듈은 그 메타 패턴.

## 명제

  - `NumberingSystem` = `(Z, C : Raw)` + `Z ≠ C` 증거.
  - 각 system 마다 numerals (0, 1, 2, ...) 가 Raw chain 으로 만들어짐.
  - 두 system 사이 변환은 `foldRaw S.Z S.C slashOrSelf` (Method A → S).
  - 이 변환이 numerals 를 numerals 로 보내는 isomorphism — `iso_numeral`.

## Why this matters

기존 수학에서 "자연수는 isomorphism up to" — Peano triple 동형성.
Closed-universe 에서: Raw 의 임의의 2-원소 선택이 동형 numbering.
foldRaw 가 그 동형사상을 구체화.
-/

namespace E213.Lens.Number.Nat213.NumberingSystem

open E213.Theory E213.Theory.Closed

/-- 213-native numbering system: (Z, C) 가 distinct Raw 쌍. -/
structure NumberingSystem where
  Z : Raw
  C : Raw
  hZC : Z ≠ C

/-- system S 의 successor — Z chain 에 C 추가. -/
def succ (S : NumberingSystem) (n : Raw) : Raw :=
  slashOrSelf n S.C

/-- system S 의 n-th numeral. -/
def numeral (S : NumberingSystem) : Nat → Raw
  | 0     => S.Z
  | n + 1 => succ S (numeral S n)

/-! ### Method A as canonical NumberingSystem -/

/-- Canonical Method A — `Z = Raw.a`, `C = Raw.b`. -/
def methodA : NumberingSystem where
  Z := Raw.a
  C := Raw.b
  hZC := by
    intro h
    have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
    exact E213.Theory.Internal.Tree.noConfusion hval

/-- methodA 의 numeral 은 `Lens.Number.Nat213.Raw.numeral` 과 동일. -/
theorem methodA_numeral_eq_nat213 (n : Nat) :
    numeral methodA n = E213.Lens.Number.Nat213.Raw.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show succ methodA _ = E213.Lens.Number.Nat213.Raw.succ _
      rw [ih]; rfl

/-! ### Isomorphism via foldRaw

Method A → S 변환:
  - Raw.a (= methodA.Z) ↦ S.Z
  - Raw.b (= methodA.C) ↦ S.C
  - slash 에서 wrapper recombination 은 그대로 slashOrSelf

이 변환은 정확히 `foldRaw S.Z S.C slashOrSelf`.
-/

/-- Method A → S 동형 사상. -/
def isoFromMethodA (S : NumberingSystem) : Raw → Raw :=
  foldRaw S.Z S.C slashOrSelf

theorem isoFromMethodA_a (S : NumberingSystem) :
    isoFromMethodA S Raw.a = S.Z := rfl

theorem isoFromMethodA_b (S : NumberingSystem) :
    isoFromMethodA S Raw.b = S.C := rfl

/-- 보조 lemma — Raw.slash 결과는 Raw.b 와 다르다.  Raw.slash 는
    canonical Tree.slash 결과를 만들고, Tree.slash ≠ Tree.b. -/
private theorem slash_ne_b (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.b := by
  intro heq
  have hval : (Raw.slash x y h).val = (Raw.b).val := congrArg Subtype.val heq
  -- Raw.b.val = Tree.b (by Raw.b 정의).
  -- (Raw.slash x y h).val 은 Tree.slash _ _ — match 의 모든 분기.
  unfold Raw.slash at hval
  -- 이제 hval : (match ... with | .lt => ⟨Tree.slash..⟩ | ...) .val = Tree.b
  split at hval
  · exact E213.Theory.Internal.Tree.noConfusion hval
  · exact E213.Theory.Internal.Tree.noConfusion hval
  · -- .eq case: 이미 absurd 처리되어 도달 불가
    rename_i hcmp
    exact h (Subtype.ext (E213.Theory.Internal.Tree.cmp_eq_to_eq _ _ hcmp))

/-- 보조: Method A numeral 은 절대 Raw.b 가 아님. -/
theorem numeral_methodA_ne_b (n : Nat) : numeral methodA n ≠ Raw.b := by
  induction n with
  | zero =>
      -- numeral methodA 0 = methodA.Z = Raw.a ≠ Raw.b
      intro h
      have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
      exact E213.Theory.Internal.Tree.noConfusion hval
  | succ k ih =>
      -- numeral methodA (k+1) = slashOrSelf (numeral methodA k) Raw.b
      -- Since numeral methodA k ≠ Raw.b, this reduces to Raw.slash → ≠ Raw.b
      show slashOrSelf (numeral methodA k) Raw.b ≠ Raw.b
      rw [slashOrSelf_of_ne ih]
      exact slash_ne_b _ _ ih

/-- **Main isomorphism**: Method A 의 n-th numeral 을 isoFromMethodA 로
    매핑하면 system S 의 n-th numeral 이 나옴.

    이게 "두 numbering 이 동형이다"의 정확한 진술.  Peano triple
    동형성의 closed-universe 표현. -/
theorem iso_numeral (S : NumberingSystem) (n : Nat) :
    isoFromMethodA S (numeral methodA n) = numeral S n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      -- LHS = isoFromMethodA S (slashOrSelf (numeral methodA k) Raw.b)
      have hne : numeral methodA k ≠ Raw.b := numeral_methodA_ne_b k
      show isoFromMethodA S (slashOrSelf (numeral methodA k) Raw.b)
         = slashOrSelf (numeral S k) S.C
      rw [slashOrSelf_of_ne hne]
      -- isoFromMethodA = foldRaw S.Z S.C slashOrSelf
      -- Apply foldRaw_slash with slashOrSelf_comm
      show foldRaw S.Z S.C slashOrSelf
              (Raw.slash (numeral methodA k) Raw.b hne)
         = slashOrSelf (numeral S k) S.C
      rw [foldRaw_slash _ _ _ slashOrSelf_comm _ _ hne]
      -- LHS = slashOrSelf (foldRaw _ _ _ (numeral methodA k)) (foldRaw _ _ _ Raw.b)
      --     = slashOrSelf (isoFromMethodA S (numeral methodA k)) S.C
      show slashOrSelf (isoFromMethodA S (numeral methodA k)) S.C
         = slashOrSelf (numeral S k) S.C
      rw [ih]

end E213.Lens.Number.Nat213.NumberingSystem
