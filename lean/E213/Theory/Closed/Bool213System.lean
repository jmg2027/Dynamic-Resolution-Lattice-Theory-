import E213.Theory.Closed.Bool213
import E213.Theory.Raw.Rec

/-!
# Theory.Closed.Bool213System — meta pattern over (T, F) choices

Bool213 도 Nat213 처럼 무한히 많은 구현 가능.  임의의 두 distinct Raw
`T ≠ F` 가 valid Bool213 system 을 줌.  메타 패턴으로 동형성 확인.

## 무한히 많은 Bool213

  - methodA: T = Raw.a,        F = Raw.b
  - methodB: T = Raw.b,        F = Raw.a       (swap)
  - methodC: T = slash a b,    F = Raw.a       (slash + leaf)
  - methodD: T = Raw.a,        F = slash a b   (역)
  - ...infinitely many

각 (T, F) with T ≠ F 가 valid system.  Raw 의 canonical Tree 가
무한히 많으니 system 도 무한히 많음.

## 동형성

서로 다른 system A, B 사이 iso 사상은:
  iso A B : Raw → Raw
    r ↦ if r = A.T then B.T
        else if r = A.F then B.F
        else r  (fallback)

이게 not, and 등 op 를 보존 (T↔F 교환, table 동등).
-/

namespace E213.Theory.Closed.Bool213System

open E213.Theory E213.Theory.Closed

/-- 213-native Boolean system: (T, F) 가 distinct Raw 쌍. -/
structure BooleanSystem where
  T : Raw
  F : Raw
  hTF : T ≠ F

/-- system S 에서 negation (= T ↔ F swap, 다른 입력은 그대로). -/
def not (S : BooleanSystem) (r : Raw) : Raw :=
  if r = S.T then S.F
  else if r = S.F then S.T
  else r

/-- system S 에서 conjunction (and). 표 정의. -/
def and (S : BooleanSystem) (x y : Raw) : Raw :=
  if x = S.T ∧ y = S.T then S.T else S.F

/-! ### Method A: 정칙 (T = Raw.a, F = Raw.b) — Bool213.lean 의 기본 -/

def methodA : BooleanSystem where
  T := Raw.a
  F := Raw.b
  hTF := by
    intro h
    have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
    exact Theory.Internal.Tree.noConfusion hval

end E213.Theory.Closed.Bool213System

namespace E213.Theory.Closed.Bool213System

open E213.Theory E213.Theory.Closed

/-! ### Iso between systems -/

/-- A → B 동형 사상.  T ↦ T', F ↦ F', 그 외 fallback. -/
def iso (A B : BooleanSystem) (r : Raw) : Raw :=
  if r = A.T then B.T
  else if r = A.F then B.F
  else r

theorem iso_T (A B : BooleanSystem) : iso A B A.T = B.T := by
  unfold iso; rw [if_pos rfl]

theorem iso_F (A B : BooleanSystem) : iso A B A.F = B.F := by
  unfold iso
  rw [if_neg (Ne.symm A.hTF), if_pos rfl]

/-! ### Iso preserves operations -/

/-- iso 가 not 보존.  T → F → T 순환을 두 system 모두에서 일치시킴. -/
theorem iso_not (A B : BooleanSystem) (r : Raw) (hr : r = A.T ∨ r = A.F) :
    iso A B (not A r) = not B (iso A B r) := by
  rcases hr with hr | hr
  · -- r = A.T → not A r = A.F → iso = B.F.  RHS: iso r = B.T → not B B.T = B.F.
    subst hr
    show iso A B (not A A.T) = not B (iso A B A.T)
    rw [iso_T]
    show iso A B (not A A.T) = not B B.T
    unfold not
    rw [if_pos rfl, if_pos rfl]
    -- Now: iso A B A.F = B.F. By iso_F.
    exact iso_F A B
  · -- r = A.F → not A r = A.T → iso = B.T.  RHS: iso r = B.F → not B B.F = B.T.
    subst hr
    show iso A B (not A A.F) = not B (iso A B A.F)
    rw [iso_F]
    show iso A B (not A A.F) = not B B.F
    unfold not
    rw [if_neg (Ne.symm A.hTF), if_pos rfl, if_neg (Ne.symm B.hTF), if_pos rfl]
    -- Now: iso A B A.T = B.T. By iso_T.
    exact iso_T A B

/-- iso 가 and 보존 (양쪽 인자 모두 valid Bool 인 경우). -/
theorem iso_and (A B : BooleanSystem) (x y : Raw)
    (hx : x = A.T ∨ x = A.F) (hy : y = A.T ∨ y = A.F) :
    iso A B (and A x y) = and B (iso A B x) (iso A B y) := by
  -- 4 cases: (T,T), (T,F), (F,T), (F,F).
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy
  · -- (T, T): and = T → iso = B.T.  RHS: iso T = B.T, iso T = B.T, and B.T B.T = B.T.
    show iso A B (and A A.T A.T) = and B (iso A B A.T) (iso A B A.T)
    rw [iso_T]
    show iso A B (and A A.T A.T) = and B B.T B.T
    unfold and
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
    exact iso_T A B
  · -- (T, F): and = F → iso = B.F.  RHS: iso T = B.T, iso F = B.F, and B.T B.F = B.F.
    show iso A B (and A A.T A.F) = and B (iso A B A.T) (iso A B A.F)
    rw [iso_T, iso_F]
    unfold and
    rw [if_neg (fun ⟨_, h⟩ => A.hTF h.symm), if_neg (fun ⟨_, h⟩ => B.hTF h.symm)]
    exact iso_F A B
  · -- (F, T): and = F → iso = B.F.  RHS: iso F = B.F, iso T = B.T, and B.F B.T = B.F.
    show iso A B (and A A.F A.T) = and B (iso A B A.F) (iso A B A.T)
    rw [iso_T, iso_F]
    unfold and
    rw [if_neg (fun ⟨h, _⟩ => A.hTF h.symm), if_neg (fun ⟨h, _⟩ => B.hTF h.symm)]
    exact iso_F A B
  · -- (F, F): and = F → iso = B.F.  RHS: iso F = B.F, iso F = B.F, and B.F B.F = B.F.
    show iso A B (and A A.F A.F) = and B (iso A B A.F) (iso A B A.F)
    rw [iso_F]
    unfold and
    rw [if_neg (fun ⟨h, _⟩ => A.hTF h.symm), if_neg (fun ⟨h, _⟩ => B.hTF h.symm)]
    exact iso_F A B

end E213.Theory.Closed.Bool213System
