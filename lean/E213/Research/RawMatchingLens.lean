import E213.Research.IdentityLens

/-!
# Research.RawMatchingLens: Raw-matching Lens 는 모두 identity view

**정리**: `L : Lens Raw` 가 다음을 만족하면 `L.view = id`:

1. `L.base_a = Raw.a`
2. `L.base_b = Raw.b`
3. `L.combine x y = Raw.slash x y h` for all `x ≠ y`.

diagonal (`L.combine x x`) 은 자유 — view 에 영향 없음.

## 의의

`idLens` 는 specific choice (diagonal = Raw.a).  이 정리는
**Raw-level data 가 일치하면 view 는 반드시 identity** 임을
보여줌.  즉 idLens 의 공식적 id-ness 는 diagonal 선택 무관.

Universal property 의 강력한 form: off-diagonal 구조가 view
를 결정.  이는 Note 34-35 의 "diagonal 은 view 에 있을 때만
의미" 관찰의 더 강한 표현.
-/

namespace E213.Research.RawMatchingLens

open E213.Firmware E213.Hypervisor E213.Research.IdentityLens

/-- Raw-matching 조건 + diagonal 자유 Lens 는 view = id. -/
theorem rawMatching_view_is_id (L : Lens Raw)
    (hba : L.base_a = Raw.a)
    (hbb : L.base_b = Raw.b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              L.combine x y = Raw.slash x y h)
    (hsym : ∀ u v : Raw, L.combine u v = L.combine v u) :
    ∀ r : Raw, L.view r = r := by
  intro r
  induction r using Raw.rec with
  | a =>
      show L.base_a = Raw.a
      exact hba
  | b =>
      show L.base_b = Raw.b
      exact hbb
  | slash x y h ihx ihy =>
      have hfs : L.view (Raw.slash x y h)
                   = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hsym x y h
      rw [hfs, ihx, ihy]
      -- Now need: L.combine x y = Raw.slash x y h
      exact hslash x y h

end E213.Research.RawMatchingLens
