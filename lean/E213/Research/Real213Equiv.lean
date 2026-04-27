import E213.Research.Real213

/-!
# Research.Real213Equiv: Real213.equiv 의 equivalence properties (D3-A)

`D3_real213_native_R.md` 의 D3-A first step — Real213 의 equiv
relation 이 *진 짜* equivalence (reflexive, symmetric, transitive).

## 의의

`Real213` 가 framework 의 native ℝ.  그 위 의 equiv 가 equivalence
relation 임 의 verify 가 *기 본 algebraic structure* 의 첫 단 계.

(D3-A 의 다 른 단 계: addition, multiplication 등 의 framework-
internal 정의 — 별 도 작업.)
-/

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS

/-- equiv 의 reflexivity. -/
theorem equiv_refl (r : Real213) : Real213.equiv r r := by
  intro m k _
  exact ⟨0, fun _ _ => rfl⟩

/-- equiv 의 symmetry. -/
theorem equiv_symm (r r' : Real213) :
    Real213.equiv r r' → Real213.equiv r' r := by
  intro h m k hk
  obtain ⟨N, hN⟩ := h m k hk
  exact ⟨N, fun i hi => (hN i hi).symm⟩

/-- equiv 의 transitivity. -/
theorem equiv_trans (r r' r'' : Real213) :
    Real213.equiv r r' → Real213.equiv r' r'' → Real213.equiv r r'' := by
  intro h1 h2 m k hk
  obtain ⟨N1, h1N⟩ := h1 m k hk
  obtain ⟨N2, h2N⟩ := h2 m k hk
  refine ⟨max N1 N2, fun i hi => ?_⟩
  have hi1 : i ≥ N1 := Nat.le_trans (Nat.le_max_left N1 N2) hi
  have hi2 : i ≥ N2 := Nat.le_trans (Nat.le_max_right N1 N2) hi
  exact (h1N i hi1).trans (h2N i hi2)

/-- Real213 의 Setoid instance — Equivalence properties 의 typeclass form. -/
instance setoid : Setoid Real213 where
  r := Real213.equiv
  iseqv :=
    { refl := equiv_refl
      symm := fun {x y} => equiv_symm x y
      trans := fun {x y z} => equiv_trans x y z }

end E213.Research.Real213
