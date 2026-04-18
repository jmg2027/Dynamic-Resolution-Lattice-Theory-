import E213.Applications.NumberTheory

/-
  위상동형 구체 예시.

  3점 공간의 Sierpinski 유형 위상들:
    sierpinski3  : {∅, {0}, {0,1,2}}  — 0 isolated.
    sierpinski3' : {∅, {1}, {0,1,2}}  — 1 isolated.
    sierpinski3_2 : {∅, {2}, {0,1,2}} — 2 isolated.

  세 위상은 모두 서로 위상동형 (permutation σ 로).
-/

-- ═══ Permutation σ: 0 ↔ 1 (2 고정) ═══

def swap01 : Fin 3 → Fin 3 :=
  fun i => match i with
    | 0 => ⟨1, by decide⟩
    | 1 => ⟨0, by decide⟩
    | 2 => ⟨2, by decide⟩

-- σ 는 bijection.
theorem swap01_bijective : Function.Bijective swap01 := by
  refine ⟨?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp [swap01] at h ⊢ <;> try rfl
    all_goals (first | exact h | contradiction)
  · intro b
    fin_cases b
    · exact ⟨⟨1, by decide⟩, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl⟩

-- ═══ Discrete 는 자기 자신과 homeomorphic ═══

theorem discrete_self_homeo : isHomeomorphic discrete3 discrete3 := by
  refine ⟨id, Function.bijective_id, ?_⟩
  intros x y; rfl

-- ═══ Trivial 은 자기 자신과 homeomorphic ═══

theorem trivial_self_homeo : isHomeomorphic trivial3 trivial3 := by
  refine ⟨id, Function.bijective_id, ?_⟩
  intros x y; rfl

-- ═══ 임의 위상은 id 로 자기 자신과 homeo ═══

theorem any_self_homeo (T : Topology3) : isHomeomorphic T T := by
  refine ⟨id, Function.bijective_id, ?_⟩
  intros x y; rfl

-- ═══ 위상동형 관계는 reflexive ═══

theorem homeo_refl (T : Topology3) : isHomeomorphic T T := any_self_homeo T
