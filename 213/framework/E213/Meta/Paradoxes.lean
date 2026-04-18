import E213.Meta.SelfReference

/-
  Meta: 고전 역설들의 213 해석.

  주요 결과:
    1. Russell 역설은 / 위에서 **자동 회피**.
       이유: Raw 는 유한 tree. memSet 에서 x ∈ s 이면 depth x < depth s.
       따라서 x ∈ x 불가.
    2. Liar 역설 (Gödel) 은 렌즈 의존적.
    3. Cantor 대각선: id' 외 모든 fold 단사 아님 (이미 증명).

  213 본질적 안전성: 무한 comprehension 없음 → 역설 생성 기반 없음.
-/

-- ═══ 부분구조 lemma: memSet 은 depth 증가 방향 ═══

theorem memSet_implies_depth_lt {x s : Raw} :
    s.memSet x = true → x.depth < s.depth := by
  induction s with
  | atom _ => intro h; simp [Raw.memSet] at h
  | rel a b _ ihb =>
    intro h
    simp only [Raw.memSet, Bool.or_eq_true] at h
    rcases h with hEq | hMem
    · have hxa : x = a := by
        rw [beq_iff_eq] at hEq; exact hEq
      subst hxa
      simp [Raw.depth]; omega
    · have := ihb hMem
      simp [Raw.depth]; omega

-- ═══ Russell 역설 회피 ═══

-- 자기 포함 불가.
theorem no_self_membership (x : Raw) : ¬ (x.memSet x = true) := by
  intro h
  exact Nat.lt_irrefl _ (memSet_implies_depth_lt h)

-- Russell 집합 R = {x : ¬ x ∈ x} 의 예비 버전.
-- R 이 있다면 R ∈ R ⟺ R ∉ R 이어야 함 (고전).
-- 213: 모든 x 가 ¬ x ∈ x (no_self_membership).
-- 따라서 R = "모든 것의 집합." 하지만 Raw 에선 무한 집합 표현 불가.
-- → Russell 집합 자체가 존재하지 않음.

theorem all_raw_no_self_mem (x : Raw) : x.memSet x = false := by
  by_contra h
  have : x.memSet x = true := by
    cases hm : x.memSet x with
    | true => rfl
    | false => exact absurd hm h
  exact no_self_membership _ this

-- 의미: 213 에서 Russell 조건 (¬ x ∈ x) 은 trivial 하게 모든 x 가 만족.
-- 고전에서 모순을 낳는 자기 포함 가능성이 / 구조에 없음.
-- 재귀 comprehension 없이 finite tree 뿐.

-- ═══ Gödel-style 자기 참조의 213 한계 ═══

-- 명제 φ : Raw → Prop 를 Raw 자체로 encode 하려면:
--   (1) 충분한 encode/decode 구조.
--   (2) 자기 참조 고정점 operator.
-- 213 의 유한 tree 만으로는 (1), (2) 모두 Lean 밖 meta-level 필요.
-- 단, "φ 가 L 에서 Independent" 는 φ 와 L 의 성질로 표현 가능 (Provability.lean).

-- 결론: Gödel 불완전성의 **구조적 원천** 은 / 에서
--   "렌즈의 유한 분해 능력" vs "Raw 의 무한 구조" 간 차이.
--   이 차이는 FoldInjective 의 comm h → non-injective 로 이미 형식화됨.

-- ═══ Cantor 대각선의 213 버전 (이미 존재) ═══

-- 모든 commutative combine 의 fold 는 단사 아님.
-- → 유한 공리계로 Raw 소진 불가.
example (L : Lens Nat) (hcomm : ∀ a b, L.combine a b = L.combine b a) :
    ¬ Function.Injective L.view :=
  fold_not_injective_of_comm L.atomValue L.combine hcomm
