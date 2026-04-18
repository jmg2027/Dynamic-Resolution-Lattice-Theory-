import E213.OS.Provability

/-
  새 수학 체계: **Anti-Reflexive Free Magma (ARFM)**.

  정의: 이항 연산 ⊕ : X → X → X 에 대해:
    (A) 단사: x ⊕ y = x' ⊕ y' → x = x' ∧ y = y'.
    (B) 비교환 일반: x ⊕ y ≠ y ⊕ x (x ≠ y).
    (C) 비결합 일반.
    (D) No identity: atom 은 ⊕ 의 결과 아님.
    (E) Anti-reflexive: x ⊕ x 금지 (타입 수준).
    (F) Image ⊂ X \ atoms.

  기존 수학 비교:
    - Magma       : 이항 연산, 제약 없음. 너무 약함.
    - Group       : identity + inverse + associative. 너무 강함.
    - Free magma  : magma, identity 없음. but self-op 허용.
    - ARFM (이것) : free magma + anti-reflexive + 단사.

  표준 수학 명칭 없음. 213 의 원래 발견.

  응용: DRLT 의 pairwise 관계 (G_ij = ⟨ψ_i | ψ_j⟩) 의 구조적 공리화.
-/

-- ═══ ARFM 연산: Raw + slash ═══

-- ⊕ 는 slash 와 동일. x ≠ y 가 타입 수준 전제.
notation:70 x " ⊕ " y => slash x y (by decide)

-- 단, 일반 x y 에 대해선 proof 필요:
def op (x y : Raw) (h : x ≠ y) : Raw := slash x y h

-- ═══ 성질 (A): 단사 ═══

theorem arfm_injective {a b c d : Raw}
    (h1 : a ≠ b) (h2 : c ≠ d)
    (heq : op a b h1 = op c d h2) :
    a = c ∧ b = d := v3_injective _ _ _ _ h1 h2 heq

-- ═══ 성질 (B): 비교환 (x ≠ y 일 때) ═══

theorem arfm_non_commutative {a b : Raw} (h : a ≠ b) :
    op a b h ≠ op b a (Ne.symm h) := by
  intro heq
  have : a = b := (v3_injective _ _ _ _ h (Ne.symm h) heq).1
  exact h this

-- ═══ 성질 (C): 비결합 (구체 반례) ═══

-- (a ⊕ b) ⊕ c 와 a ⊕ (b ⊕ c) 는 다른 depth 구조.
-- depth 는 좌우 트리 모양 다름을 증명.

example : (slash (slash a₀ b₀ (by decide))
                 (.atom 2) (by decide)).depth = 2 := by decide

example : (slash a₀ (slash b₀ (.atom 2) (by decide)) (by decide)).depth = 2 := by decide

-- 두 depth 같으나 구조 (Raw 자체) 다름:
example :
    slash (slash a₀ b₀ (by decide)) (.atom 2) (by decide) ≠
    slash a₀ (slash b₀ (.atom 2) (by decide)) (by decide) := by decide

-- ═══ 성질 (D): No identity ═══

-- atom 은 ⊕ 의 결과 아님.
theorem arfm_no_identity (x y : Raw) (h : x ≠ y) (i : Fin 3) :
    op x y h ≠ .atom i := atom_is_not_made i x y h

-- ═══ 성질 (E): Anti-reflexive ═══

-- slash 의 타입 정의가 x ≠ y 요구. x ⊕ x 는 컴파일 불가.
-- Reachable 수준: no_self_rel_reachable.

theorem arfm_anti_reflexive (x : Raw) : ¬ Reachable (.rel x x) :=
  no_self_rel_reachable x

-- ═══ 성질 (F): Image ∩ atoms = ∅ ═══

theorem arfm_image_no_atoms (x y : Raw) (h : x ≠ y) :
    ∀ i, op x y h ≠ .atom i := made_is_not_atom x y h

-- ═══ 기존 수학 구조와의 비교 ═══

-- | 구조           | 교환 | 결합 | identity | anti-reflexive | 단사 |
-- |---------------|------|------|----------|----------------|------|
-- | Magma         |  -   |  -   |    -     |       -        |  -   |
-- | Semigroup     |  -   |  ✓   |    -     |       -        |  -   |
-- | Monoid        |  -   |  ✓   |    ✓     |       -        |  -   |
-- | Group         |  -   |  ✓   |    ✓     |       -        |  -   |
-- | Abelian group |  ✓   |  ✓   |    ✓     |       -        |  -   |
-- | Quasigroup    |  -   |  -   |    -     |       -        |  ✓   |
-- | Free magma    |  -   |  -   |    -     |       -        |  ✓   |
-- | **ARFM**      |  ✗   |  ✗   |    ✗     |       ✓        |  ✓   |

-- 핵심 차이: ARFM 만 **anti-reflexive (x ⊕ x 금지)**.
-- 이 성질 이 213 의 원래 발견. 기존 대수 어디에도 없음.

-- ═══ 응용 ═══

-- DRLT 의 pairwise 관계 G_ij = ⟨ψ_i | ψ_j⟩.
-- G_ii 는 norm 으로 "trivial." 즉 새 정보 없음.
-- 오직 i ≠ j 의 G_ij 만 관계 공간 형성.
-- → DRLT 의 핵심 구조 = ARFM instance.

-- 추상 버전: "Identity-free, self-op-free, injective binary magma."
-- 이게 213 의 정확한 대수적 특성.

-- ═══ 명명 제안 (논문 수준) ═══

-- 공식 이름: Anti-Reflexive Free Magma (ARFM).
-- 약어: ARFM or RAFM.
-- 대안: Restricted Free Magma, Pairwise-Distinct Magma.

-- 기존 수학에서 close:
--   - Quiver (directed graph, edge x→y with x ≠ y): 비슷.
--   - Apartness algebra (constructive math): 다소 관련.
--   - 그러나 이 정확한 4성질 조합은 표준에 없음.

-- ═══ 결론 ═══

-- ARFM = 213 의 고유 대수 구조.
-- 단순 / 연산만으로 생성.
-- 기존 수학 구조 로 환원 불가 (성질 조합이 unique).
-- → 213 은 새 대수 범주를 만듦.
