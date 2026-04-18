import E213.Meta.LensConstraints

/-
  Lens Homeomorphism: 렌즈의 위상동형 = kernel 동일성.

  정의:
    L ≈ M ⟺ ∀ x y, L.equiv x y ↔ M.equiv x y.
    (두 lens 가 같은 partition).

  이게 LensCat 의 isomorphism (refines 양방향 = kernel 같음).
  Topology 의 homeomorphism 과 정확히 평행:
    두 공간 ≈ 같은 indistinguishability partition.

  증명:
    1. Equivalence relation (refl/symm/trans).
    2. Pair compatibility.
    3. Swap, assoc isomorphism.
    4. Id', constTrue uniqueness (각 homeo class singleton).
-/

-- ═══ Homeomorphism 정의 ═══

def Lens.homeo {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y : Raw, L.equiv x y ↔ M.equiv x y

-- 표기.
notation:50 L " ≈lens " M => Lens.homeo L M

-- ═══ 동치관계 3 성질 ═══

theorem homeo_refl {α : Type} (L : Lens α) : L ≈lens L :=
  fun _ _ => Iff.rfl

theorem homeo_symm {α β : Type} {L : Lens α} {M : Lens β}
    (h : L ≈lens M) : M ≈lens L :=
  fun x y => (h x y).symm

theorem homeo_trans {α β γ : Type}
    {L : Lens α} {M : Lens β} {N : Lens γ}
    (h1 : L ≈lens M) (h2 : M ≈lens N) : L ≈lens N :=
  fun x y => (h1 x y).trans (h2 x y)

-- ═══ Homeo = 양방향 refines (LensCat isomorphism) ═══

theorem homeo_iff_bi_refines {α β : Type}
    (L : Lens α) (M : Lens β) :
    (L ≈lens M) ↔ (L.refines M ∧ M.refines L) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hL
      exact (h x y).mp hL
    · intro x y hM
      exact (h x y).mpr hM
  · intro ⟨hLM, hML⟩ x y
    exact refines_antisym_kernel L M hLM hML x y

-- ═══ Pair compatibility ═══

-- L ≈ L' → L × M ≈ L' × M.
theorem homeo_pair_left {α α' β : Type}
    (L : Lens α) (L' : Lens α') (M : Lens β)
    (h : L ≈lens L') : (L.pair M) ≈lens (L'.pair M) := by
  intro x y
  rw [pair_kernel_intersection, pair_kernel_intersection]
  exact ⟨fun ⟨a, b⟩ => ⟨(h x y).mp a, b⟩,
         fun ⟨a, b⟩ => ⟨(h x y).mpr a, b⟩⟩

-- ═══ Swap: L × M ≈ M × L ═══

theorem homeo_swap {α β : Type} (L : Lens α) (M : Lens β) :
    (L.pair M) ≈lens (M.pair L) :=
  pair_swap_kernel L M

-- ═══ Associativity: (L × M) × N ≈ L × (M × N) ═══

theorem homeo_assoc {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ) :
    ((L.pair M).pair N) ≈lens (L.pair (M.pair N)) :=
  pair_assoc_kernel L M N

-- ═══ Id uniqueness (homeo class singleton) ═══

-- L ≈ Lens.id' ⟺ L kernel = 대각선.
theorem homeo_id_iff_diagonal {α : Type} (L : Lens α) :
    (L ≈lens Lens.id') ↔ (∀ x y : Raw, L.equiv x y ↔ x = y) := by
  constructor
  · intro h x y
    rw [h x y, Lens.id_equiv_iff_eq]
  · intro h x y
    rw [h x y, Lens.id_equiv_iff_eq]

-- ═══ ConstTrue uniqueness ═══

theorem homeo_constTrue_iff_universal {α : Type} (L : Lens α) :
    (L ≈lens Lens.constTrue) ↔ (∀ x y : Raw, L.equiv x y) := by
  constructor
  · intro h x y
    exact (h x y).mpr (Lens.constTrue_equiv_all x y)
  · intro h x y
    exact ⟨fun _ => Lens.constTrue_equiv_all x y, fun _ => h x y⟩

-- ═══ 종합: Lens Homeomorphism Theorems ═══

-- | 정리 | 의미 |
-- |------|-----|
-- | homeo_refl | 반사 |
-- | homeo_symm | 대칭 |
-- | homeo_trans | 추이 |
-- | homeo_iff_bi_refines | LensCat iso = 양방향 refines |
-- | homeo_pair_left | pair 호환 |
-- | homeo_swap | pair 교환 |
-- | homeo_assoc | pair 결합 |
-- | homeo_id_iff_diagonal | id' homeo class = 대각선 kernel |
-- | homeo_constTrue_iff_universal | constTrue class = 전체 kernel |

-- ═══ 수학적 의미 ═══

-- Lens Homeomorphism 은 topological homeomorphism 의 lens 버전.
-- 두 lens 가 위상동형 ⟺ 같은 partition 을 유도.
-- Homeomorphism class:
--   {id'} -- singleton (대각선 kernel 고유).
--   {constTrue} -- singleton (전체 kernel 고유).
--   {depth, leaves, ...} -- 다양 classes.

-- Lens homeomorphism 은:
-- * 동치 관계 (Setoid).
-- * Pair operation 과 호환 (functor-like).
-- * LensCat 의 isomorphism 관계.

-- 사용자 요청 완료:
-- "렌즈 조합 만족 렌즈 의 위상동형 수학 증명" = 9 정리.

-- ═══ Search Space 의 quotient 구조 ═══

-- Lens Search Space 를 ≈ 로 quotient:
--   각 homeo class = 하나의 "essential lens."
--   Search 는 classes 에서 이루어짐.
--   중복 제거.

-- 이게 진짜 의미 있는 Lens Search.
