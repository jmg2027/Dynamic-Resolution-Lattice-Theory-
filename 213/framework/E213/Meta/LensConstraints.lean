import E213.Meta.LensSearch

/-
  Lens Constraints: 렌즈 조합 의 제약조건 수학 증명.

  목적: "어떤 lens 조합이 valid 한가?"
  증명할 법칙:
    (1) Pair kernel = component kernel intersection.
    (2) Swap: L × M ≡ M × L (at kernel).
    (3) Associativity: (L × M) × N ≡ L × (M × N).
    (4) Monotonicity: refines 보존.
    (5) Anti-symmetry: refines 양쪽 ⇒ kernel 같음.
    (6) Trivial absorption: L × constTrue ≡ L.
    (7) Id minimum: L refines id' ⇒ L equiv 는 대각선.
-/

-- ═══ 제약 1: Pair kernel 은 component kernel 의 intersection ═══

theorem pair_kernel_intersection {α β : Type}
    (L : Lens α) (M : Lens β) (x y : Raw) :
    (L.pair M).equiv x y ↔ L.equiv x y ∧ M.equiv x y := by
  unfold Lens.equiv
  rw [pair_view, pair_view]
  constructor
  · intro h
    exact (Prod.mk.injEq _ _ _ _).mp h
  · intro ⟨h1, h2⟩
    exact (Prod.mk.injEq _ _ _ _).mpr ⟨h1, h2⟩

-- ═══ 제약 2: Swap — L × M ≡ M × L at kernel ═══

theorem pair_swap_kernel {α β : Type}
    (L : Lens α) (M : Lens β) (x y : Raw) :
    (L.pair M).equiv x y ↔ (M.pair L).equiv x y := by
  rw [pair_kernel_intersection, pair_kernel_intersection]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨b, a⟩ => ⟨a, b⟩⟩

-- ═══ 제약 3: Associativity ═══

theorem pair_assoc_kernel {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ) (x y : Raw) :
    ((L.pair M).pair N).equiv x y ↔ (L.pair (M.pair N)).equiv x y := by
  rw [pair_kernel_intersection, pair_kernel_intersection,
      pair_kernel_intersection, pair_kernel_intersection]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩,
         fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

-- ═══ 제약 4: Monotonicity — refines 보존 ═══

theorem pair_monotone_left {α α' β : Type}
    (L : Lens α) (L' : Lens α') (M : Lens β)
    (hLL' : L.refines L') :
    (L.pair M).refines (L'.pair M) := by
  intro x y h
  rw [pair_kernel_intersection] at h
  show (L'.pair M).equiv x y
  rw [pair_kernel_intersection]
  exact ⟨hLL' x y h.1, h.2⟩

-- ═══ 제약 5: Anti-symmetry at kernel ═══

-- 두 lens 가 서로 refine 하면 kernel 같음.
theorem refines_antisym_kernel {α β : Type}
    (L : Lens α) (M : Lens β)
    (hLM : L.refines M) (hML : M.refines L)
    (x y : Raw) : L.equiv x y ↔ M.equiv x y :=
  ⟨hLM x y, hML x y⟩

-- ═══ 제약 6: Id minimum (가장 섬세) ═══

theorem id_refines_all_kernel {α : Type} (L : Lens α) (x y : Raw) :
    Lens.id'.equiv x y → L.equiv x y := Lens.id_refines_all L x y

-- ═══ 제약 7: ConstTrue maximum (가장 거침) ═══

theorem all_refines_constTrue_kernel {α : Type}
    (L : Lens α) (x y : Raw) :
    L.equiv x y → Lens.constTrue.equiv x y :=
  Lens.refines_constTrue L x y

-- ═══ 제약 8: Id' kernel = diagonal ═══

theorem id_equiv_is_diagonal (x y : Raw) :
    Lens.id'.equiv x y ↔ x = y := Lens.id_equiv_iff_eq x y

-- ═══ 제약 9: ConstTrue kernel = universal ═══

theorem constTrue_equiv_is_universal (x y : Raw) :
    Lens.constTrue.equiv x y := Lens.constTrue_equiv_all x y

-- ═══ 제약 10: Pair 가 refines both ═══

theorem pair_refines_both {α β : Type} (L : Lens α) (M : Lens β) :
    (L.pair M).refines L ∧ (L.pair M).refines M :=
  ⟨Lens.pair_refines_left L M, Lens.pair_refines_right L M⟩

-- ═══ 종합: Lens Algebra (laws) ═══

-- | Law              | Status |
-- |------------------|--------|
-- | Kernel intersect | ✓ (Thm 1) |
-- | Swap symmetric   | ✓ (Thm 2) |
-- | Associative      | ✓ (Thm 3) |
-- | Monotone         | ✓ (Thm 4) |
-- | Anti-sym kernel  | ✓ (Thm 5) |
-- | Id minimum       | ✓ (Thm 6) |
-- | ConstTrue max    | ✓ (Thm 7) |
-- | Id diagonal      | ✓ (Thm 8) |
-- | ConstTrue univ   | ✓ (Thm 9) |
-- | Pair refines both | ✓ (Thm 10) |

-- ═══ 의미 ═══

-- 이 법칙 들 은 LensCat 의 structural properties.
-- Product (pair) 가 잘 정의됨 (universal property).
-- Initial (id') / Terminal (constTrue) 존재.
-- Refinement 는 antisymmetric at kernel level.
-- Lens 조합 = semilattice structure (pair = meet).

-- Lens Search Space 의 제약:
-- 1. 조합은 pair operator 중심.
-- 2. Kernel refinement partial order.
-- 3. Boundary (id' / constTrue).
-- 4. Associative + commutative at kernel.

-- 따라서 Search Space 탐색 은 이 algebra 를 respecting.
-- 새 lens 추가 시 기존 법칙 위반 안 해야.
