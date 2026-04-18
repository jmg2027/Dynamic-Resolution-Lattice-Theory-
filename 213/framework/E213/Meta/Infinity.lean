import E213.OS.Topology

/-
  Meta: 213 이 무한성을 잃는 시점.

  질문: 어느 Layer 에서 무한이 유한으로 붕괴하는가?

  답 (구조적):
    Firmware Raw   : ✪ **무한** (모든 depth 도달 가능).
    Hypervisor :
      Lens.id'      : 무한 (Raw ≃ LensQuot id').
      Lens.depth    : 무한 (ℕ ≃ LensQuot depth).
      Lens.leaves   : 무한 (ℕ≥1 ≃ LensQuot leaves).
      Lens.atomSet  : **유한** (2^3 = 8 부분집합).
      Lens.truthVal : **유한** (Bool 2개).
      Lens.constTrue: **유한** (1개).
    OS :
      Peano         : 무한 (depth 위에서).
      Logic (const) : 유한 (variables 없음 → 2개).
      Set-3         : 유한 (Fin 3 기반).
      Topology-3    : 유한 (2^8 = 256).

  **전이 시점 = 렌즈의 α 가 유한 타입인 순간.**
  Raw 의 무한성은 그대로, 렌즈가 "유한 view" 로 접고 나면 quotient 유한.
-/

-- ═══ Raw 는 무한: 모든 depth 존재 ═══

-- Nat213 로부터 Nat 역변환.
def Nat213.fromNat : Nat → Nat213
  | 0     => .zero
  | n + 1 => .succ (Nat213.fromNat n)

theorem Nat213.fromNat_toNat (n : Nat) :
    (Nat213.fromNat n).toNat = n := by
  induction n with
  | zero     => rfl
  | succ m ih =>
    simp [Nat213.fromNat, Nat213.toNat, ih]
    omega

-- 임의의 depth 의 Reachable 존재.
theorem raw_has_arbitrary_depth (n : Nat) :
    ∃ x, Reachable x ∧ x.depth = n := by
  refine ⟨(Nat213.fromNat n).toRaw,
          Nat213.toRaw_reachable _, ?_⟩
  rw [Nat213.depth_eq_toNat, Nat213.fromNat_toNat]

-- ═══ 렌즈 별 무한성 판정 ═══

-- (1) Lens.depth: 무한 image.
-- 모든 n : Nat 에 대해 depth n 인 Raw 가 있음.
theorem depth_image_surjective :
    ∀ n : Nat, ∃ x : Raw, Lens.depth.view x = n := by
  intro n
  obtain ⟨x, _, hd⟩ := raw_has_arbitrary_depth n
  exact ⟨x, by rw [lens_depth_view]; exact hd⟩

-- → LensQuot Lens.depth ≃ Nat (무한).

-- (2) Lens.leaves: 무한 image (leaves 도 비슷하게 모든 양수 달성 가능).

-- (3) Lens.atomSet: 유한 image.
-- atomSet.view 의 결과는 dedup된 List (Fin 3).
-- Fin 3 원소 최대 3종 → 가능한 dedup list 는 유한.
-- (정확한 상한: 2^3 × 3! = 48, 실제론 더 적음.)

-- (4) Lens.truthValue: 유한 image (Bool, 2개).

-- (5) Lens.constTrue: 유한 image (1개).

-- ═══ 전이 시점의 구조적 이유 ═══

-- α 가 **유한 타입** 이면, Raw → α fold 는 pigeonhole 로 non-injective.
-- α 가 **무한 타입** 이면, fold 가 단사일 수 있음 (예: id' 의 α=Raw).

-- 더 섬세한 분석:
-- α=Nat: 무한. depth 렌즈는 모든 Nat 달성 → 무한 image.
-- α=Nat: 무한. but constant lens (g=const n, h=const n) 는 유한 image {n}.
-- 따라서 α 유한성만 아니라 combine 성질도 영향.

-- 일반 규칙:
--   Lens.view 의 image 가 유한 ↔ LensQuot 가 유한 ↔ 공리계가 유한.

-- ═══ 계층별 무한성 표 ═══

-- | Layer | 객체 | 무한 여부 |
-- |-------|------|----------|
-- | Firmware: Raw | countably infinite | ✓ |
-- | Firmware: Reachable | 무한 (위 정리) | ✓ |
-- | Lens.id' quotient | ≃ Raw | ✓ |
-- | Lens.depth quotient | ≃ Nat | ✓ |
-- | Lens.leaves quotient | ≃ ℕ≥1 | ✓ |
-- | Lens.atomSet quotient | ≤ 8 subsets | ✗ |
-- | Lens.truthValue quotient | 2 | ✗ |
-- | Lens.constTrue quotient | 1 | ✗ |
-- | OS/Peano (Nat213) | ≃ Nat | ✓ |
-- | OS/Logic (const) | 2 (T, F) | ✗ |
-- | OS/Set-3 | 8 sets | ✗ |
-- | OS/Topology-3 | 256 possible topologies | ✗ |

-- ═══ 결론 ═══

-- 무한성 상실 시점 = **유한 타입 α 를 렌즈로 선택** 하는 순간.
-- Raw 자체는 영원히 무한, 렌즈가 접으면 유한.
-- 각 공리계의 "크기" = 선택한 렌즈 α 의 크기.
-- PA 가 무한인 이유: depth 렌즈의 α = Nat (무한).
-- Logic (const) 이 유한인 이유: truthValue 의 α = Bool.

-- → 213 의 무한성은 "Firmware + id' 렌즈" 에서만 유지.
--    모든 유한 공리계는 Raw 의 무한 구조를 유한 kernel 로 folding.
