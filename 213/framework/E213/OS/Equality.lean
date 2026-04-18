import E213.OS.Peano
import E213.Hypervisor.LensKernel

/-
  질문: Peano의 =은 213에서 어떻게 나오는가?

  답:
    - 213 Firmware 에는 = 없음. ≠ 만 (slash 전제).
    - Lean (Hardware) 이 = 제공 (DecidableEq Raw).
    - Hypervisor 의 Lens kernel (LensKernel.lean) 이 일반 등호 생성.
    - Peano 의 = 은 Lens.id' (가장 섬세 렌즈) 의 kernel 특수 경우.

  환원 체인:
    m = n  ↔  m.toRaw = n.toRaw                  (Nat213 단사 embedding)
           ↔  m.toRaw =[Lens.id'] n.toRaw        (id' kernel)
           ↔  ¬ (m.toRaw ≠ n.toRaw)              (≠ 의 부정)

  정직한 의미:
    Lens.id'.equiv 가 유일한 "완전한 같다."
    다른 렌즈의 kernel 은 더 거친 "같다" → 다른 공리계.
    Peano 는 Lens.id' 를 써서 (실질적으로) Lean 의 = 그대로.
-/

-- ═══ 환원 1: Nat213의 =  ↔  Raw의 = (toRaw injective) ═══

theorem Nat213.eq_iff_toRaw_eq (m n : Nat213) :
    m = n ↔ m.toRaw = n.toRaw :=
  ⟨fun h => by rw [h], toRaw_inj⟩

-- ═══ 환원 2: Raw의 =  ↔  Lens.id'.equiv (가장 섬세 kernel) ═══

theorem Nat213.eq_iff_id_equiv (m n : Nat213) :
    m = n ↔ Lens.id'.equiv m.toRaw n.toRaw := by
  rw [eq_iff_toRaw_eq, Lens.id_equiv_iff_eq]

-- ═══ 환원 3: Lens.id'.equiv  ↔  ¬ (Firmware 의 ≠) ═══

theorem Nat213.eq_iff_not_ne (m n : Nat213) :
    m = n ↔ ¬ (m.toRaw ≠ n.toRaw) := by
  rw [eq_iff_toRaw_eq]
  exact ⟨fun h hne => hne h, fun h => Classical.not_not.mp h⟩

-- ═══ 결론 ═══
-- Peano 의 = 은 Lens.id' 의 kernel. 가장 섬세 렌즈.
-- 다른 렌즈 (depth, leaves, atomSet) 는 거친 kernel → 다른 "같다."
-- 각 공리계는 **자기 렌즈의 kernel 을 = 로 선언** 한 것.
-- 이것이 "같다 를 공리로 추가" 의 실제 의미: 렌즈 고정.
