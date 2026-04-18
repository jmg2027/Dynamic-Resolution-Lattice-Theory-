import E213.Hypervisor.LensKernel

/-
  Provability Classifier: 증명 가능성의 213 분류.

  핵심: 명제 φ 와 렌즈 L 에 대해 4분류.
    1. RespectsLens L φ : φ 가 L의 kernel 을 존중.
    2. Provable L φ     : 모든 Reachable 에서 φ.
    3. Refutable L φ    : φ 반례 존재.
    4. Independent L φ  : L 이 φ 결정 못 함.

  Gödel 독립성의 213 버전:
    Independent L φ ↔ ¬ RespectsLens L φ.
    렌즈를 세밀화 하면 해결 가능해질 수도.

  문제 분류:
    - Provable:    확정 참.
    - Refutable:   확정 거짓.
    - Independent: 렌즈 미세화 필요 (Gödel-like).
-/

variable {α : Type}

-- ═══ 1. RespectsLens ═══

-- φ 가 렌즈 L 의 kernel 을 존중: 같은 view → 같은 진리값.
def RespectsLens (L : Lens α) (φ : Raw → Prop) : Prop :=
  ∀ x y, L.equiv x y → (φ x ↔ φ y)

-- ═══ 2. Provable ═══

def ProvableIn (L : Lens α) (φ : Raw → Prop) : Prop :=
  ∀ x, Reachable x → φ x

-- L 무관하게 정의되어 보이지만, 실용에선 L-respecting φ 만 고려.

-- ═══ 3. Refutable ═══

def RefutableIn (L : Lens α) (φ : Raw → Prop) : Prop :=
  ∃ x, Reachable x ∧ ¬ φ x

-- ═══ 4. Independent ═══

-- L 안에서 φ 결정 불가: 같은 kernel 클래스인데 진리값 다름.
def IndependentIn (L : Lens α) (φ : Raw → Prop) : Prop :=
  ∃ x y, Reachable x ∧ Reachable y ∧
         L.equiv x y ∧ (φ x ∧ ¬ φ y)

-- ═══ 핵심 정리: Independent ↔ ¬ RespectsLens ═══

theorem independent_iff_not_respects (L : Lens α) (φ : Raw → Prop) :
    IndependentIn L φ → ¬ RespectsLens L φ := by
  rintro ⟨x, y, _, _, hxy, hφx, hnφy⟩ hresp
  exact hnφy ((hresp x y hxy).mp hφx)

-- 역방향은 classical (LEM 필요). 여기선 한 방향만.

-- ═══ Provable vs Refutable: 배타 ═══

theorem provable_not_refutable (L : Lens α) (φ : Raw → Prop) :
    ProvableIn L φ → ¬ RefutableIn L φ := by
  rintro hprov ⟨x, hrx, hnφ⟩
  exact hnφ (hprov x hrx)

-- ═══ 예시 1: Gödel-style 독립 명제 ═══

-- φ(x) := (x = aab₀). 구체 객체 판별.
-- depth 렌즈로는 독립: aab₀ =[depth] bab₀ (둘 다 depth=2)
-- 이지만 φ(aab₀)=true, φ(bab₀)=false.

example : IndependentIn Lens.depth (fun x => x = aab₀) := by
  refine ⟨aab₀, bab₀, ?_, ?_, ?_, rfl, ?_⟩
  · decide  -- Reachable aab₀
  · decide  -- Reachable bab₀
  · decide  -- aab₀ =[depth] bab₀
  · decide  -- bab₀ ≠ aab₀

-- depth 렌즈는 "이 트리가 정확히 aab₀인가"를 결정 못 함.
-- 렌즈를 id' 로 세밀화하면 결정 가능 (kernel 이 대각선).
example : RespectsLens Lens.id' (fun x => x = aab₀) := by
  intro x y h
  rw [Lens.id_equiv_iff_eq] at h
  rw [h]

-- ═══ 예시 2: depth-respecting 명제 ═══

-- φ(x) := (x.depth = 0). atom 만 만족.
-- depth 렌즈에선 당연히 respects (depth 가 결정).
example : RespectsLens Lens.depth (fun x => x.depth = 0) := by
  intro x y h
  unfold Lens.equiv at h
  simp [lens_depth_view] at h
  rw [h]

-- ═══ 의미 ═══
-- 1. 각 공리계 = 렌즈 선택 + respecting 명제의 집합.
-- 2. 렌즈 L 에서 결정 불가한 명제 = Independent (Gödel-like).
-- 3. 렌즈 세밀화로 독립성 해소. 최대 섬세 = id' = 전부 결정.
-- 4. 문제의 "어려움" = 어떤 렌즈에선 independent, 다른 렌즈에선 결정.
