import E213.OS.Provability

/-
  OS Layer: Propositional Logic 을 / 위에.

  렌즈: Lens.truthValue (α = Bool).
  인코딩:
    ⊤       → atom 0
    ⊥       → atom 1
    p → q   → rel p.toRaw q.toRaw   (implication 은 비대칭 → / 와 자연)

  Peano 와 평행 구조:
    Peano  : depth 렌즈 + atom 0 = zero, atom 1 = succ 시작자.
    Logic  : truthValue 렌즈 + atom 0 = ⊤, atom 1 = ⊥.
  같은 / 공리, 다른 렌즈 선택 → 다른 공리계.

  변수 없는 상수 logic. Assignment 도입은 향후.
-/

-- ═══ Prop213: 자기 타입 ═══

inductive Prop213 where
  | tru : Prop213
  | fls : Prop213
  | imp : Prop213 → Prop213 → Prop213
  deriving DecidableEq, Repr

def Prop213.toRaw : Prop213 → Raw
  | .tru     => a₀
  | .fls     => b₀
  | .imp p q => .rel p.toRaw q.toRaw

-- Raw 수준 진리값 (나중에 렌즈와 일치 증명).
def Prop213.truth : Prop213 → Bool
  | .tru     => true
  | .fls     => false
  | .imp p q => !p.truth || q.truth

-- ═══ Bool 렌즈 ═══

-- atom 0 = ⊤ = true, 그 외 atom = false.
-- rel x y = implication: !x || y.
def Lens.truthValue : Lens Bool :=
  ⟨fun i => i.val == 0, fun a b => !a || b⟩

-- ═══ Prop213.truth 와 Bool 렌즈 일치 ═══

theorem Prop213.truth_eq_lens (p : Prop213) :
    Lens.truthValue.view p.toRaw = p.truth := by
  induction p with
  | tru => rfl
  | fls => rfl
  | imp p q ihp ihq =>
    show Lens.truthValue.view (.rel p.toRaw q.toRaw) =
         (!p.truth || q.truth)
    simp [Lens.view, Raw.fold, Lens.truthValue]
    rw [show Lens.truthValue.view p.toRaw = p.truth from ihp]
    rw [show Lens.truthValue.view q.toRaw = q.truth from ihq]

-- ═══ Tautology: 모든 상수 assignment 에서 참 ═══

def Prop213.isTautology (p : Prop213) : Prop := p.truth = true

instance (p : Prop213) : Decidable p.isTautology :=
  inferInstanceAs (Decidable _)

-- 기본 예시 (decide 검증).
example : Prop213.tru.isTautology := by decide                       -- ⊤
example : ¬ Prop213.fls.isTautology := by decide                     -- ¬ ⊥
example : (Prop213.imp .fls .tru).isTautology := by decide           -- ⊥ → ⊤
example : (Prop213.imp .tru .tru).isTautology := by decide           -- ⊤ → ⊤
example : ¬ (Prop213.imp .tru .fls).isTautology := by decide         -- ¬ (⊤ → ⊥)
example : (Prop213.imp .fls .fls).isTautology := by decide           -- ⊥ → ⊥

-- p → p (자기 자신): 근데 rel 에 요구되는 p ≠ p 불가.
-- 따라서 p → p 식은 Raw 수준에선 slash 로 만들 수 없음 (a/a 거부).
-- Prop213 에선 imp p p 으로 만들 수 있지만 toRaw 가 rel p.toRaw p.toRaw.
-- Reachable 이 아님 (no_self_rel_reachable).
-- → 자기참조 tautology 는 / 구조 밖.
example : ¬ Reachable (Prop213.imp .tru .tru).toRaw := by decide

-- ═══ Provability Classifier 적용 ═══

-- Raw 수준 명제: "이 Raw 의 truthValue = true".
def isTrue : Raw → Prop := fun x => Lens.truthValue.view x = true

instance : DecidablePred isTrue := fun x =>
  inferInstanceAs (Decidable (Lens.truthValue.view x = true))

-- truthValue 렌즈는 isTrue 를 자동 respects (정의상).
theorem isTrue_respects : RespectsLens Lens.truthValue isTrue := by
  intro x y h
  unfold isTrue Lens.equiv at h ⊢
  rw [h]

-- 그러나 Provable 도 Refutable 도 아님: 양쪽 증거 있음.
-- atom 0 은 true, atom 1 은 false.
example : isTrue a₀ := by decide
example : ¬ isTrue b₀ := by decide

-- Refutable 확정.
example : RefutableIn Lens.truthValue isTrue := by
  refine ⟨b₀, ?_, ?_⟩
  · exact .atom 1
  · decide

-- Provable 은 아님 (반례 있음).
-- Bool 렌즈는 거친 렌즈 → 많은 명제가 결정 가능 (값 2개 뿐).

-- ═══ 의미 ═══
-- Logic 공리계 = Bool 렌즈 + implication 결합.
-- Peano 와 평행: 같은 / 바닥, 다른 렌즈, 다른 공리계.
-- Bool 렌즈의 kernel: {x : view x = true} vs {view x = false}.
--   2개 동치류. 가장 거친 유한 렌즈.
-- 자기참조 (p → p) 는 / 거부: logic 이 / 에 완전히 환원되진 않음.
--   고전 logic 의 "trivial tautology" 가 / 에선 generated 하지 않음.
--   이건 /의 비대칭성이 낳는 구조적 제약.
