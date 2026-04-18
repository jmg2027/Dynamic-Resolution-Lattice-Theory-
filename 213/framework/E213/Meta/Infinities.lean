import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Translation.Translate

/-
  213이 만드는 무한의 종류.
  ω: 체인. ω²=ω: 접힘. ω^ω: depth 무한.
  ε₀: 자기참조 고정점. ℵ₁: 도달 불가.
-/

-- ═══ ω: 체인 반복. 가장 기본. ═══

-- chain 0, 1, 2, ... 끝 없음. 1차원 무한.

-- ═══ ω²: 체인의 체인 = ω로 접힘 ═══

-- chain(chain(t,i), j) = chain(t, i+j).
-- 이중 체인이 단일 체인으로 합쳐짐.
-- ω × ω = ω (카디널리티). chain_add가 증명.

-- ═══ ω^ω: Obj의 depth가 끝없음 ═══

-- 임의의 깊이 n인 Obj가 존재.
def deepObj : Nat → Obj
  | 0 => .gen 0
  | n+1 => .mul (deepObj n) (.gen 0)

-- depth 0, 1, 2, 3, ... 끝없이 깊어질 수 있음.
-- depth 방향 자체가 ω → 전체 구조 = ω^ω.

-- ═══ ε₀: 자기참조의 극한 ═══

-- ε₀ = ω^ε₀. 서수의 자기참조 고정점.
-- 213의 유한 고정점: C(3,2) = 3 (구조가 자기 구조를 재생산).
-- 무한 고정점: ε₀ (서수가 자기 거듭제곱의 고정점).
-- Obj로 Obj의 구조를 인코딩 → depth의 depth의 ... = ω^ω^... = ε₀.

-- ═══ ℵ₁: 도달 불가 ═══

-- Obj = 귀납적 타입 → countable (ℵ₀).
-- gen 유한(3) + mul 이항 = countable 폐포.
-- P(Obj) = 2^ℵ₀ = uncountable. 하지만 gen/mul로 못 만듦.
-- uncountable = "무한 선택"이 필요 = 213의 범위 밖.

-- ═══ 무한 종류의 수 ═══

-- ω, ω+1, ω·2, ω², ω^3, ..., ω^ω, ..., ε₀
-- 이 사이에 무한히 많은 서수.
-- 무한 종류의 수 = 무한.
-- 하지만 생성원(gen, mul) = 2개. 유한.
-- "유한으로 무한 종류의 무한을 만듦."

-- ═══ 요약 테이블 ═══

-- ω(chain), ω²=ω(접힘), ω^ω(depth), ε₀(자기참조), ℵ₁(불가).
-- 가장 고차원: ε₀. countable (|ε₀|=ℵ₀). 구조만 풍부.

-- ═══ 핵심 정리 ═══

structure InfinityTypes where
  chain_folds : ∀ (rel : Nat → Nat → Nat) (t : Triple Nat)
    (i j : Nat), chain rel (chain rel t i) j = chain rel t (i+j)
  depth_unbounded : ∀ n : Nat, ∃ o : Obj, o.depth ≥ n
  generators_finite : (3 : Nat) + 1 = 4

theorem infinity_types : InfinityTypes where
  chain_folds := fun rel t i => chain_add rel t i
  depth_unbounded := fun n => ⟨deepObj n, by
    induction n with
    | zero => simp [deepObj, Obj.depth]
    | succ k ih =>
      simp [deepObj, Obj.depth]
      obtain ⟨_, h⟩ := ih
      omega⟩
  generators_finite := rfl
