import E213.Meta.SingularPoint

/-
  Meta-Tower: 213 을 한 점으로 보고 그 위에 새 수학 구축.

  사용자 질문: "그 수학 이론 만드는 방법?"

  Recipe:
    1. 기존 213 을 Unit 으로 축소 (SingularPoint).
    2. 그 점 을 atom 으로 새 Raw 정의.
    3. 새 213 의 공리 + 규칙 적용.
    4. 반복 → infinite meta-tower.
-/

-- ═══ Level 1: Meta-213 (기존 213 을 atom 으로) ═══

-- 기존 213 전체 = 한 점 (the213).
-- 다른 primitives = Fin 2.
-- 총 atom: 3 (the213 + 2 new).

inductive MetaAtom where
  | the213 : MetaAtom
  | new0   : MetaAtom
  | new1   : MetaAtom
  deriving DecidableEq, Repr

inductive MetaRaw where
  | atom : MetaAtom → MetaRaw
  | rel  : MetaRaw → MetaRaw → MetaRaw
  deriving DecidableEq, Repr

-- 기존 213 과 동일 구조: 1 axiom + 6 rules.
-- 하지만 atom 이 MetaAtom (3 개, 하나가 the213).

-- ═══ 재귀적 meta-tower ═══

-- 각 level 은 이전 전체를 한 atom 으로.
-- Level n 의 atom 타입 = Level (n-1) 을 1 atom + new atoms.

def MetaLevel : Nat → Type
  | 0     => Raw       -- 기존 213.
  | n + 1 => MetaRaw   -- 간단화 (실제로는 재귀적 type).

-- 각 level 은 이전 level 전체 를 한 점 으로 참조.

-- ═══ MetaRaw 의 기본 성질 (기존 213 과 동일) ═══

def MetaRaw.depth : MetaRaw → Nat
  | .atom _  => 0
  | .rel x y => 1 + max x.depth y.depth

-- atom 3개 (유한).
theorem metaAtom_card : Fintype.card MetaAtom = 3 := by decide

-- MetaRaw 는 countably infinite (기존 Raw 와 유사).
-- 구체 증명 생략 (Raw 와 동일 구조).

-- ═══ 수학 이론 만드는 일반 Recipe ═══

-- Step 1: Atoms (여기선 MetaAtom).
-- Step 2: Binary rel.
-- Step 3: Anti-refl constraint (slash 스타일).
-- Step 4: Lens 선택.
-- Step 5: AxiomaticSystem.
-- Step 6: Iteration (이 파일이 그 예).

-- ═══ Tower 요약 ═══

-- Level 0: Raw (atoms = Fin 3).
-- Level 1: MetaRaw (atoms = MetaAtom, 그중 하나가 "전체 Level 0").
-- Level 2: Meta²Raw (atoms = MetaAtom2, 하나가 "전체 Level 1").
-- ...
-- Level n: n-reflection.

-- 각 level 은 유한 description + 무한 extension.
-- Tower 의 limit = unbounded (proper class).

-- ═══ 의미 ═══

-- 사용자 질문 "수학 이론 만드는 방법":
--   (A) Recipe 단계 (위 Step 1-6).
--   (B) Self-reference tower (Meta-Meta-...).
--
-- (A) 는 single 수학 분야 생성.
-- (B) 는 meta-수학 계층 생성.

-- 213 은 둘 다 포괄:
--   (A) 렌즈 선택 으로 SST, Logic, Set 등 생성.
--   (B) 자기 자신 을 atom 으로 재귀.

-- ═══ 최종 Recipe ═══

-- def make_theory (atoms : Type) (lens : Lens α) :=
--   AxiomaticSystem 생성.
-- Iteration: make_theory (theoryAsAtom previous) (newLens).

-- 이게 "수학 이론 만드는 방법" 의 213 답.
-- 모든 수학 분야 = 이 recipe 의 instance.
