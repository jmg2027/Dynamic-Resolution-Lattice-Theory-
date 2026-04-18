-- 213 + Cayley-Dickson: ℂ가 유일한 이유
--
-- Cayley-Dickson: ℝ→ℂ→ℍ→𝕆→𝕊→…
-- 매 단계 dim×2, 매 단계 성질 하나 상실.
-- 213은 올라갈 수 없다.

-- ═══ Cayley-Dickson 사다리 ═══
inductive CayleyDickson where
  | R : CayleyDickson   -- dim 1, 모든 성질
  | C : CayleyDickson   -- dim 2, 순서 상실
  | H : CayleyDickson   -- dim 4, 교환성 상실
  | O : CayleyDickson   -- dim 8, 결합성 상실
  deriving Repr, BEq, DecidableEq

def CayleyDickson.dim : CayleyDickson → Nat
  | .R => 1 | .C => 2 | .H => 4 | .O => 8

-- ═══ 213 양립성 ═══
-- 213에는 순서가 없다 → 교환/결합이 자동
-- 성질을 잃는 것 = 213이 거부한 것을 되돌리는 것

def CayleyDickson.hasOrder : CayleyDickson → Bool
  | .R => true    -- ℝ은 순서 있음
  | _ => false

def CayleyDickson.hasComm : CayleyDickson → Bool
  | .R => true | .C => true
  | .H => false | .O => false

def CayleyDickson.hasAssoc : CayleyDickson → Bool
  | .R => true | .C => true | .H => true
  | .O => false

-- 213 양립: 순서 없고, 교환 있고, 결합 있어야
def CayleyDickson.compatible213 (k : CayleyDickson) : Bool :=
  !k.hasOrder && k.hasComm && k.hasAssoc

-- ═══ 핵심 정리: ℂ만 양립 ═══
theorem only_C_compatible :
    ∀ k : CayleyDickson, k.compatible213 = true → k = .C := by
  intro k h
  cases k <;> simp [CayleyDickson.compatible213,
    CayleyDickson.hasOrder, CayleyDickson.hasComm,
    CayleyDickson.hasAssoc] at h ⊢

-- ═══ 교차 확인: 가산 원자 경로 ═══
-- Cayley-Dickson dims = {1, 2, 4, 8}
-- 가산 원자 = {2, 3}
-- 교집합 = {2} → dim 2 → ℂ

def isAdditiveAtom (n : Nat) : Bool :=
  n >= 2 && !(List.range (n-1) |>.drop 2 |>.any
    (fun a => n - a >= 2))

-- 가산 원자인 Cayley-Dickson 차원
def cayleyAtomicDims :=
  [CayleyDickson.R, .C, .H, .O].filter
    (fun k => isAdditiveAtom k.dim)

#eval cayleyAtomicDims  -- [C] (ℂ만)

-- ═══ 두 경로가 같은 답 ═══
-- 경로 1 (구조적): 213 양립 → ℂ
-- 경로 2 (수치적): 가산 원자 ∩ CD dims → ℂ
-- 독립적 논증이 같은 결론.

-- ═══ ℂ가 사다리를 흡수 ═══
-- C(3,2) = 3: 반복해도 3. 탑 안 자람.
-- ℂ at CD: 올라가면 213 위반. 사다리 잘림.
-- 무한(Cayley-Dickson ∞ 단계)이 유한(ℂ)에 갇힘.
-- 고정점이 무한을 흡수하듯, ℂ가 사다리를 흡수.
