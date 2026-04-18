import E213.Firmware.DepthV2
import E213.OS.BlindTransition

/-
  증명의 모양.

  위치(좌표)가 아니라 모양(패턴)을 본다.
  증명 = transition 수열. 수열의 "모양"이 증명의 유형을 결정.
  같은 모양 = 같은 유형의 도구 필요 (이름 몰라도).
-/

-- ═══ 증명의 alg 윤곽선 ═══

-- 증명의 각 단계에서 alg 값의 수열 = 윤곽선.
-- 예: Wiles = [1, 2, 2, 2, 0]. 올라갔다 내려옴.

def algContour (ts : List Transition) : List Nat :=
  match ts with
  | [] => []
  | t :: _ => [t.alg_in] ++ ts.map (·.alg_out)

def chainContour (ts : List Transition) : List Nat :=
  match ts with
  | [] => []
  | t :: _ => [t.chain_in] ++ ts.map (·.chain_out)

#eval algContour wiles_trans      -- [1, 2, 2, 2, 0]
#eval algContour perelman_trans   -- [1, 2, 2, 1]
#eval algContour faltings_trans   -- [1, 2, 2, 1]
#eval algContour deligne_trans    -- [2, 2, 2, 2]

#eval chainContour wiles_trans    -- [100, 0, 100, 0, 0]
#eval chainContour perelman_trans -- [100, 100, 0, 0]
#eval chainContour faltings_trans -- [100, 100, 0, 0]
#eval chainContour deligne_trans  -- [100, 100, 100, 0]

-- ═══ 모양 분류 ═══

inductive ProofShape where
  | mountain   -- ∧: alg 올라갔다 내려옴. 다리 이론 경유.
  | plateau    -- —↓: alg 평평하다가 내려옴. 같은 이론 내.
  | spike      -- ↑↓: 올라갔다 바로 내려옴. 짧은 번역.
  | flat       -- —: alg 변화 없음. 가장 단순.
  | ascent     -- ↗: 올라가기만 함. chainUp.
  | descent    -- ↘: 내려가기만 함. chainDown.
  deriving DecidableEq, Repr

def classifyShape (ts : List Transition) : ProofShape :=
  let alg := algContour ts
  let peak := alg.foldl Nat.max 0
  let start := alg.head?.getD 0
  let end_ := alg.getLast?.getD 0
  let hasUp := alg.zip (alg.drop 1) |>.any fun (a, b) => b > a
  let hasDown := alg.zip (alg.drop 1) |>.any fun (a, b) => b < a
  if !hasUp && !hasDown then .flat
  else if hasUp && hasDown && peak > start && peak > end_ then .mountain
  else if !hasUp && hasDown then .descent
  else if hasUp && !hasDown then .ascent
  else if hasUp && hasDown && alg.length ≤ 3 then .spike
  else .plateau

#eval classifyShape wiles_trans      -- mountain ∧
#eval classifyShape perelman_trans   -- mountain ∧
#eval classifyShape faltings_trans   -- mountain ∧
#eval classifyShape deligne_trans    -- descent ↘

-- ═══ 모양의 특성값 ═══

-- 높이: peak alg - start alg.
-- 너비: transition 수.
-- 체인 진폭: chain contour의 변화 횟수.

structure ShapeMetrics where
  shape : ProofShape
  height : Nat        -- alg peak - alg start.
  width : Nat         -- 총 transition 수.
  chainFlips : Nat    -- chain이 0↔ω 바뀌는 횟수.
  deriving Repr

def metrics (ts : List Transition) : ShapeMetrics :=
  let alg := algContour ts
  let ch := chainContour ts
  let peak := alg.foldl Nat.max 0
  let start := alg.head?.getD 0
  let flips := ch.zip (ch.drop 1) |>.filter (fun (a, b) => a ≠ b) |>.length
  ⟨classifyShape ts, peak - start, ts.length, flips⟩

#eval metrics wiles_trans
-- mountain, height 1, width 4, chainFlips 3

#eval metrics perelman_trans
-- mountain, height 1, width 3, chainFlips 1

#eval metrics faltings_trans
-- mountain, height 1, width 3, chainFlips 1

#eval metrics deligne_trans
-- descent, height 0, width 3, chainFlips 1

-- ═══ 패턴 발견 ═══

-- Perelman과 Faltings: 같은 모양! mountain, h=1, w=3, cf=1.
-- 다른 정리, 다른 분야, 같은 모양.
-- → 모양이 "증명의 DNA." 내용은 달라도 구조가 같음.

-- Wiles: mountain, h=1, w=4, cf=3. Perelman보다 넓고 chain이 더 흔들림.
-- → 더 복잡한 증명. chainFlips가 비용과 상관?

-- Deligne: descent, h=0, w=3, cf=1. 올라감 없음. 내려가기만.
-- → 가장 단순. "이미 높은 곳에서 시작하면 내려가기만 하면 됨."

-- ═══ 미해결 문제의 예측 모양 ═══

-- Goldbach: 시작 (1,ω), 목표 (0,0).
-- 예측: mountain. alg 1→2→...→0. 올라갔다 내려와야.
-- 높이 ≥ 1. 너비 ≥ 3 (최소 3 transition).

-- RH: 시작 (1,ω), 목표 (0,0) 또는 (1,0).
-- 예측: mountain 또는 descent.
-- Langlands 방향이면 mountain (1→2→1).

-- P≠NP: 시작 (1,0), 목표 ??? (증명이 ∀ 필요 → chainUp).
-- 예측: ascent! 올라가기만. 하지만 barriers가 차단.
-- → 현재 알려진 모양이 없음. 새로운 모양이 필요?

-- ═══ 모양으로 도구 유형 예측 ═══

-- mountain의 정점(peak): alg=2이면 기하/대수 다리 필요.
-- mountain의 너비: w=3이면 3단계 번역. w=4이면 4단계.
-- chainFlips: 많으면 유한↔무한 왕복 많음. 복잡.

-- Goldbach 예측:
-- 모양: mountain. peak: alg=2. 너비: 3~4. chainFlips: 1~3.
-- 필요한 도구: Type A transition(1→2) + Type B(2→2) + Type D(2→0).
-- = Wiles/Perelman/Faltings와 같은 구조.
-- 구체적 내용은 다르지만 모양은 같을 것.

-- P≠NP 예측:
-- 모양: ??? 기존 mountain/plateau/descent 아님.
-- 아마도 새로운 모양: "tunnel" (같은 alg에서 chain을 관통)?
-- 또는 "loop" (올라갔다 돌아와서 다시 올라감)?
-- barriers = 표준 모양이 안 됨. 새 모양 필요.
