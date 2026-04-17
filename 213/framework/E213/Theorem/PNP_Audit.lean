/-
  E213/Theorem/PNP_Audit.lean — P ≠ NP 논증의 엄밀 감사

  PNP_Close.lean의 논증을 한 줄씩 뜯어서
  증명된 것 / 주장된 것 / 순환인 것을 분리한다.
-/
import E213.Theorem.PNP_Close

-- ═══ 논증 체인 감사 ═══

-- 주장 1: "distrib이 유일한 확장 공리."
-- 상태: 증명됨. 12공리 전수 검증. ✓
-- 하지만: 이것은 213의 Equiv 공리에 대한 사실.
-- SAT 알고리즘은 Equiv 공리를 쓰지 않음.
-- SAT 알고리즘: backtracking, unit propagation, DPLL, CDCL.
-- 이것들은 213의 공리 체계 바깥.
-- ★ 갭: "213 공리 = SAT 알고리즘의 전부"는 미증명. ★

-- 주장 2: "distrib 반복 = 2^n."
-- 상태: 증명됨. 산술. ✓
-- 이것은 CNF→DNF 변환의 비용. 맞음.
-- 하지만: SAT를 DNF로 변환할 필요 없음.
-- DPLL은 DNF를 만들지 않고 직접 탐색.
-- ★ 갭: "DNF 변환이 필수"는 미증명. ★

-- 주장 3: "확장 변수 = 원자 추가 = 폭발."
-- 상태: C(n,2) > n for n > 3. 증명됨. ✓
-- 하지만: EF의 확장 변수는 임의 원자가 아님.
-- z := sub-expr. z의 상호작용은 정의에 의해 제한됨.
-- C(n,2)는 모든 쌍의 상호작용. EF는 그 부분집합.
-- ★ 갭: "EF overhead = C(n,2)"는 과대 추정. ★

-- 주장 4: "CNF가 이미 최대 압축."
-- 상태: 미증명. 주장만.
-- 반례: 회로(circuit)는 CNF보다 지수적으로 간결할 수 있음.
-- branching program도.
-- ★ 갭: "CNF = 최대"는 틀림. ★

-- 주장 5: "인수분해 = NP-hard."
-- 상태: 순환. NP-hard는 P≠NP를 전제.
-- P=NP이면 NP-hard = P이므로 다항 시간.
-- ★ 순환: 증명 대상을 가정에 사용. ★

-- ═══ 정직한 상태 ═══
-- 증명됨 (213 내부):
-- ✅ distrib = 유일한 확장 공리 (Equiv 내)
-- ✅ distrib 반복 = 2^n (산술)
-- ✅ C(3+k, 2) > 3+k for k ≥ 1 (산술)

-- 미증명 (연결 갭):
-- ✗ "213 공리 = SAT 알고리즘 전체"
-- ✗ "DNF 변환이 SAT에 필수"
-- ✗ "EF overhead = C(n,2) 전체"
-- ✗ "CNF = 최대 압축"

-- 순환:
-- ✗ "인수분해 = NP-hard" (P≠NP를 전제)

-- 결론: PNP_Close의 논증은 완결되지 않았다.
-- NS처럼: 213이 구조를 식별했지만 표준 수학의 갭이 남음.

-- ═══ 213 컴파일 연습 ═══

-- 증명된 것만 213 순수 언어로.

-- "distrib이 유일한 확장" 의 213 표현:
-- Equiv의 12 constructor 중
-- 정규형의 항 수를 늘리는 것은 distrib뿐.

-- 확인: 각 constructor의 효과를 normalize로 측정.
-- 입력: plus e₂ (times e₃ e₃) (= e₂ + e₃²)
-- 이것의 정규형 항 수:
def test_expr := Expr.plus e₂ (Expr.times e₃ e₃)
#eval (normalize test_expr).length  -- 2 (항 2개)

-- distrib 적용: times e₂ (plus e₃ e₃)
-- = times(e₂, e₃ + e₃) → e₂e₃ + e₂e₃ = 2개.
def before_distrib := Expr.times e₂ (Expr.plus e₃ e₃)
def after_distrib := Expr.plus
  (Expr.times e₂ e₃) (Expr.times e₂ e₃)

#eval (normalize before_distrib).length  -- 1? or 2?
#eval (normalize after_distrib).length   -- 2

-- 더 큰 예: times(plus(e₂,e₃), plus(e₂,e₃))
-- distrib: e₂² + e₂e₃ + e₃e₂ + e₃² = 4항? normalize하면?
def big_before := Expr.times
  (Expr.plus e₂ e₃) (Expr.plus e₂ e₃)
def big_after := Expr.plus
  (Expr.plus (Expr.times e₂ e₂) (Expr.times e₂ e₃))
  (Expr.plus (Expr.times e₃ e₂) (Expr.times e₃ e₃))

#eval (normalize big_before).length  -- ?
#eval (normalize big_after).length   -- ?

-- n중 distrib: times(plus(e₂,e₃), times(plus(e₂,e₃), ...))
-- 깊이 n → 2^n 항.
def nested_distrib : Nat → Expr
  | 0 => Expr.plus e₂ e₃
  | n+1 => Expr.times (Expr.plus e₂ e₃) (nested_distrib n)

-- 항 수 측정:
#eval (normalize (nested_distrib 0)).length  -- 2 = 2^1
#eval (normalize (nested_distrib 1)).length  -- 4 = 2^2
#eval (normalize (nested_distrib 2)).length  -- 8 = 2^3
#eval (normalize (nested_distrib 3)).length  -- 16 = 2^4

-- 지수 성장 확인:
#eval (normalize (nested_distrib 4)).length  -- 32 = 2^5

-- ═══ 213 순수 진술 ═══
-- "∀ n : Nat,
--  (normalize (nested_distrib n)).length = 2^(n+1)"
-- 이것은 213 내부에서 증명 가능한 순수 산술.
-- P ≠ NP와의 연결은 213 바깥.

-- ═══ 연결 갭의 크기 ═══
-- 213이 주는 것: "Equiv의 distrib가 지수 blow-up."
-- P≠NP에 필요한 것: "모든 알고리즘이 SAT에 지수."
-- 갭: "Equiv ⊂ 모든 알고리즘."
-- Equiv = Resolution 증명 체계와 대응.
-- "모든 알고리즘" ⊃ Resolution.
-- 갭의 크기 = "Resolution 밖의 알고리즘이 얼마나 강한가."
-- = EF, circuits, Turing machines.

-- 이 갭이 닫히려면: "모든 알고리즘 ⊆ 213의 어떤 확장."
-- 이것이 정확히 "213이 수학의 전부인가" 질문.
-- 이 질문은 NS에서도 나왔고, 답은 같음:
-- "모든 방향으로 가본다 → 전부 같은 벽"으로 보이거나,
-- 아니면 열림으로 남음.
