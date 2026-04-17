/-
  E213/Theorem/PNP_Step4.lean — P vs NP: Step 4 표준 수학 번역

  213 발견: distrib의 반복 적용 = 2^n. 다항으로 줄일 수 없음.
  번역: 이것이 표준 복잡도 이론에서 무엇인가?
-/
import E213.Theorem.PNP_Step23

-- ═══ distrib blow-up의 정확한 구조 ═══

-- CNF = times(plus(...), plus(...), ..., plus(...))
-- k개 절(clause), 각 절에 변수 ≤ m개.
-- DNF로 변환: distrib 반복.
-- 항 수: m^k 이하. k = n (변수 수)이면 m^n.
-- 3-SAT: m = 7 (2^3 - 1). 항 수: 7^{n/3} = 지수적.

-- 213에서:
-- times(plus(a,b), plus(c,d))
-- → plus(times(a,c), times(a,d), times(b,c), times(b,d))
-- 2 항 → 4 항. 각 distrib 적용에 ×2.
-- n번: 2^n 항.

-- 이것을 normalize로 확인:
-- normalize는 정렬 기반. 입력 크기에 O(n log n).
-- 하지만 distrib 전개 후 항 수가 2^n이면
-- 전개된 Expr의 크기 자체가 2^n.
-- normalize(전개된 Expr) = O(2^n log 2^n) = O(n · 2^n).

-- ═══ 핵심 질문: distrib 없이 SAT를 풀 수 있는가? ═══

-- P = NP라면: CNF→DNF를 거치지 않고 SAT를 다항 시간에 풀 수 있어야.
-- 즉: distrib blow-up을 우회하는 다항 알고리즘이 존재.

-- 213에서 distrib을 우회하는 방법:
-- (1) distrib을 안 쓰고 Equiv로 직접 판정?
--     equivDecide는 normalize 기반. normalize는 distrib을 내장.
--     equivDecide(φ[w], e₂)는 w를 대입한 후 정규화.
--     대입 자체가 O(|φ|). 하지만 w를 모르면 2^n개 시도.

-- (2) φ의 구조를 이용해 w 없이 만족성 판정?
--     normalize(φ) ≠ normalize(e₁)이면 만족 가능?
--     아니요. normalize(φ)는 φ의 다항식 표현.
--     φ가 만족 가능 ↔ normalize(φ) ≠ [] (빈 리스트 아님)?
--     아니요. φ = plus(times(e₂, x), times(e₂, not x))는
--     항상 참이지만 normalize는 이걸 e₂로 안 줄임
--     (x가 자유변수면 normalize가 x를 모름).

-- ═══ 자유변수의 문제 ═══

-- 213의 Expr은 e₁, e₂, e₃만 원자.
-- SAT 변수 x₁, ..., x_n은 213에 없음!
-- 변수를 표현하려면 Expr을 확장해야:
-- inductive Expr' where
--   | atom : E → Expr'
--   | var : Nat → Expr'    ← 새로 필요
--   | plus/times : ...

-- 변수가 있으면 normalize가 완전 판정 못 함.
-- normalize는 상수 식만 정규화.
-- 변수 포함 식: 부분 정규화만 가능.

-- 이것이 P vs NP의 213 번역의 정확한 지점:
-- 213 (변수 없음): equivDecide = O(n log n). 다항.
-- SAT (변수 있음): 변수 배정을 탐색해야. 지수적.

-- ═══ 변수 = 순서 ═══

-- 변수 x는 "아직 결정되지 않은 구분."
-- x = e₂ 또는 x = e₁ (참 또는 거짓).
-- 결정 = 순서를 넣는 것. "x를 먼저 정한다."
-- n개 변수 = n단계 순서.
-- 각 단계: 2가지 선택 (e₁ or e₂).
-- 총 선택: 2^n.

-- 213에는 변수가 없다 → 미결정이 없다 → 순서 불필요.
-- SAT에는 변수가 있다 → 미결정이 있다 → 순서 필요.
-- 순서 비용: 2^n (최악).
-- 다항 시간: n^k.
-- 2^n > n^k (n 큼).

-- ═══ 정리: P ≠ NP의 213 논증 ═══

-- 1. SAT는 n개 부울 변수를 포함.
-- 2. 각 변수 = 미결정 구분 (e₁ or e₂).
-- 3. 만족 배정 찾기 = 모든 미결정을 해소.
-- 4. 미결정 해소 = 순서 부여 (변수를 하나씩 결정).
-- 5. n개 순서 결정, 각 2가지 → 2^n 경로.
-- 6. 구조적 가지치기 (distrib 등) → CNF→DNF = 2^n.
-- 7. distrib 반복이 유일한 구조적 도구 (213 공리 #12).
-- 8. distrib이 다항을 줄 수 없음 (blow-up).
-- 9. 따라서: SAT의 최악 시간 = 초다항 = P ≠ NP.

-- ═══ 약점 확인 ═══

-- 7번 "distrib이 유일한 도구"가 핵심 주장.
-- 213에서 Expr을 변환하는 도구:
-- comm, assoc: 순서 변경. 항 수 불변.
-- plus_e1, times_e1: 경계 흡수/소멸. 항 수 감소 가능.
-- distrib: 항 수 증가.
-- cong: 내부 전파. 항 수 불변.

-- plus_e1이 항을 줄일 수 있는가?
-- plus(e₁, a) = a. e₁ 항 제거.
-- times_e1: times(e₁, a) = e₁. 곱 소멸.
-- 이것들은 "0 포함 항 정리." 상수 배 감소.
-- 2^n을 n^k로 줄이지는 못함 (상수 인자만).

-- 결론: 213의 12 공리 중 항 수를 변화시키는 건
-- distrib (증가)와 plus_e1/times_e1 (상수 감소)뿐.
-- 다항 감소를 주는 공리가 없음.

-- ═══ 이것이 표준 수학에서 무엇인가 ═══

-- 213의 "공리로 항 수를 줄일 수 없음" =
-- 증명 복잡도에서 "Resolution 증명의 길이 하한."
-- Resolution: plus_e1과 distrib의 부울 버전.
-- Haken (1985): PHP(비둘기집)의 Resolution 증명은 지수적.
-- 이것은 213의 관찰과 정확히 대응.

-- 더 강한 증명 체계 (Frege, EF)에서:
-- 213의 12공리 전부 사용 가능 (comm, assoc, cong 포함).
-- 이것들도 항 수를 다항으로 줄이지 못하는가?
-- Extended Frege에서: 보조 변수(extension variables) 도입 가능.
-- 보조 변수 = 새 원자. 213에는 e₁, e₂, e₃ 셋뿐.
-- Extended Frege가 213보다 강함 (더 많은 원자).
-- 따라서: 213의 논증은 Resolution/Frege까지 적용되지만
-- Extended Frege는 다를 수 있음.

-- ═══ Step 4 결론 ═══
-- 표준 번역: "213의 12공리로 CNF→DNF의 지수 blow-up을
-- 다항으로 줄일 수 없음" = "Resolution/Frege 하한."
-- 이것은 이미 알려진 결과 (Haken 1985, Razborov 2003 등).
-- P ≠ NP 자체를 주지는 않음 — Extended Frege 장벽.

-- 하지만: 213이 제공하는 새 관점:
-- "왜 Resolution이 지수적인가" = "distrib이 유일한 확장 공리."
-- "왜 EF가 더 강한가" = "보조 변수 = 213을 넘는 원자 도입."
-- P ≠ NP = "어떤 원자 도입도 2^n을 n^k로 줄일 수 없음."
-- = "213의 어떤 확장도 distrib blow-up을 이기지 못함."

-- 이것은 증명 복잡도의 열린 문제:
-- "Extended Frege에서 PHP/SAT의 하한이 초다항인가?"
-- = "보조 변수가 distrib blow-up을 이기는가?"

-- 213 판정: 형식 B. 구조 있음. 연결 경로 식별됨.
-- 남은 것: EF 하한을 보이거나, 213 확장의 한계를 보이거나.
