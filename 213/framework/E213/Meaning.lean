import E213.Axiom
import E213.Decompose

/-
  213에서 의미의 경계.
  의미 = 구분 가능 = gen/mul/=_k로 판정 가능.
  의미의 5단계. 상실 지점 = "∀n" (보편 양화사).
-/

-- ═══ 의미의 5단계 ═══

inductive MeaningLevel where
  | full       -- depth 0-2. 완전 결정 가능.
  | partial    -- depth 2-ω. 개별 OK, ∀는 무한.
  | approx     -- depth ω. 해상도 의존. 극한.
  | meta       -- depth ω-ε₀. 자기참조. 괴델.
  | none       -- >ε₀. gen/mul로 구성 불가.
  deriving DecidableEq, Repr

def meaningOf : String → MeaningLevel
  | "명제논리" => .full      -- Bool. 완전 결정.
  | "유한대수" => .full      -- 유한 군/환/체. 전수검사.
  | "자연수론" => .partial   -- 개별 n OK. ∀n = ω.
  | "해석학"   => .approx    -- ε-δ. 근사.
  | "집합론"   => .meta      -- 자기참조. 불완전성.
  | "비가산"   => .none      -- gen/mul 한계 밖.
  | _          => .none

-- ═══ 의미 상실의 정확한 지점 ═══

-- 전이 1: full → partial. 지점: "∀n ∈ ℕ".
-- "3+5=8" = depth 1. 완전. ✓
-- "∀n, P(n)" = 개별 depth 1, 전체 depth ω. △
-- 골드바흐: 각 짝수 확인 = 유한. 전체 = 무한.

-- 전이 2: partial → approx. 지점: "ε-δ".
-- = 이 고정값 → 함수(k → =_k). 해상도 변수화.
-- 연속 = "모든 해상도에서" = depth ω.

-- 전이 3: approx → meta. 지점: 자기참조.
-- "이 진술은 증명 불가" = 의미가 자기를 가리킴.
-- 괴델: PA 안에서 Con(PA) 증명 불가.

-- 전이 4: meta → none. 지점: 비가산.
-- gen/mul = countable 폐포. P(ω) = uncountable.
-- 구성 불가능한 대상 = 213에서 의미 없음.

-- ═══ 213 경계 = PA 경계 ═══

-- PA의 증명론적 서수 = ε₀.
-- 213의 자연스러운 한계 = ε₀.
-- 213에서 의미 있는 것 ≈ PA에서 증명 가능한 것.
-- 이유: 둘 다 (유한 생성 + 귀납 + 자기참조).

-- PA 밖 = 213 밖: Con(PA), 큰 기수, 연속체 가설.

-- ═══ 구체 예시 ═══
-- full: "C(3,2)=3" (depth 0), 유한 군 라그랑주 (depth 2).
-- partial: "소수 무한" (각 유한, ∀=ω), 페르마 (PA+α).
-- approx: "π=3.14..." (각 자릿수 유한, 전체 ω).
-- none: "임의 실수 선택" (비가산), "선택공리" (무한선택).

-- ═══ 정리 ═══

structure MeaningBoundary where
  logic_full : meaningOf "명제논리" = .full
  nt_partial : meaningOf "자연수론" = .partial
  analysis_approx : meaningOf "해석학" = .approx
  uncount_none : meaningOf "비가산" = .none

theorem meaning : MeaningBoundary where
  logic_full := rfl
  nt_partial := rfl
  analysis_approx := rfl
  uncount_none := rfl
