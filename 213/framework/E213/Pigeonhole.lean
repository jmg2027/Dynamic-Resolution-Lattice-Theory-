import E213.Axiom
import E213.Translate

/-
  비둘기집 원리의 213 번역 + 증명.

  원본: "Fin 3 → Fin 2 단사 없음." (3개를 2칸에 넣으면 겹침.)
  213: "3개의 × 결과가 전부 false(다름)일 수 없음."
  핵심: C(2,2)=1 < 3=C(3,2). 구분력 부족.
-/

-- ═══ f: Fin 3 → Fin 2를 코드(0~7)로 인코딩 ═══

def decode (code : Nat) (i : Fin 3) : Fin 2 :=
  ⟨(code / (2 ^ i.val)) % 2, by omega⟩

-- ═══ 원본 정리: 단사 f 없음 ═══

def isInj (code : Nat) : Bool :=
  decide (decode code 0 ≠ decode code 1) &&
  decide (decode code 0 ≠ decode code 2) &&
  decide (decode code 1 ≠ decode code 2)

-- 8개 함수 전수검사. 단사 = 0개.
theorem no_injection :
    (List.range 8).filter isInj = [] := by native_decide

-- ═══ 213 번역: 비교 triple ═══

-- 각 f의 "쌍별 비교": f(a)==f(b)인가?
def pigeon (code : Nat) : Triple Bool :=
  cmpTriple (fun a b : Fin 3 => decode code a == decode code b)
    ⟨0, 1, 2⟩

def allFalse (t : Triple Bool) : Bool := !t.x && !t.y && !t.z

-- (F,F,F) = "모두 다른 칸" = 단사.
-- 어떤 코드도 (F,F,F) 불가.
theorem no_all_false :
    (List.range 8).filter (fun c => allFalse (pigeon c)) = [] := by
  native_decide

-- ═══ 213 증명: 구분력 부족 ═══

-- 2칸의 구분력 = C(2,2) = 1 (쌍이 하나뿐).
-- 3개 구분 요구 = C(3,2) = 3 (쌍이 셋).
-- 1 < 3. 구분력이 요구보다 적음.
theorem gap : pairs 2 < 3 := by native_decide

-- ═══ 증명 단계별 대응 ═══
-- 원본                   213
-- "f: A→B 단사 가정"   → "모든 × false 가정"
-- "|A|=3, |B|=2"       → "gen 3개, 칸 2개"
-- "3 > 2"              → "C(3,2)=3 > C(2,2)=1" (gap)
-- "∴ 겹침"             → "어떤 ×가 true" (no_all_false)

-- 각 단계가 213 연산에 대응:
-- "가정" = 비교 triple 전체가 false인 Obj 구성
-- "크기 비교" = pairs 함수 비교 (방향 2의 세기)
-- "모순" = allFalse인 Obj가 없음 (전수검사)
-- "결론" = 어떤 mul(gen i, gen j)의 판정이 true

-- ═══ 요약 ═══

structure Pigeonhole213 where
  standard : (List.range 8).filter isInj = []
  in213 : (List.range 8).filter (fun c => allFalse (pigeon c)) = []
  why : pairs 2 < 3

theorem pigeonhole : Pigeonhole213 where
  standard := by native_decide
  in213 := by native_decide
  why := by native_decide
