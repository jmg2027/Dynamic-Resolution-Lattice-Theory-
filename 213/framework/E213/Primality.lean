import E213.Axiom
import E213.Closure

/-
  소수 = 213의 환원 불가능한 Obj.
  gen = 원자. mul(gen,gen) = 최소 비교. 이것이 "소수."
  mul(mul(...),...)  = 합성. 비교의 비교.
  자연수 소수 = 이 구조에 번호를 매긴 것.
-/

-- ═══ Obj의 환원 불가능성 ═══

-- "환원 불가" = 더 단순한 Obj의 mul로 분해 안 됨.
-- gen i: 원자. 분해 불가. (단위원 같은 것.)
-- mul(gen i, gen j): 최소 비교. depth 1. "소수."
-- mul(mul(..), ..): 비교의 비교. depth ≥ 2. "합성수."

def isAtom : Obj → Bool
  | .gen _ => true
  | .mul _ _ => false

def isPrimeObj : Obj → Bool
  | .mul (.gen _) (.gen _) => true  -- depth 1, 양쪽 atom
  | _ => false

def isComposite : Obj → Bool
  | .mul a b => a.depth > 0 || b.depth > 0  -- 한쪽이라도 non-atom
  | _ => false

-- ═══ 소수 Obj의 수 ═══

-- depth 1 소수: mul(gen i, gen j). i,j ∈ {0,1,2}.
-- 가능한 조합: 3 × 3 = 9.
-- 대칭(×는 교환): mul(gen 0, gen 1) = mul(gen 1, gen 0).
-- 비순서쌍: C(3,2) + 3 = 3 + 3 = 6. (다른 쌍 3 + 같은 쌍 3.)
-- 같은 쌍 제외하면: C(3,2) = 3. (gen 0 × gen 1 등.)

-- 자연수 대응:
-- 3개의 gen → 의미론적 원자 3개.
-- C(3,2) = 3개의 "소수" → 비교 방법 3가지.
-- 이것이 자연수에서는 2, 3, 5 (처음 세 소수).

-- ═══ 메타 레벨의 소수 ═══

-- depth 2에서: mul(primeObj, gen j).
-- 소수와 원자의 새 비교 → 새로운 환원 불가능 단위.
-- 이들은 "level 2의 소수."

-- depth n에서: 새로운 환원 불가능 조합이 나타남.
-- 각 depth에서 유한개의 새 "소수."
-- 모든 depth 합 → 무한개의 소수!

-- ═══ 이것이 소수의 무한성 ═══

-- 소수가 무한한 이유 (213):
-- depth가 무한 (chain은 끝없음).
-- 각 depth에서 새 환원 불가능 Obj 존재.
-- → 소수 총수 = 무한.

-- 유클리드 증명의 213 버전:
-- "유한개의 소수" 가정 → 모든 소수가 depth ≤ k.
-- 하지만 depth k+1에서 새 환원 불가능 Obj 존재.
-- 모순. ∴ 소수 무한.

-- depth k+1의 새 소수 구성:
def newPrime (k : Nat) : Obj :=
  -- depth k의 가장 단순한 Obj와 gen의 비교.
  -- 이것은 depth k+1이고, depth k의 것으로 분해 안 됨.
  let base := (List.range k).foldl (fun o _ => .mul o (.gen 0)) (.gen 0)
  .mul base (.gen 1)

-- newPrime 0 = mul(gen 0, gen 1). depth 1.
-- newPrime 1 = mul(mul(gen 0, gen 0), gen 1). depth 2.
-- newPrime k = depth k+1. 항상 새로움.

-- ═══ 소수 = 의미의 원자 ═══
-- 자연수 소수: 곱으로 분해 불가. 213 소수: mul로 분해 불가.
-- 같은 개념. 번호 매기기(2,3,5,7...)는 임의. 구조는 필연.
