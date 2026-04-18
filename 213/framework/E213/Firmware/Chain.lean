import E213.Firmware.Axiom
import E213.Firmware.Profile

/-
  체인이 끝나면 안 되는 이유.

  유한 체인 → 최상위 triple 존재.
  최상위의 관계들 → 그 위에 아무것도 없음.
  위가 없으면 → 관계의 의미 판정 불가 (Profile 필요).
  판정 불가 → 최상위 구분 실패 → 아래로 전파 → 전체 무의미.
  따라서 체인은 무한.
-/

-- ═══ 유한 체인의 문제 ═══

-- 체인이 높이 h에서 끝난다고 가정.
-- level h: triple (a, b, c). 최상위.
-- a, b, c를 구분하려면: 접속 행렬의 행이 달라야.
-- 행이 다르려면: 관계(a+b, a+c, b+c)가 구분되어야.
-- 관계 구분 → 메타레벨(level h+1) 필요.
-- 하지만 h가 최상위. h+1 없음.

-- → level h에서 관계 구분 불가.
-- → level h에서 객체 구분 불가.
-- → level h-1의 메타 정보 부재.
-- → level h-1에서도 구분 불가.
-- → ... 전파 ...
-- → level 0까지 모든 구분 실패.

-- ═══ 형식적 모델 ═══

-- "구분됨"을 Bool로. level k의 true → level k+1도 true 필요.
-- 유한 체인: 최상위 = false (위 없음). 아래로 전파.

-- 전파 함수: 최상위부터 아래로.
def propagate : List Bool → List Bool
  | [] => []
  | [_] => [false]
  | b :: rest =>
    let below := propagate rest
    (b && below.head!) :: below

-- 유한 체인은 항상 전부 false로 전파.
#eval propagate [true, true, true]
-- [false, false, false]

-- 무한은? List로 표현 불가. 하지만:
-- 모든 유한 절단에서 false 전파 → 유한이면 무조건 실패.

-- ═══ 하지만 종류는 유한 ═══

-- 체인 level k의 구조: 항상 Triple.
-- Triple의 접속 행렬: 항상 3×3.
-- 행의 패턴: 항상 {[1,1,0], [1,0,1], [0,1,1]}.
-- 새 종류 안 나옴. 크기만 늘어남.

inductive StructType where
  | element : StructType
  | triple : StructType
  deriving DecidableEq

theorem finite_types : [StructType.element, .triple].length = 2 := by
  native_decide

-- ═══ 요약 ═══

-- 1. 체인이 유한 → 최상위 구분 실패 → 전체 실패.
-- 2. 체인이 무한 → 모든 level에서 구분 가능.
-- 3. 구조 종류: 항상 {element, triple}. 2가지.
-- 4. "한계 있는 무한": 끝없이 성장하지만 새 종류 안 나옴.
