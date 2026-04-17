/-
  E213/Compiler.lean — 수학 공식 → 213 문자열 컴파일러

  논리식을 입력하면 213 문자열을 출력.
-/
import Init

-- ═══ 논리식 타입 ═══
inductive Formula where
  | var : String → Formula          -- 변수 x, y, z
  | const : String → Formula        -- 상수 ∅, 0, 1
  | mem : Formula → Formula → Formula      -- ∈
  | eq : Formula → Formula → Formula       -- =
  | neg : Formula → Formula                -- ¬
  | conj : Formula → Formula → Formula     -- ∧
  | disj : Formula → Formula → Formula     -- ∨
  | impl : Formula → Formula → Formula     -- →
  | iff : Formula → Formula → Formula      -- ↔
  | forall_ : String → Formula → Formula   -- ∀x.φ
  | exists_ : String → Formula → Formula   -- ∃x.φ
  | app : String → Formula → Formula       -- f(x)
  deriving Repr

open Formula

-- ═══ 컴파일러: Formula → 213 문자열 ═══
def compile : Formula → String
  | var _ => "2"                    -- 변수 = 미결정 구분
  | const _ => "1"                  -- 상수 = 경계
  | mem a b =>
    compile a ++ "1" ++ compile b   -- ∈ = 경계로 연결된 두 것
  | eq a b =>
    compile a ++ "231" ++ compile b -- = = 구분→재귀→경계
  | neg a =>
    "21" ++ compile a               -- ¬ = 구분 후 뒤집기
  | conj a b =>
    compile a ++ "22" ++ compile b  -- ∧ = 구분의 구분
  | disj a b =>
    compile a ++ "212" ++ compile b -- ∨ = 구분+경계+구분
  | impl a b =>
    compile a ++ "21" ++ compile b  -- → = 구분 후 방향
  | iff a b =>
    compile a ++ "2121" ++ compile b -- ↔ = →∧← = 양방향
  | forall_ _ body =>
    "2" ++ "1" ++ compile body      -- ∀ = 구분 + 경계 + 본문
  | exists_ _ body =>
    "3" ++ "1" ++ compile body      -- ∃ = 창발 + 경계 + 본문
  | app _ x =>
    "22" ++ compile x               -- f(x) = 적용 = 구분²

-- ═══ ZFC 공리 ═══

-- 1. 외연: ∀x∀y[∀z(z∈x ↔ z∈y) → x=y]
def zfc_ext : Formula :=
  forall_ "x" (forall_ "y"
    (impl
      (forall_ "z" (iff (mem (var "z") (var "x"))
                        (mem (var "z") (var "y"))))
      (eq (var "x") (var "y"))))

-- 2. 공집합: ∃x∀y ¬(y∈x)
def zfc_empty : Formula :=
  exists_ "x" (forall_ "y" (neg (mem (var "y") (var "x"))))

-- 3. 쌍: ∀x∀y∃z∀w(w∈z ↔ w=x ∨ w=y)
def zfc_pair : Formula :=
  forall_ "x" (forall_ "y" (exists_ "z" (forall_ "w"
    (iff (mem (var "w") (var "z"))
         (disj (eq (var "w") (var "x"))
               (eq (var "w") (var "y")))))))

-- 4. 합집합: ∀x∃y∀z(z∈y ↔ ∃w(z∈w ∧ w∈x))
def zfc_union : Formula :=
  forall_ "x" (exists_ "y" (forall_ "z"
    (iff (mem (var "z") (var "y"))
         (exists_ "w" (conj (mem (var "z") (var "w"))
                             (mem (var "w") (var "x")))))))

-- 5. 멱집합: ∀x∃y∀z(z∈y ↔ ∀w(w∈z → w∈x))
def zfc_power : Formula :=
  forall_ "x" (exists_ "y" (forall_ "z"
    (iff (mem (var "z") (var "y"))
         (forall_ "w" (impl (mem (var "w") (var "z"))
                            (mem (var "w") (var "x")))))))

-- 6. 무한: ∃x(∅∈x ∧ ∀y(y∈x → S(y)∈x))
def zfc_inf : Formula :=
  exists_ "x" (conj
    (mem (const "∅") (var "x"))
    (forall_ "y" (impl
      (mem (var "y") (var "x"))
      (mem (app "S" (var "y")) (var "x")))))

-- 7. 분리: ∀x∃y∀z(z∈y ↔ z∈x ∧ φ(z))
def zfc_sep : Formula :=
  forall_ "x" (exists_ "y" (forall_ "z"
    (iff (mem (var "z") (var "y"))
         (conj (mem (var "z") (var "x"))
               (app "φ" (var "z"))))))

-- 8. 정칙: ∀x(x≠∅ → ∃y(y∈x ∧ ¬∃z(z∈y ∧ z∈x)))
def zfc_found : Formula :=
  forall_ "x" (impl
    (neg (eq (var "x") (const "∅")))
    (exists_ "y" (conj
      (mem (var "y") (var "x"))
      (neg (exists_ "z" (conj
        (mem (var "z") (var "y"))
        (mem (var "z") (var "x"))))))))

-- ═══ 컴파일 실행 ═══
#eval compile zfc_ext
#eval compile zfc_empty
#eval compile zfc_pair
#eval compile zfc_union
#eval compile zfc_power
#eval compile zfc_inf
#eval compile zfc_sep
#eval compile zfc_found

-- 길이
#eval (compile zfc_ext).length
#eval (compile zfc_empty).length
#eval (compile zfc_pair).length
#eval (compile zfc_union).length
#eval (compile zfc_power).length
#eval (compile zfc_inf).length
#eval (compile zfc_sep).length
#eval (compile zfc_found).length

-- 총 ZFC 비용
#eval [(compile zfc_ext).length,
       (compile zfc_empty).length,
       (compile zfc_pair).length,
       (compile zfc_union).length,
       (compile zfc_power).length,
       (compile zfc_inf).length,
       (compile zfc_sep).length,
       (compile zfc_found).length]

-- 합계
#eval [(compile zfc_ext).length,
       (compile zfc_empty).length,
       (compile zfc_pair).length,
       (compile zfc_union).length,
       (compile zfc_power).length,
       (compile zfc_inf).length,
       (compile zfc_sep).length,
       (compile zfc_found).length].foldl (·+·) 0
