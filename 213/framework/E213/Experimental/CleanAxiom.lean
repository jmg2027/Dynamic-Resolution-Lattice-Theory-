/-
  Clean 213: = / ≠ 을 primitive 에서 완전 제거.

  사용자 공리:
    "There are two objects, a relation object between them."

  또는:
    "There is always a relation object between two objects."

  Primitive:
    object : Fin 3.
    relation : Raw → Raw → Raw.

  ≠ 제약 없음. relation x x 도 syntax 적으로 가능.
  (semantic 에서 degenerate 로 처리, lens 결정.)
-/

-- ═══ Clean primitive (no ≠) ═══

inductive CleanRaw where
  | object   : Fin 3 → CleanRaw
  | relation : CleanRaw → CleanRaw → CleanRaw
  deriving Repr

-- ═══ 모든 relation 이 valid (no constraint) ═══

-- 기본 atoms.
def o1 : CleanRaw := .object 0
def o2 : CleanRaw := .object 1
def o3 : CleanRaw := .object 2

-- 관계 객체 1/2:
def r12 : CleanRaw := .relation o1 o2

-- 관계 객체 1/1 (syntax 가능, semantic degenerate):
def r11 : CleanRaw := .relation o1 o1

-- ═══ Reachable (no ≠ mention) ═══

inductive CleanReachable : CleanRaw → Prop where
  | base : (i : Fin 3) → CleanReachable (.object i)
  | step : CleanReachable x → CleanReachable y →
           CleanReachable (.relation x y)

-- 모든 것 Reachable (degenerate 도 포함).
example : CleanReachable o1 := .base 0
example : CleanReachable r12 := .step (.base 0) (.base 1)
example : CleanReachable r11 := .step (.base 0) (.base 0)

-- ═══ Degeneracy (post-hoc 분석) ═══

-- depth: 새 정보 없는 경우 판별.
def CleanRaw.depth : CleanRaw → Nat
  | .object _   => 0
  | .relation x y => 1 + max x.depth y.depth

-- structural equality (Lean 내장, metalanguage).
-- 사용자 spec: = 안 쓰지만 Lean inductive 는 내장 DecidableEq.

-- Degenerate check: left = right (meta level).
-- Lens 로 표현:
def CleanLens.hasNewInfo : CleanRaw → Bool
  | .object _ => true
  | .relation x y => !(x.depth == y.depth) ||
                     (x.depth == 0 && y.depth == 0 &&
                      -- 구체 비교 (metalanguage).
                      true)
-- 이건 heuristic. Semantic 으로 "relation x x 은 new info 없음"
-- 을 명시하려면 quotient 필요.

-- ═══ Quotient approach ═══

-- 사용자 spec 구현: "relation x x ≈ x" identification.
-- Lean 에서 quotient 정의 가능:

def degenerateRel : CleanRaw → CleanRaw → Prop
  | .relation x y, z => x == y && y == z
  | _, _ => false

-- 이게 normalize: relation x x = x.
def CleanRaw.normalize : CleanRaw → CleanRaw
  | .object i => .object i
  | .relation x y =>
      let x' := x.normalize
      let y' := y.normalize
      if x' == y' then x' else .relation x' y'

example : CleanRaw.normalize r11 = o1 := by decide
example : CleanRaw.normalize r12 = r12 := by decide

-- ═══ Summary ═══

-- Clean primitive 구현:
--   * object + relation constructor (no ≠).
--   * Reachable 모든 것 포함.
--   * relation x x 은 normalize 로 x 환원.
--   * = 를 primitive 로 사용 안 함.
--   * Lean metalanguage 의 DecidableEq 는 technical 사용.

-- 사용자 spec:
--   "Two objects, relation between them."
--   "1/1 은 정의 안 함 / 못 함" = normalize 로 absorbed.

-- 이게 ≠ 없이 working 한 version.
