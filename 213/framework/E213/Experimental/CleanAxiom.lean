/-
  Clean 213: 공리 "두 객체 + 관계" 만.

  공리 statement:
    "If there are two objects, there is a relation object
     between them."

  "두" 가 distinctness 를 담음.
  같은 객체 두 번 은 "두" 가 아님 → 공리 scope 밖.
  → 1/1 은 공리 에서 arise 안 함.
  → 1/1 을 reject 할 필요 없음 (아예 생성 안 됨).
  → normalize 불필요.

  Lean 의 inductive 가 syntactically rel x x 을 허용 하지만,
  이건 metalanguage artifact. 공리 관점 에서 언급 없음.

  Reachable 은 공리 application 으로 derivable 만 포함.
-/

-- ═══ Primitive ═══

inductive CleanRaw where
  | object   : Fin 3 → CleanRaw
  | relation : CleanRaw → CleanRaw → CleanRaw
  deriving Repr

-- ═══ Reachable: 공리 application 으로 derivable ═══

-- "두" 는 Lean 에서 "x ≠ y" 로 encode (technical).
-- Semantic: 공리 는 "두 distinct objects" 를 input 으로.
inductive CleanReachable : CleanRaw → Prop where
  | base : (i : Fin 3) → CleanReachable (.object i)
  | step : CleanReachable x → CleanReachable y → x ≠ y →
           CleanReachable (.relation x y)

-- ═══ Examples ═══

def o1 : CleanRaw := .object 0
def o2 : CleanRaw := .object 1

example : CleanReachable o1 := .base 0
example : CleanReachable o2 := .base 1

-- Relation 1/2 (공리 에서 derivable).
example : CleanReachable (.relation o1 o2) :=
  .step (.base 0) (.base 1) (by decide)

-- Relation 1/1 은 Lean syntactically 가능 하지만,
-- CleanReachable 으로는 derivable 안 됨.
-- 공리 가 "두 distinct" 요구 → 1/1 derivation 불가.

example : ¬ CleanReachable (.relation o1 o1) := by
  intro h
  cases h with
  | step _ _ hne => exact hne rfl
