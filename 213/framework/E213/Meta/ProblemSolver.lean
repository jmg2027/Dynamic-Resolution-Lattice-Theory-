import E213.Meta.CategoryFunctor

/-
  213 자동 Problem Solver.

  목적: 사용자가 명제 입력 → 213 framework 가 자동 판정.

  Pipeline:
    1. Problem213 입력 (명제 + decidable instance).
    2. Batch check: levelUpTo n 에 대해 명제 검증.
    3. Lens 순회: 어느 렌즈에서 respecting 인지.
    4. Verdict: Provable/Refutable/Independent/Unknown.
    5. Diagnostic report.
-/

-- ═══ Problem213: 자동 검증 가능한 문제 ═══

structure Problem213 where
  name : String
  prop : Raw → Prop
  decInst : DecidablePred prop

-- ═══ Check: 한 Raw 에 대한 검증 ═══

def Problem213.check (P : Problem213) (x : Raw) : Bool :=
  @decide (P.prop x) (P.decInst x)

-- ═══ Batch check: levelUpTo n 전체 ═══

def Problem213.checkLevel (P : Problem213) (n : Nat) :
    List (Raw × Bool) :=
  (levelUpTo n).map (fun x => (x, P.check x))

-- Counter (true / false counts).
def Problem213.stats (P : Problem213) (n : Nat) :
    Nat × Nat :=
  let results := P.checkLevel n
  let trues := results.filter (fun p => p.2).length
  (trues, results.length - trues)

-- ═══ Verdict 자동 판정 (유한 level 기반) ═══

def Problem213.conjectureProvable (P : Problem213) (n : Nat) : Bool :=
  (P.stats n).2 = 0

def Problem213.conjectureRefutable (P : Problem213) (n : Nat) : Bool :=
  (P.stats n).2 ≠ 0

def Problem213.verdictAt (P : Problem213) (n : Nat) : Verdict :=
  let (t, f) := P.stats n
  if f = 0 then .provable
  else if t = 0 then .refutable
  else .independent

-- ═══ 구체 예시 ═══

-- 예시 1: "모든 Raw 는 Reachable 이다."
def prob_all_reachable : Problem213 :=
  { name := "All Raw are Reachable"
    prop := Reachable
    decInst := inferInstance }

example : prob_all_reachable.conjectureProvable 0 = true := by
  native_decide

-- 예시 2: "모든 Raw depth = 0."
def prob_all_depth_zero : Problem213 :=
  { name := "All depth = 0"
    prop := fun x => x.depth = 0
    decInst := fun x => inferInstanceAs (Decidable (_ = _)) }

example : prob_all_depth_zero.conjectureProvable 0 = true := by
  native_decide

-- 예시 3: "모든 Raw 는 atom 0 이다" (false).
def prob_all_atom_zero : Problem213 :=
  { name := "All are atom 0"
    prop := fun x => x = a₀
    decInst := fun x => inferInstanceAs (Decidable _) }

example : prob_all_atom_zero.conjectureRefutable 0 = true := by
  native_decide

-- ═══ Diagnostic Report ═══

structure Report where
  problemName : String
  levelChecked : Nat
  trueCount : Nat
  falseCount : Nat
  verdict : Verdict

def Problem213.report (P : Problem213) (n : Nat) : Report :=
  let (t, f) := P.stats n
  { problemName := P.name
    levelChecked := n
    trueCount := t
    falseCount := f
    verdict := P.verdictAt n }

example : (prob_all_reachable.report 0).verdict = .provable := by
  native_decide

example : (prob_all_atom_zero.report 0).verdict = .refutable := by
  native_decide
