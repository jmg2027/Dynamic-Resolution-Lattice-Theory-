import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Translation.Translate
import E213.Hypervisor.PA
import E213.OS.Goldbach.Statement

/-
  스택 트레이스 프레임워크.

  213 아키텍처의 모든 레이어를 관통하는 호출을 추적.
  각 레이어에서 뭘 했는지, 어떤 API를 썼는지, 결과가 뭔지 기록.
  실제 CPU의 스택 트레이스처럼 "여기서 뭐 했는데 결과가 이거" 형태.
-/

-- ═══ 트레이스 프레임 ═══

inductive Layer where
  | hw | fw | trans | hv | os | app
  deriving DecidableEq, Repr

structure Frame where
  layer : Layer
  operation : String
  input : String
  output : String
  deriving Repr

abbrev Trace := List Frame

-- 트레이스에 프레임 추가
def Trace.push (t : Trace) (layer : Layer) (op input output : String) : Trace :=
  t ++ [⟨layer, op, input, output⟩]

-- 트레이스 출력
def Trace.dump (t : Trace) : String :=
  let lines := t.enum.map fun (i, f) =>
    s!"[{i}] {repr f.layer} | {f.operation} | {f.input} → {f.output}"
  "\n".intercalate lines

-- ═══ 트레이스를 뽑으면서 실행하는 래퍼 ═══

-- Firmware: relify를 트레이스하면서 실행.
def tracedRelify (rel : Nat → Nat → Nat) (t : Triple Nat)
    (trace : Trace) : Triple Nat × Trace :=
  let result := relify rel t
  let frame : Frame := {
    layer := .fw
    operation := "relify"
    input := s!"({t.x}, {t.y}, {t.z})"
    output := s!"({result.x}, {result.y}, {result.z})"
  }
  (result, trace ++ [frame])

-- Firmware: chain을 트레이스하면서 실행.
def tracedChain (rel : Nat → Nat → Nat) (t : Triple Nat) (k : Nat)
    (trace : Trace) : Triple Nat × Trace := Id.run do
  let mut tr := trace
  let mut current := t
  tr := tr.push .fw "chain[0]" s!"({t.x}, {t.y}, {t.z})" "start"
  for i in List.range k do
    let next := relify rel current
    tr := tr.push .fw s!"chain[{i+1}]"
      s!"relify({current.x}, {current.y}, {current.z})"
      s!"({next.x}, {next.y}, {next.z})"
    current := next
  return (current, tr)

-- Translation: chain → ℕ 변환을 트레이스.
def tracedChainToNat (k : Nat) (trace : Trace) : Nat × Trace :=
  (k, trace.push .trans "chain→ℕ" s!"chain level {k}" s!"{k}")

-- Hypervisor: PA 연산을 트레이스.
def tracedPAAdd (m n : Nat) (trace : Trace) : Nat × Trace :=
  (m + n, trace.push .hv "PA.add" s!"{m} + {n}" s!"{m + n}")

-- OS: goldbach 검사를 트레이스.
def tracedGoldbach (n : Nat) (trace : Trace) : Bool × Trace :=
  let result := goldbach n
  let pair := goldbachPair n
  let pairStr := match pair with
    | some (p, q) => s!"({p}, {q})"
    | none => "none"
  (result, trace.push .os "goldbach"
    s!"n={n}" s!"{result}, pair={pairStr}")

-- ═══ 실행 1: 간단한 relify 트레이스 ═══

#eval do
  let mut tr : Trace := []
  let t : Triple Nat := ⟨10, 20, 30⟩
  let (r1, tr1) := tracedRelify (· + ·) t tr
  let (r2, tr2) := tracedRelify (· + ·) r1 tr1
  return tr2.dump

-- ═══ 실행 2: chain 트레이스 (mod 7) ═══

#eval do
  let t : Triple Nat := ⟨0, 1, 2⟩
  let rel := fun a b => (a + b) % 7
  let (_, tr) := tracedChain rel t 5 []
  return tr.dump

-- ═══ 실행 3: 전체 스택 관통 — Goldbach ═══

-- HW → FW → Trans → HV → OS 전체 경로.
#eval do
  let mut tr : Trace := []

  -- Layer 0 (HW): Lean 시작.
  tr := tr.push .hw "init" "Lean kernel" "type check ready"

  -- Layer 1 (FW): Triple 생성 + relify.
  let t : Triple Nat := ⟨2, 3, 5⟩
  tr := tr.push .fw "Triple" "gen" s!"({t.x}, {t.y}, {t.z})"
  let (r, tr2) := tracedRelify (· + ·) t tr
  tr := tr2
  tr := tr.push .fw "pairs(3)" "C(3,2)" s!"{pairs 3}"

  -- Layer 1→2 (Trans): chain → ℕ.
  let (_, tr3) := tracedChainToNat 100 tr
  tr := tr3

  -- Layer 2 (HV): PA 연산.
  let (sum, tr4) := tracedPAAdd 47 53 tr
  tr := tr4

  -- Layer 3 (OS): Goldbach 검사.
  let (result, tr5) := tracedGoldbach sum tr
  tr := tr5

  -- 최종 출력.
  tr := tr.push .app "report" s!"goldbach({sum})" s!"{result}"
  return tr.dump

-- ═══ 실행 4: 범위 Goldbach 트레이스 ═══

#eval do
  let mut tr : Trace := []
  tr := tr.push .hw "init" "batch mode" "ready"
  for n in [4, 6, 8, 10, 20, 50, 100] do
    let (result, tr2) := tracedGoldbach n tr
    tr := tr2
  return tr.dump

-- ═══ 실행 5: 약점 탐지 트레이스 ═══

#eval do
  let mut tr : Trace := []
  -- constRel 공격.
  let constRel := fun (a : Nat) (_ : Nat) => a
  let t : Triple Nat := ⟨1, 2, 3⟩
  let (r, tr2) := tracedRelify constRel t tr
  -- 구분 붕괴 여부 확인.
  let collapsed := r.x == r.y || r.x == r.z || r.y == r.z
  tr := tr2.push .fw "distinction_check"
    s!"({r.x},{r.y},{r.z})" s!"collapsed={collapsed}"
  return tr.dump

-- ═══ 트레이스 분석 유틸 ═══

-- 레이어별 프레임 수 세기.
def Trace.countByLayer (t : Trace) : List (Layer × Nat) :=
  [.hw, .fw, .trans, .hv, .os, .app].map fun l =>
    (l, t.filter (·.layer == l) |>.length)

-- 특정 레이어만 필터.
def Trace.filterLayer (t : Trace) (l : Layer) : Trace :=
  t.filter (·.layer == l)

-- 마지막 프레임.
def Trace.last? (t : Trace) : Option Frame :=
  t.getLast?

-- ═══ 정리: 트레이스 프레임워크가 모든 레이어를 관통 ═════

-- HW(init) → FW(Triple, relify, pairs)
-- → Trans(chain→ℕ) → HV(PA.add) → OS(goldbach) → App(report).
-- 각 프레임에 layer, operation, input, output 기록.
-- 약점(constRel 붕괴)도 트레이스에서 보임.
-- 스택 트레이스 = 213 아키텍처의 X-ray.
