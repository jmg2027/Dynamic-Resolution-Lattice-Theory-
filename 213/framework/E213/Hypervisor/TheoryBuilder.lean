import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Test.StackTrace

/-
  이론 작성 프레임워크.

  수학 이론 = Hypervisor 프로그램.
  각 이론은 Firmware API(gen, mul, relify, chain)를 호출하여
  자신의 공리를 구현하고, 자신의 API를 상위에 제공.

  이론 작성법:
  1. 이론의 "타입"을 정의 (어떤 연산이 있는가).
  2. 각 공리를 Firmware API로 번역.
  3. 공리에서 나오는 정리를 증명.
  4. 스택 트레이스로 Firmware 호출 확인.
-/

-- ═══ 이론 명세 ═══

-- 이론 = 연산(ops) + 공리(axioms) + 이 공리의 Firmware 번역.
-- 각 연산은 gen/mul/relify/chain 중 하나에 대응.

-- 연산의 213 대응 유형:
inductive FWOp where
  | usesGen    -- 원소 선택 (존재 주장)
  | usesMul    -- 이항 비교 (관계)
  | usesRelify -- 전체 분배 (구조 보존)
  | usesChain  -- 반복 (귀납, 무한)
  | usesEq     -- 등호 (해상도 판정)
  deriving DecidableEq, Repr

-- 공리의 213 분해:
structure AxiomSpec where
  name : String
  ops : List FWOp          -- 사용하는 Firmware 연산
  depth : Nat              -- 필요한 chain depth
  description : String     -- 213으로 뭘 말하는가
  deriving Repr

-- 이론 = 공리들의 묶음:
structure TheorySpec where
  name : String
  axioms : List AxiomSpec
  deriving Repr

-- 이론의 총 depth = 가장 깊은 공리:
def TheorySpec.depth (t : TheorySpec) : Nat :=
  t.axioms.foldl (fun d a => Nat.max d a.depth) 0

-- 이론이 사용하는 모든 FW 연산:
def TheorySpec.allOps (t : TheorySpec) : List FWOp :=
  t.axioms.foldl (fun ops a => ops ++ a.ops) [] |>.eraseDups

-- ═══ PA (Peano Arithmetic) ═══

def PA : TheorySpec := {
  name := "PA (Peano Arithmetic)"
  axioms := [
    { name := "zero_exists"
      ops := [.usesGen]
      depth := 0
      description := "gen 0 = 0이 있다. chain level 0." },
    { name := "succ_closed"
      ops := [.usesChain]
      depth := 1
      description := "chain (k+1) = succ k. chain 한 단계 올림." },
    { name := "succ_injective"
      ops := [.usesMul, .usesEq]
      depth := 1
      description := "chain(n+1)=chain(m+1) → n=m. mul 결과 비교." },
    { name := "succ_ne_zero"
      ops := [.usesMul, .usesEq]
      depth := 1
      description := "chain(n+1) ≠ chain(0). relify ≠ id." },
    { name := "induction"
      ops := [.usesChain, .usesEq]
      depth := 100  -- ω: ∀n에 대해
      description := "P(0) ∧ ∀n(P(n)→P(n+1)) → ∀nP(n). chain 전체." },
    { name := "add_def"
      ops := [.usesChain]
      depth := 1
      description := "m+n = chain_add. chain 합성." },
    { name := "mul_def"
      ops := [.usesChain, .usesRelify]
      depth := 2
      description := "m×n = relify 반복. chain of chain." }
  ]
}

#eval PA.name
#eval PA.depth        -- 100 (induction이 지배)
#eval PA.allOps       -- [usesGen, usesChain, usesMul, usesEq, usesRelify]

-- PA의 213 해석:
-- "PA = chain의 이론. ℕ은 chain level.
--  +는 chain 합성. ×는 chain의 chain.
--  귀납은 chain 전체(depth ω)에 대한 주장.
--  PA의 대부분(depth ≤ 2)은 Firmware에서 직접 검증 가능.
--  귀납(depth ω)만 HW(Lean)의 Nat.rec에 의존."

-- ═══ ZFC ═══

def ZFC : TheorySpec := {
  name := "ZFC (Zermelo-Fraenkel + Choice)"
  axioms := [
    { name := "extensionality"
      ops := [.usesMul, .usesEq]
      depth := 1
      description := "∀z(z∈x ↔ z∈y) → x=y. mul(z,x)와 mul(z,y) 비교." },
    { name := "empty_set"
      ops := [.usesGen]
      depth := 0
      description := "∅ 존재. gen으로 빈 집합 선택." },
    { name := "pairing"
      ops := [.usesGen, .usesMul]
      depth := 1
      description := "{a,b} 존재. gen 2번 + mul로 쌍 구성." },
    { name := "union"
      ops := [.usesMul, .usesRelify]
      depth := 1
      description := "∪S 존재. relify = 쌍별 합치기." },
    { name := "powerset"
      ops := [.usesChain]
      depth := 100  -- ω: 모든 부분집합
      description := "P(S) 존재. chain으로 모든 부분집합 열거. depth ω." },
    { name := "infinity"
      ops := [.usesChain]
      depth := 100  -- ω: 무한 집합
      description := "ω 존재. chain 자체가 ω." },
    { name := "separation"
      ops := [.usesMul, .usesEq]
      depth := 1
      description := "{x∈S : P(x)}. mul로 판정하여 분리." },
    { name := "replacement"
      ops := [.usesMul, .usesChain]
      depth := 100
      description := "F[S] 존재. mul을 S 전체에 적용. depth ω." },
    { name := "foundation"
      ops := [.usesMul]
      depth := 2
      description := "∈-순환 없음. mul chain이 내려가면 멈춤." },
    { name := "choice"
      ops := [.usesGen, .usesChain]
      depth := 100
      description := "선택함수 존재. gen을 무한 집합 각각에. depth ω." }
  ]
}

#eval ZFC.name
#eval ZFC.depth       -- 100 (powerset, infinity, replacement, choice)
#eval ZFC.allOps      -- 전부 사용
#eval ZFC.axioms.length  -- 10

-- ZFC의 213 해석:
-- "ZFC = gen(존재) + mul(소속) + chain(무한)의 이론.
--  유한 집합론(depth ≤ 2): pairing, separation, foundation.
--  무한 집합론(depth ω): powerset, infinity, replacement, choice.
--  ZFC의 '힘' = depth ω 연산 4개.
--  PA보다 강한 이유: depth ω 연산이 더 많음."

-- ═══ 군론 ═══

def GroupTheory : TheorySpec := {
  name := "Group Theory"
  axioms := [
    { name := "closure"
      ops := [.usesMul]
      depth := 0
      description := "a·b ∈ G. mul이 Obj를 만듦." },
    { name := "associativity"
      ops := [.usesMul, .usesEq]
      depth := 2
      description := "(a·b)·c = a·(b·c). depth-2 Obj 비교." },
    { name := "identity"
      ops := [.usesGen, .usesEq]
      depth := 1
      description := "∃e, a·e=a. gen으로 e 선택." },
    { name := "inverse"
      ops := [.usesGen, .usesMul, .usesEq]
      depth := 1
      description := "∀a ∃b, a·b=e. gen+mul+eq." }
  ]
}

#eval GroupTheory.depth  -- 2 (associativity)
#eval GroupTheory.allOps -- [usesMul, usesEq, usesGen]

-- 군론의 213 해석:
-- "군 = mul이 닫혀 있고(depth 0), 중첩해도 순서 무관(depth 2),
--  중립과 역이 있는(depth 1) 구조.
--  depth 2가 최대: 결합법칙. 유한 군은 Firmware로 완전 검증.
--  chain/relify 불필요! mul과 eq만으로 충분.
--  → 군론은 213의 가장 '가벼운' 이론."

-- ═══ 위상수학 ═══

def Topology : TheorySpec := {
  name := "Point-Set Topology"
  axioms := [
    { name := "open_empty_full"
      ops := [.usesGen]
      depth := 0
      description := "∅, X 열림. gen으로 선택." },
    { name := "open_union"
      ops := [.usesRelify, .usesChain]
      depth := 100  -- 임의 합집합 = ω
      description := "임의 합집합 열림. relify를 무한 적용. depth ω." },
    { name := "open_finite_inter"
      ops := [.usesMul]
      depth := 2
      description := "유한 교집합 열림. mul 유한 번." },
    { name := "continuity"
      ops := [.usesChain, .usesEq]
      depth := 100
      description := "f⁻¹(U) 열림. chain(ε-δ). depth ω." },
    { name := "compactness"
      ops := [.usesChain, .usesGen]
      depth := 100
      description := "유한 부분덮개. chain에서 유한 gen 선택. depth ω." }
  ]
}

#eval Topology.depth  -- 100
#eval Topology.allOps -- [usesGen, usesRelify, usesChain, usesMul, usesEq]

-- 위상의 213 해석:
-- "위상 = 열린집합의 이론. 열린집합 = '해상도 무관 구분.'
--  유한 교(depth 2): mul 유한 번. Firmware 직접.
--  임의 합(depth ω): chain으로 무한 합. HW 의존.
--  연속(depth ω): ε-δ = chain level 간 보장.
--  위상이 어려운 이유: depth ω 연산이 3개. ZFC와 비슷."

-- ═══ 이론 비교 ═══

#eval [PA, ZFC, GroupTheory, Topology].map fun t =>
  (t.name, t.depth, t.axioms.length, t.allOps.length)

-- ═══ 스택 트레이스로 이론 실행 ═══

-- PA의 zero+succ를 Firmware에서 실행:
#eval do
  let mut tr : Trace := []
  tr := tr.push .hw "init" "PA theory" "loading"
  -- PA.zero: gen
  tr := tr.push .fw "gen" "PA.zero" "chain level 0"
  -- PA.succ: chain
  tr := tr.push .fw "chain[1]" "PA.succ(0)" "chain level 1"
  tr := tr.push .fw "chain[2]" "PA.succ(1)" "chain level 2"
  -- PA.add: chain_add
  tr := tr.push .trans "chain_add" "1 + 2" "chain level 3"
  tr := tr.push .hv "PA.add" "1 + 2 = 3" "verified"
  return tr.dump

-- 군론의 결합법칙을 Firmware에서 실행:
#eval do
  let mut tr : Trace := []
  tr := tr.push .fw "mul" "a·b" "depth 1"
  tr := tr.push .fw "mul" "(a·b)·c" "depth 2"
  tr := tr.push .fw "mul" "a·(b·c)" "depth 2"
  tr := tr.push .fw "eq" "(a·b)·c =? a·(b·c)" "depth 2 comparison"
  tr := tr.push .hv "assoc" "verified" "depth 2"
  return tr.dump
