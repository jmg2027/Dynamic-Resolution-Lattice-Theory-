import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Test.StackTrace
import E213.Hypervisor.TheoryBuilder

/-
  구체적 정리들의 213 분해 + 증명 스택 트레이스.

  각 정리를:
  1. 진술을 213 명령어로 분해.
  2. 증명의 각 단계를 FW 연산으로 분해.
  3. 스택 트레이스로 전체 흐름 확인.
-/

-- ═══ 정리 명세 ═══

structure ProofStep where
  name : String
  fw_op : FWOp
  depth : Nat
  description : String
  deriving Repr

structure TheoremSpec where
  name : String
  theory : String       -- 어떤 이론(OS)에 속하는가
  statement_depth : Nat -- 진술의 depth
  steps : List ProofStep
  deriving Repr

def TheoremSpec.proof_depth (t : TheoremSpec) : Nat :=
  t.steps.foldl (fun d s => Nat.max d s.depth) 0

def TheoremSpec.fw_ops (t : TheoremSpec) : List FWOp :=
  t.steps.map (·.fw_op) |>.eraseDups

-- ═══ 정리 1: 유클리드 (소수 무한) ═══

def euclid_infinitude : TheoremSpec := {
  name := "Euclid: 소수는 무한하다"
  theory := "PA"
  statement_depth := 100  -- ∀ finite set → ∃ prime not in it. depth ω.
  steps := [
    { name := "assume_finite"
      fw_op := .usesGen
      depth := 0
      description := "유한 집합 S = {p₁,...,pₖ} 가정. gen으로 선택." },
    { name := "construct_N"
      fw_op := .usesMul
      depth := 1
      description := "N = p₁×p₂×...×pₖ + 1 구성. mul 반복." },
    { name := "N_has_prime_factor"
      fw_op := .usesMul
      depth := 1
      description := "N ≥ 2이므로 소인수 q 존재. mul(q, N/q) = N." },
    { name := "q_not_in_S"
      fw_op := .usesEq
      depth := 1
      description := "q|N이고 q|p₁...pₖ이면 q|1. 모순. eq로 판정." },
    { name := "contradiction"
      fw_op := .usesEq
      depth := 0
      description := "q ∉ S. S가 모든 소수를 포함한다는 가정 모순." }
  ]
}

-- 213 해석:
-- 진술: depth ω (∀ finite set). 증명: max depth 1.
-- 환원폭: ω → 1. "임의의 유한 집합"을 "하나 구성"으로 환원.
-- FW 연산: gen(가정) → mul(구성) → mul(인수) → eq(모순).
-- 증명 전체가 depth 1! ∀만 빼면 유한 검사.

-- ═══ 정리 2: 라그랑주 (군론) ═══

def lagrange : TheoremSpec := {
  name := "Lagrange: |H| divides |G|"
  theory := "Group"
  statement_depth := 2
  steps := [
    { name := "define_cosets"
      fw_op := .usesMul
      depth := 1
      description := "gH = {g·h : h∈H}. mul로 각 원소에 g 적용." },
    { name := "cosets_partition"
      fw_op := .usesEq
      depth := 2
      description := "잉여류가 분할. g₁H=g₂H or 서로소. depth 2 (결합)." },
    { name := "cosets_same_size"
      fw_op := .usesMul
      depth := 1
      description := "g·: H→gH 전단사. mul이 크기 보존." },
    { name := "count"
      fw_op := .usesEq
      depth := 1
      description := "|G| = [G:H]×|H|. 개수 세기 = eq 반복." }
  ]
}

-- 213 해석:
-- 진술 depth 2. 증명 max depth 2. 환원폭 0!
-- 진술과 증명이 같은 depth. "자연스러운" 정리.
-- 전부 mul + eq. chain 불필요. 유한 군에서 native_decide 가능.

-- ═══ 정리 3: 칸토어 대각선 ═══

def cantor_diagonal : TheoremSpec := {
  name := "Cantor: |S| < |P(S)|"
  theory := "ZFC"
  statement_depth := 100  -- ∀S, ∀f:S→P(S), f not surjective. depth ω.
  steps := [
    { name := "assume_surjection"
      fw_op := .usesGen
      depth := 0
      description := "f: S→P(S) 전사 가정. gen으로 f 선택." },
    { name := "construct_diagonal"
      fw_op := .usesMul
      depth := 1
      description := "D = {x∈S : x∉f(x)}. mul(x, f(x))의 부정." },
    { name := "D_is_subset"
      fw_op := .usesEq
      depth := 1
      description := "D ⊆ S. D ∈ P(S)." },
    { name := "find_preimage"
      fw_op := .usesGen
      depth := 1
      description := "f 전사이므로 ∃d, f(d)=D. gen으로 d 선택." },
    { name := "self_reference"
      fw_op := .usesEq
      depth := 1
      description := "d∈D ↔ d∉f(d)=D. 자기참조 모순. eq 판정." }
  ]
}

-- 213 해석:
-- 진술 depth ω (∀S ∀f). 증명 max depth 1.
-- 환원폭: ω → 1. 유클리드와 같은 패턴.
-- 핵심: self_reference (자기참조). 213의 구조:
-- mul(d, f(d)) = mul(d, D). D는 mul(d,-)의 부정으로 정의.
-- "¬로 정의된 것에 자기를 넣으면 모순." Negation.lean의 정리!

-- ═══ 정리 4: 중간값 정리 ═══

def intermediate_value : TheoremSpec := {
  name := "IVT: f(a)<0<f(b) → ∃c, f(c)=0"
  theory := "Topology"
  statement_depth := 100  -- 연속 = ε-δ = depth ω.
  steps := [
    { name := "bisect"
      fw_op := .usesMul
      depth := 1
      description := "m=(a+b)/2. f(m) 부호 확인. mul로 비교." },
    { name := "choose_half"
      fw_op := .usesEq
      depth := 1
      description := "f(m)<0이면 [m,b], f(m)>0이면 [a,m]. eq 판정." },
    { name := "iterate"
      fw_op := .usesChain
      depth := 100
      description := "이분법 반복. chain. 구간 길이 → 0. depth ω." },
    { name := "completeness"
      fw_op := .usesEq
      depth := 100
      description := "코시 수열의 극한 존재. ℝ 완비성. depth ω." },
    { name := "continuity_transfer"
      fw_op := .usesChain
      depth := 100
      description := "f 연속 → f(c)=0. ε-δ. depth ω." }
  ]
}

-- 213 해석:
-- 진술 depth ω (연속 조건). 증명도 depth ω (이분법 극한).
-- 환원폭: 0! 진술과 증명이 같은 depth.
-- depth ω 단계 3개: iterate, completeness, continuity.
-- 위상 정리는 "depth ω에서 depth ω로." 환원이 아니라 전개.
-- 대수 정리(라그랑주)와의 차이: 대수는 환원폭 0 (자연), 위상도 0이지만 depth가 높음.

-- ═══ 정리 5: FTA (산술의 기본 정리) ═══

def fta : TheoremSpec := {
  name := "FTA: 유일한 소인수분해"
  theory := "PA"
  statement_depth := 2
  steps := [
    { name := "existence_induction"
      fw_op := .usesChain
      depth := 100
      description := "n에 대한 강한 귀납. chain level n. depth ω." },
    { name := "n_prime_or_composite"
      fw_op := .usesMul
      depth := 1
      description := "n 소수이면 끝. 아니면 n=ab. mul 분해." },
    { name := "recurse"
      fw_op := .usesChain
      depth := 100
      description := "a, b < n에 귀납. chain 감소." },
    { name := "uniqueness_euclid_lemma"
      fw_op := .usesMul
      depth := 2
      description := "p|ab → p|a or p|b. mul depth 2." },
    { name := "induction_on_length"
      fw_op := .usesChain
      depth := 100
      description := "분해 길이에 귀납. chain." }
  ]
}

-- 213 해석:
-- 진술 depth 2 (소인수분해 = mul 반복). 증명 depth ω (귀납).
-- 환원폭: 2 → ω → 2. "ω를 거쳐서 2로 돌아옴."
-- 귀납(depth ω)이 다리. 진술 자체는 유한(depth 2).
-- "유한 진술이지만 증명에 무한이 필요한" 패턴.

-- ═══ 비교 출력 ═══

#eval [euclid_infinitude, lagrange, cantor_diagonal,
       intermediate_value, fta].map fun t =>
  (t.name, t.statement_depth, t.proof_depth, t.steps.length, t.fw_ops)

-- ═══ 스택 트레이스: 유클리드 ═══

#eval do
  let mut tr : Trace := []
  tr := tr.push .hw "init" "Euclid's theorem" "start"
  for step in euclid_infinitude.steps do
    tr := tr.push .fw step.name step.description s!"depth {step.depth}"
  tr := tr.push .os "QED" "소수 무한" "proved at depth 1"
  return tr.dump

-- ═══ 스택 트레이스: 칸토어 ═══

#eval do
  let mut tr : Trace := []
  tr := tr.push .hw "init" "Cantor diagonal" "start"
  for step in cantor_diagonal.steps do
    tr := tr.push .fw step.name step.description s!"depth {step.depth}"
  tr := tr.push .os "QED" "|S|<|P(S)|" "proved at depth 1"
  return tr.dump

-- ═══ 정리의 213 분류 체계 ═══

-- Type A: 진술 ω, 증명 ≤ 2. 환원폭 큼. "쉬운" 정리.
--   유클리드(ω→1), 칸토어(ω→1), 비둘기집(ω→0).

-- Type B: 진술 ≤ 2, 증명 ≤ 2. 환원폭 0. "자연스러운" 정리.
--   라그랑주(2→2).

-- Type C: 진술 ≤ 2, 증명 ω. "다리가 필요한" 정리.
--   FTA(2→ω→2). 와일즈(2→ω→0).

-- Type D: 진술 ω, 증명 ω. 환원폭 0이지만 높음. "어려운" 정리.
--   IVT(ω→ω). 골드바흐(?).
