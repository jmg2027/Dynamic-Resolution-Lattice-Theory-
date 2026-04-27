/-!
# E213.Kernel.Term — 213 의 deep-embedded AST.

비전: Lean 은 syntactic host, 213 이 진짜 kernel.
Term 은 *데이터* 이고, 모든 의미는 Term 위의 *총함수* 로 결정됨.
Lean 의 propext / Quot.sound / Classical 어느 것도 Term 의
의미에 load-bearing 이 아니다.

Raw 원시 (CLAUDE.md 공리: "things exist with pairwise relations"):
  zero  : Raw 의 distinguishing-구조 부재
  succ  : Raw 의 새 entity 추가
  add   : counting 합성
  mul   : pairwise grouping (Cartesian)

후속 layer 가 add/mul 로 entity 산술 + Lens 구분 정의.
-/

namespace E213.Kernel

inductive Term : Type
  | zero : Term
  | succ : Term → Term
  | add  : Term → Term → Term
  | mul  : Term → Term → Term
  deriving Repr

namespace Term

/-- 213 표준 상수 (CLAUDE.md "Key Constants"). -/
def nS : Term := succ (succ (succ zero))      -- 3
def nT : Term := succ (succ zero)              -- 2
def d  : Term :=                                -- 5
  succ (succ (succ (succ (succ zero))))
def c  : Term := succ (succ zero)              -- 2

/-- Term 의 Raw eval: Term → ℕ.
    구조귀납 + 핵심 산술만 사용 → 0 axiom. -/
def eval : Term → Nat
  | zero      => 0
  | succ t    => Nat.succ (eval t)
  | add a b   => eval a + eval b
  | mul a b   => eval a * eval b

/-- 213-internal equivalence: 두 Term 이 같은 ℕ 로 eval.
    Bool 반환 — Prop 평등 / propext 우회. -/
def equiv (a b : Term) : Bool := Nat.beq (eval a) (eval b)

end Term
end E213.Kernel
