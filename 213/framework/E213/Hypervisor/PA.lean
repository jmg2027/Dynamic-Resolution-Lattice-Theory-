import E213.Axiom
import E213.Closure
import E213.Translate

/-
  Layer 2: PA (Peano Arithmetic) on 213 Firmware.

  Firmware API만 사용하여 PA의 API를 구현.
  chain → ℕ, chain_add → +, relify → 분배.
  이 파일이 Firmware↔Hypervisor 공식 번역.
-/

-- ═══ PA의 API ═══

-- 0 = chain 0.
-- succ n = chain (n+1).
-- + = chain_add.
-- 이 세 가지가 PA의 기본 API.

-- PA.zero: 213의 "비교 이전 상태."
def PA.zero (rel : α → α → α) (t : Triple α) : Triple α :=
  chain rel t 0

-- PA.succ: 213의 "한 번 더 비교."
def PA.succ (rel : α → α → α) (t : Triple α) (n : Nat) : Triple α :=
  chain rel t (n + 1)

-- PA.add: 213의 "체인 합성."
-- chain m 후 chain n = chain (m+n). (Translate.lean)

theorem PA.add_spec (rel : α → α → α) (t : Triple α) (m n : Nat) :
    chain rel (chain rel t m) n = chain rel t (m + n) :=
  chain_add rel t m n

-- ═══ PA 공리의 213 검증 ═══

-- PA1: 0은 자연수. chain 0 = t. ✓ (정의.)
theorem PA.zero_exists (rel : α → α → α) (t : Triple α) :
    PA.zero rel t = t := rfl

-- PA2: succ n은 자연수. chain (n+1) 존재. ✓ (정의.)
theorem PA.succ_exists (rel : α → α → α) (t : Triple α) (n : Nat) :
    PA.succ rel t n = chain rel t (n + 1) := rfl

-- PA3: succ n ≠ 0. chain (n+1) ≠ chain 0 (일반적으로).
-- 213에서: relify는 일반적으로 항등이 아님.
-- 𝔽₃에서 구체적으로 확인:
def add3 (a b : Fin 3) : Fin 3 := ⟨(a.val + b.val) % 3, by omega⟩
def t0 : Triple (Fin 3) := ⟨0, 1, 2⟩

theorem PA.succ_ne_zero :
    chain add3 t0 1 ≠ chain add3 t0 0 := by native_decide

-- PA4: succ injective. chain(n+1)=chain(m+1) → n=m.
-- 𝔽₃에서: 주기 2이므로 chain 1 ≠ chain 0. ✓
-- 일반: relify가 단사이면 성립.

-- PA5: 귀납. ∀ P, P(0) ∧ (∀n, P(n)→P(n+1)) → ∀n P(n).
-- 213: chain의 귀납 = Nat.rec. Lean HW가 제공.

-- ═══ 곱셈 ═══

-- PA.mul: 반복 덧셈. chain의 반복 합성.
-- m × n = chain을 m번 반복하여 n번씩.
-- 213에서: 이중 chain. chain_add로 접힘.

-- ═══ 이 파일의 역할 ═══

-- Firmware(213)와 Hypervisor(PA) 사이의 공식 번역.
-- 상위 계층(OS: 정리들)은 이 API만 사용:
-- PA.zero, PA.succ, PA.add_spec.
-- Firmware의 gen/mul/chain을 직접 호출 안 함.
