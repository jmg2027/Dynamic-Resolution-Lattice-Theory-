import E213.Kernel.Term

/-!
# E213.Kernel.Demo — 첫 axiom-free capstone.

비전 검증: Lean kernel axiom (propext, Quot.sound, Classical.choice)
*어느 것도* 사용하지 않고 213 의 핵심 사실 입증.
모든 증명은 `rfl` (definitional reduction) → `#print axioms` 가
빈 리스트 반환해야 함.
-/

namespace E213.Kernel.Demo

open Term

/-- 차원 법칙: n_S + n_T = d  (3 + 2 = 5).
    이론의 가장 기본 정수 관계. -/
theorem dim_law : equiv (add nS nT) d = true := rfl

/-- c = n_T  (CLAUDE.md: c=2, n_T=2). -/
theorem c_eq_nT : equiv c nT = true := rfl

/-- d² = 25  (ATM_029 의 위상 counting → α_GUT 의 산술 토대).
    25 = 5·4 + 5 형태로 *다른 Term* 과 equiv 검증. -/
theorem d_sq_25 :
    equiv (mul d d)
          (add (mul d (succ (succ (succ (succ zero))))) d) = true := rfl

/-- 보강: d·d 의 eval 이 *literally* 25. -/
theorem eval_d_sq : eval (mul d d) = 25 := rfl

/-- (n_S · n_T)² = 36 — Phase 차원수 squared. -/
theorem nSnT_sq_36 : eval (mul (mul nS nT) (mul nS nT)) = 36 := rfl

/-- 2 n_S² = 18  (Argon octet 닫힘 카운트). -/
theorem two_nS_sq : eval (mul (succ (succ zero)) (mul nS nS)) = 18 := rfl

/-- 2 n_S³ = 54  (Xe period 닫힘). -/
theorem two_nS_cube :
    eval (mul (succ (succ zero)) (mul nS (mul nS nS))) = 54 := rfl

end E213.Kernel.Demo

/-! ## Axiom 감사

각 capstone 이 어느 axiom 에 의존하는지 출력.
기대값: 모두 빈 리스트 (no axioms). -/

#print axioms E213.Kernel.Demo.dim_law
#print axioms E213.Kernel.Demo.c_eq_nT
#print axioms E213.Kernel.Demo.d_sq_25
#print axioms E213.Kernel.Demo.eval_d_sq
#print axioms E213.Kernel.Demo.nSnT_sq_36
#print axioms E213.Kernel.Demo.two_nS_sq
#print axioms E213.Kernel.Demo.two_nS_cube
