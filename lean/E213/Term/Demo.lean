import E213.Term.Term

/-!
# E213.Term.Demo — first axiom-free capstone.

Vision check: proves core facts of 213 without using *any* of the
Lean kernel axioms (propext, Quot.sound, Classical.choice).
All proofs are by `rfl` (definitional reduction) → `#print axioms`
should return an empty list.
-/

namespace E213.Term.Demo

open Term

/-- Dimension law: n_S + n_T = d  (3 + 2 = 5).
    The most fundamental integer relation of the theory. -/
theorem dim_law : Term.equiv (add Term.nS Term.nT) Term.d = true := rfl

/-- c = n_T  (CLAUDE.md: c=2, n_T=2). -/
theorem c_eq_nT : Term.equiv Term.c Term.nT = true := rfl

/-- d² = 25  (ATM_029 topological counting → arithmetic foundation of α_GUT).
    Verified via equiv with *another Term* of the form 25 = 5·4 + 5. -/
theorem d_sq_25 :
    Term.equiv (mul Term.d Term.d)
          (add (mul Term.d (succ (succ (succ (succ zero))))) Term.d) = true := rfl

/-- Reinforcement: eval of d·d is *literally* 25. -/
theorem eval_d_sq : Term.eval (mul Term.d Term.d) = 25 := rfl

/-- (n_S · n_T)² = 36 — count squared. -/
theorem nSnT_sq_36 : Term.eval (mul (mul Term.nS Term.nT) (mul Term.nS Term.nT)) = 36 := rfl

/-- 2 n_S² = 18  (Argon octet closure count). -/
theorem two_nS_sq : Term.eval (mul (succ (succ zero)) (mul Term.nS Term.nS)) = 18 := rfl

/-- 2 n_S³ = 54  (Xe period closure). -/
theorem two_nS_cube :
    Term.eval (mul (succ (succ zero)) (mul Term.nS (mul Term.nS Term.nS))) = 54 := rfl

end E213.Term.Demo

/-! ## Axiom audit

Prints which axioms each capstone depends on.
Expected: all empty lists (no axioms). -/

#print axioms E213.Term.Demo.dim_law
#print axioms E213.Term.Demo.c_eq_nT
#print axioms E213.Term.Demo.d_sq_25
#print axioms E213.Term.Demo.eval_d_sq
#print axioms E213.Term.Demo.nSnT_sq_36
#print axioms E213.Term.Demo.two_nS_sq
#print axioms E213.Term.Demo.two_nS_cube
