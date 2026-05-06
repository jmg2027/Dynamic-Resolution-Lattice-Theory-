import E213.Term.Term

/-!
# E213.Term.MonomialAxioms — basic algebra over `Term`.

Concrete-value rewrite axioms used by the Rust `normal_form` mapper.
Each closes by `rfl` because both sides reduce to the same `Nat`
under `eval`.  No `simp`, no `Nat.mul_comm` invocation, no propext —
everything is *literally* the same number after evaluation.

Used by:
  * `rust-engine/crates/kernel/src/normal_form.rs` — `RewriteRule`
    impls cite each theorem name.

Lean citations (all 0 axiom):
  ns_mul_nt_eq_six, mul_comm_ns_nt, ns_sq_eq_9, nt_sq_eq_4, d_sq_eq_25,
  ns_plus_nt_eq_d.
-/

namespace E213.Term.MonomialAxioms

open Term

/-- `NS · NT = 6`. -/
theorem ns_mul_nt_eq_six : eval (mul nS nT) = 6 := rfl

/-- `NS · NT = NT · NS` at concrete (3, 2): commutativity instance. -/
theorem mul_comm_ns_nt : eval (mul nS nT) = eval (mul nT nS) := rfl

/-- `NS² = 9`. -/
theorem ns_sq_eq_9 : eval (mul nS nS) = 9 := rfl

/-- `NT² = 4`. -/
theorem nt_sq_eq_4 : eval (mul nT nT) = 4 := rfl

/-- `d² = 25`. -/
theorem d_sq_eq_25 : eval (mul d d) = 25 := rfl

/-- `NS + NT = d` (= 5). -/
theorem ns_plus_nt_eq_d : eval (add nS nT) = eval d := rfl

end E213.Term.MonomialAxioms

#print axioms E213.Term.MonomialAxioms.ns_mul_nt_eq_six
#print axioms E213.Term.MonomialAxioms.mul_comm_ns_nt
#print axioms E213.Term.MonomialAxioms.ns_sq_eq_9
#print axioms E213.Term.MonomialAxioms.nt_sq_eq_4
#print axioms E213.Term.MonomialAxioms.d_sq_eq_25
#print axioms E213.Term.MonomialAxioms.ns_plus_nt_eq_d
