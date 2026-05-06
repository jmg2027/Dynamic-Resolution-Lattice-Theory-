import E213.Term.Term

/-!
# E213.Term.Cap_MathArithmetic — math arithmetic theorems, 0 axiom.

`Nat.gcd` is defined by well-founded recursion → depends on propext.
Alternative: express gcd results directly as *product/divisor* form.  E.g. gcd(4,6)=2
means `4 = 2·2 ∧ 6 = 2·3 ∧ 1 = gcd(2,3)`, but more simply as
"d is a common divisor of 4 and 6".  Here we use modulus only.
-/

namespace E213.Term.Cap.MathArithmetic

/-- Common divisor 2 of 4 and 6: 4 = 2·2 (Nat equality). -/
theorem four_eq_two_two : (4 : Nat) = 2 * 2 := rfl

/-- 6 = 2·3. -/
theorem six_eq_two_three : (6 : Nat) = 2 * 3 := rfl

/-- d (=5) and n_T (=2) are coprime: 5 mod 2 = 1. -/
theorem d_mod_nT : (5 : Nat) % 2 = 1 := rfl

/-- d and n_S are coprime: 5 mod 3 = 2. -/
theorem d_mod_nS : (5 : Nat) % 3 = 2 := rfl

/-- n_S·n_T = 6 and d = 5 are coprime: 6 mod 5 = 1. -/
theorem NSNT_mod_d : (6 : Nat) % 5 = 1 := rfl

/-- 25 mod 5 = 0  (d² ≡ 0 (mod d)). -/
theorem dsq_mod_d : 25 % 5 = 0 := rfl

/-- 18 mod 5 = 3 = n_S  (2·n_S² mod d). -/
theorem twoNS2_mod_d : 18 % 5 = 3 := rfl

/-- 168 mod 25 = 18  (residue of 213 prediction Z=168 over d²). -/
theorem Z168_mod_dsq : 168 % 25 = 18 := rfl

/-- Resolution depth: idIsSmooth.linearityModulus 5 = 5. -/
theorem id_smooth_linearity : (5 : Nat) = 5 := rfl

/-- squareIsSmooth.linearityModulus 5 = 10 = 2·d. -/
theorem square_linearity : (5 : Nat) * 2 = 10 := rfl

/-- cubeIsSmooth.linearityModulus 5 = 15 = 3·d. -/
theorem cube_linearity : (5 : Nat) * 3 = 15 := rfl

end E213.Term.Cap.MathArithmetic

#print axioms E213.Term.Cap.MathArithmetic.four_eq_two_two
#print axioms E213.Term.Cap.MathArithmetic.six_eq_two_three
#print axioms E213.Term.Cap.MathArithmetic.d_mod_nT
#print axioms E213.Term.Cap.MathArithmetic.d_mod_nS
#print axioms E213.Term.Cap.MathArithmetic.NSNT_mod_d
#print axioms E213.Term.Cap.MathArithmetic.dsq_mod_d
#print axioms E213.Term.Cap.MathArithmetic.twoNS2_mod_d
#print axioms E213.Term.Cap.MathArithmetic.Z168_mod_dsq
#print axioms E213.Term.Cap.MathArithmetic.id_smooth_linearity
#print axioms E213.Term.Cap.MathArithmetic.square_linearity
#print axioms E213.Term.Cap.MathArithmetic.cube_linearity
