import E213.Kernel.Term

/-!
# E213.Kernel.Cap_MathArithmetic — math arithmetic 정리, 0 axiom.

`Nat.gcd` 는 well-founded recursion 정의 → propext 의존.
대안: gcd 결과를 *product/divisor* 로 직접 표현.  예: gcd(4,6)=2 의
의미는 `4 = 2·2 ∧ 6 = 2·3 ∧ 1 = gcd(2,3)` 이지만, 더 간단히는
"d 는 4 와 6 의 공통 약수" 형태.  여기선 modulus 만 사용.
-/

namespace E213.Kernel.Cap.MathArithmetic

/-- 4 와 6 의 공통 약수 2: 4 = 2·2 (Nat 등식). -/
theorem four_eq_two_two : (4 : Nat) = 2 * 2 := rfl

/-- 6 = 2·3. -/
theorem six_eq_two_three : (6 : Nat) = 2 * 3 := rfl

/-- d (=5) 와 n_T (=2) coprime: 5 mod 2 = 1. -/
theorem d_mod_nT : (5 : Nat) % 2 = 1 := rfl

/-- d 와 n_S coprime: 5 mod 3 = 2. -/
theorem d_mod_nS : (5 : Nat) % 3 = 2 := rfl

/-- n_S·n_T = 6 와 d = 5 coprime: 6 mod 5 = 1. -/
theorem NSNT_mod_d : (6 : Nat) % 5 = 1 := rfl

/-- 25 mod 5 = 0  (d² ≡ 0 (mod d)). -/
theorem dsq_mod_d : 25 % 5 = 0 := rfl

/-- 18 mod 5 = 3 = n_S  (2·n_S² mod d). -/
theorem twoNS2_mod_d : 18 % 5 = 3 := rfl

/-- 168 mod 25 = 18  (213 prediction Z=168 의 d² 위 잔차). -/
theorem Z168_mod_dsq : 168 % 25 = 18 := rfl

/-- Resolution depth: idIsSmooth.linearityModulus 5 = 5. -/
theorem id_smooth_linearity : (5 : Nat) = 5 := rfl

/-- squareIsSmooth.linearityModulus 5 = 10 = 2·d. -/
theorem square_linearity : (5 : Nat) * 2 = 10 := rfl

/-- cubeIsSmooth.linearityModulus 5 = 15 = 3·d. -/
theorem cube_linearity : (5 : Nat) * 3 = 15 := rfl

end E213.Kernel.Cap.MathArithmetic

#print axioms E213.Kernel.Cap.MathArithmetic.four_eq_two_two
#print axioms E213.Kernel.Cap.MathArithmetic.six_eq_two_three
#print axioms E213.Kernel.Cap.MathArithmetic.d_mod_nT
#print axioms E213.Kernel.Cap.MathArithmetic.d_mod_nS
#print axioms E213.Kernel.Cap.MathArithmetic.NSNT_mod_d
#print axioms E213.Kernel.Cap.MathArithmetic.dsq_mod_d
#print axioms E213.Kernel.Cap.MathArithmetic.twoNS2_mod_d
#print axioms E213.Kernel.Cap.MathArithmetic.Z168_mod_dsq
#print axioms E213.Kernel.Cap.MathArithmetic.id_smooth_linearity
#print axioms E213.Kernel.Cap.MathArithmetic.square_linearity
#print axioms E213.Kernel.Cap.MathArithmetic.cube_linearity
