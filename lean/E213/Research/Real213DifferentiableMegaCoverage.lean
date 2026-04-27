import E213.Research.Real213DifferentiableMid

/-!
# Research.Real213DifferentiableMegaCoverage

Phase AM: total polynomial-differentiation coverage 0-16 in a single
12-fact theorem.  Mirror of `polynomial_coverage_1_to_16` (IsSmooth side).

## Coverage

  Degree  0:  idIsDifferentiable           modulus = k
  Degree  2:  squareIsDifferentiable       modulus = 2k
  Degree  3:  cubeIsDifferentiable         modulus = 3k
  Degree  4:  quarticIsDifferentiable      modulus = 4k
  Degree  5:  quinticIsDifferentiable      modulus = 5k
  Degree  6:  sexticIsDifferentiable       modulus = 6k
  Degree  7:  septicIsDifferentiable       modulus = 7k
  Degree  8:  octicIsDifferentiable        modulus = 8k
  Degree  9:  nonicIsDifferentiable        modulus = 9k
  Degree 10:  decicIsDifferentiable        modulus = 10k
  Degree 12:  dodecicIsDifferentiable      modulus = 12k
  Degree 16:  hexadecicIsDifferentiable    modulus = 16k
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **Polynomial differentiation total coverage 0-16**: all concrete
    polynomial IsDifferentiable instances + their modulus equalities
    in a single conjunctive theorem. -/
theorem polynomial_diff_full_coverage (k : Nat) :
    idIsDifferentiable.linearityModulus k = k
    ∧ squareIsDifferentiable.linearityModulus k = 2 * k
    ∧ cubeIsDifferentiable.linearityModulus k = 3 * k
    ∧ quarticIsDifferentiable.linearityModulus k = 4 * k
    ∧ quinticIsDifferentiable.linearityModulus k = 5 * k
    ∧ sexticIsDifferentiable.linearityModulus k = 6 * k
    ∧ septicIsDifferentiable.linearityModulus k = 7 * k
    ∧ octicIsDifferentiable.linearityModulus k = 8 * k
    ∧ nonicIsDifferentiable.linearityModulus k = 9 * k
    ∧ decicIsDifferentiable.linearityModulus k = 10 * k
    ∧ dodecicIsDifferentiable.linearityModulus k = 12 * k
    ∧ hexadecicIsDifferentiable.linearityModulus k = 16 * k :=
  ⟨rfl,
   squareIsDifferentiable_modulus k, cubeIsDifferentiable_modulus k,
   quarticIsDifferentiable_modulus k, quinticIsDifferentiable_modulus k,
   sexticIsDifferentiable_modulus k, septicIsDifferentiable_modulus k,
   octicIsDifferentiable_modulus k, nonicIsDifferentiable_modulus k,
   decicIsDifferentiable_modulus k, dodecicIsDifferentiable_modulus k,
   hexadecicIsDifferentiable_modulus k⟩

end E213.Research.Real213CutSum
