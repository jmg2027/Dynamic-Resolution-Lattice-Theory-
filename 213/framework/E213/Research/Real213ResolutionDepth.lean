import E213.Research.Real213IsSmooth

/-!
# Research.Real213ResolutionDepth: linearityModulus = resolution depth

## Cross-track parallel (Phase J + Physics)

Sister branch's `Physics/ResolutionDepth.lean` formalized the
principle for gauge couplings:

| Force        | Resolution depth | Form                |
|--------------|-----------------|---------------------|
| α₃ (color)   | N = 1           | exact integer 8     |
| α₂ (weak)    | N = 2           | exact integer 30    |
| α₁ (EM)      | N = ∞           | 6π² transcendental  |

The analog in our analysis track: **`linearityModulus` IS the
resolution depth** of a smooth function.  Polynomial of degree d
needs d dyadic levels per output unit.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **Identity has resolution depth 1**: linearityModulus n = n. -/
theorem idIsSmooth_modulus (n : Nat) :
    idIsSmooth.linearityModulus n = n := rfl

/-- **Constants have resolution depth 0**: linearityModulus n = 0. -/
theorem constIsSmooth_modulus (c : Nat → Nat → Bool) (n : Nat) :
    (constIsSmooth c).linearityModulus n = 0 := rfl

/-- **Linear scaling has resolution depth 1**: same as id. -/
theorem cutScaleIsSmooth_modulus (a b : Nat) (n : Nat) :
    (cutScaleIsSmooth a b).linearityModulus n = n := rfl

/-- **x ↦ x² has resolution depth 2**: linearityModulus n = 2n. -/
theorem squareIsSmooth_modulus (n : Nat) :
    squareIsSmooth.linearityModulus n = 2 * n := by
  show n + n = 2 * n
  rw [Nat.two_mul]

/-- **x ↦ x³ has resolution depth 3**: linearityModulus n = 3n. -/
theorem cubeIsSmooth_modulus (n : Nat) :
    cubeIsSmooth.linearityModulus n = 3 * n := by
  show n + (n + n) = 3 * n
  have e3 : (3 : Nat) * n = n + n + n := by
    rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.add_mul,
        Nat.add_mul, Nat.one_mul]
  rw [e3, Nat.add_assoc]

/-- **x ↦ x⁴ has resolution depth 4**: linearityModulus n = 4n. -/
theorem quarticIsSmooth_modulus (n : Nat) :
    quarticIsSmooth.linearityModulus n = 4 * n := by
  show (n + n) + (n + n) = 4 * n
  have e4 : (4 : Nat) * n = n + n + n + n := by
    rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl,
        Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
  rw [e4]
  omega

/-- **Resolution depth principle (capstone)**: polynomial functions
    of degree d have linearityModulus n = d * n.

    Linear-in-n growth, slope = degree.  This is the analysis-domain
    analog of physics-track ResolutionDepth.depth_principle_witnesses
    — same quantitative pattern (depth = mass-scale cutoff = how many
    dyadic levels exposure of linearity needs). -/
theorem polynomial_resolution_depth_principle (n : Nat) :
    idIsSmooth.linearityModulus n = 1 * n
    ∧ squareIsSmooth.linearityModulus n = 2 * n
    ∧ cubeIsSmooth.linearityModulus n = 3 * n
    ∧ quarticIsSmooth.linearityModulus n = 4 * n := by
  refine ⟨?_, squareIsSmooth_modulus n,
          cubeIsSmooth_modulus n, quarticIsSmooth_modulus n⟩
  rw [Nat.one_mul]
  exact idIsSmooth_modulus n

/-! ### Concrete decide tests — explicit depth values for n = 5

Sister-branch `WhyBasel.lean` style decide-based concrete tests
showing the explicit numerical pattern. -/

/-- id at depth 5: modulus = 5 (slope 1). -/
example : idIsSmooth.linearityModulus 5 = 5 := by decide

/-- square at depth 5: modulus = 10 (slope 2). -/
example : squareIsSmooth.linearityModulus 5 = 10 := by decide

/-- cube at depth 5: modulus = 15 (slope 3). -/
example : cubeIsSmooth.linearityModulus 5 = 15 := by decide

/-- quartic at depth 5: modulus = 20 (slope 4). -/
example : quarticIsSmooth.linearityModulus 5 = 20 := by decide

/-- quintic (x⁵) at depth 5: modulus = 25 (slope 5). -/
example : quinticIsSmooth.linearityModulus 5 = 25 := by decide

/-- sextic (x⁶) at depth 5: modulus = 30 (slope 6). -/
example : sexticIsSmooth.linearityModulus 5 = 30 := by decide

/-- septic (x⁷) at depth 5: modulus = 35 (slope 7). -/
example : septicIsSmooth.linearityModulus 5 = 35 := by decide

/-- octic (x⁸) at depth 5: modulus = 40 (slope 8). -/
example : octicIsSmooth.linearityModulus 5 = 40 := by decide

/-! ### P3: composeIsSmooth modulus = product of degrees -/

/-- compose square ∘ square : x ↦ (x²)² = x⁴.
    Modulus 5 = 20 = 4 × 5 (degrees compose multiplicatively). -/
example :
    (composeIsSmooth squareIsSmooth squareIsSmooth).linearityModulus 5 = 20
    := by decide

/-- compose square ∘ cube: x ↦ (x²)³ = x⁶.
    Modulus 5 = 30 = 6 × 5. -/
example :
    (composeIsSmooth squareIsSmooth cubeIsSmooth).linearityModulus 5 = 30
    := by decide

/-- compose id ∘ square: still gives modulus 10 (degree 2 effectively). -/
example :
    (composeIsSmooth idIsSmooth squareIsSmooth).linearityModulus 5 = 10
    := by decide

/-- compose square ∘ quartic: x ↦ (x²)⁴ = x⁸. Modulus 40 (degree 8). -/
example :
    (composeIsSmooth squareIsSmooth quarticIsSmooth).linearityModulus 5 = 40
    := by decide

/-! ### P4: midIsSmooth modulus computations -/

/-- midIsSmooth on (id, id): x ↦ midpoint(x, x) ≈ x.  Modulus = max(id, id) = id. -/
example : (midIsSmooth idIsSmooth idIsSmooth).linearityModulus 5 = 5 := by decide

/-- midIsSmooth on (id, square): mixed.  Modulus = max(n, 2n) = 2n. -/
example : (midIsSmooth idIsSmooth squareIsSmooth).linearityModulus 5 = 10 := by decide

/-- midIsSmooth on (square, cube): mixed.  Modulus = max(2n, 3n) = 3n. -/
example : (midIsSmooth squareIsSmooth cubeIsSmooth).linearityModulus 5 = 15 := by decide

/-- midIsSmooth on (quartic, octic): degree 4 + 8 mixed. Modulus = max(20, 40) = 40. -/
example : (midIsSmooth quarticIsSmooth octicIsSmooth).linearityModulus 5 = 40 := by decide

/-! ### Q1: addIsSmooth modulus = max behavior (linear) -/

/-- addIsSmooth (id, id): max(5, 5) = 5. -/
example : (addIsSmooth idIsSmooth idIsSmooth).linearityModulus 5 = 5 := by decide

/-- addIsSmooth (id, square): max(5, 10) = 10. -/
example : (addIsSmooth idIsSmooth squareIsSmooth).linearityModulus 5 = 10 := by decide

/-- addIsSmooth (square, cube): max(10, 15) = 15. -/
example : (addIsSmooth squareIsSmooth cubeIsSmooth).linearityModulus 5 = 15 := by decide

/-- addIsSmooth (cube, septic): max(15, 35) = 35. -/
example : (addIsSmooth cubeIsSmooth septicIsSmooth).linearityModulus 5 = 35 := by decide

/-! ### Q2: mulIsSmooth modulus = sum behavior (compounding) -/

/-- mulIsSmooth (id, id): id + id = 5 + 5 = 10. -/
example : (mulIsSmooth idIsSmooth idIsSmooth).linearityModulus 5 = 10 := by decide

/-- mulIsSmooth (id, square): id + square = 5 + 10 = 15. -/
example : (mulIsSmooth idIsSmooth squareIsSmooth).linearityModulus 5 = 15 := by decide

/-- mulIsSmooth (square, cube): square + cube = 10 + 15 = 25 (degree 5). -/
example : (mulIsSmooth squareIsSmooth cubeIsSmooth).linearityModulus 5 = 25 := by decide

/-- mulIsSmooth (cube, septic): cube + septic = 15 + 35 = 50 (degree 10). -/
example : (mulIsSmooth cubeIsSmooth septicIsSmooth).linearityModulus 5 = 50 := by decide

/-! ### Q3: 3-way composition tests -/

/-- compose (compose square square) square: x ↦ ((x²)²)² = x⁸. Modulus 40. -/
example :
    (composeIsSmooth (composeIsSmooth squareIsSmooth squareIsSmooth) squareIsSmooth).linearityModulus 5 = 40
    := by decide

/-- compose square (compose square square): x ↦ (x²)^4 = x⁸. Modulus 40. -/
example :
    (composeIsSmooth squareIsSmooth (composeIsSmooth squareIsSmooth squareIsSmooth)).linearityModulus 5 = 40
    := by decide

/-! ### R1: x¹⁰ and x¹⁶ moduli -/

/-- decic (x¹⁰) at depth 5: modulus = 50. -/
example : decicIsSmooth.linearityModulus 5 = 50 := by decide

/-- hexadecic (x¹⁶) at depth 5: modulus = 80. -/
example : hexadecicIsSmooth.linearityModulus 5 = 80 := by decide

/-- nonic (x⁹) at depth 5: modulus = 45 (slope 9). -/
example : nonicIsSmooth.linearityModulus 5 = 45 := by decide

/-- twelfth (x¹²) at depth 5: modulus = 60 (slope 12). -/
example : twelfthIsSmooth.linearityModulus 5 = 60 := by decide

/-- fifteenth (x¹⁵) at depth 5: modulus = 75 (slope 15). -/
example : fifteenthIsSmooth.linearityModulus 5 = 75 := by decide

/-- eleventh (x¹¹) at depth 5: modulus = 55 (slope 11). -/
example : eleventhIsSmooth.linearityModulus 5 = 55 := by decide

/-- thirteenth (x¹³) at depth 5: modulus = 65 (slope 13). -/
example : thirteenthIsSmooth.linearityModulus 5 = 65 := by decide

/-- fourteenth (x¹⁴) at depth 5: modulus = 70 (slope 14). -/
example : fourteenthIsSmooth.linearityModulus 5 = 70 := by decide

/-! ### W1: Polynomial coverage capstone for degrees 1-16 -/

/-- **Polynomial chain coverage 1-16**: 16-fact bundle showing
    every integer degree 1-16 has an IsSmooth instance with modulus
    at depth 5 = 5 × degree. -/
theorem polynomial_coverage_1_to_16 :
    idIsSmooth.linearityModulus 5 = 5
    ∧ squareIsSmooth.linearityModulus 5 = 10
    ∧ cubeIsSmooth.linearityModulus 5 = 15
    ∧ quarticIsSmooth.linearityModulus 5 = 20
    ∧ quinticIsSmooth.linearityModulus 5 = 25
    ∧ sexticIsSmooth.linearityModulus 5 = 30
    ∧ septicIsSmooth.linearityModulus 5 = 35
    ∧ octicIsSmooth.linearityModulus 5 = 40
    ∧ nonicIsSmooth.linearityModulus 5 = 45
    ∧ decicIsSmooth.linearityModulus 5 = 50
    ∧ eleventhIsSmooth.linearityModulus 5 = 55
    ∧ twelfthIsSmooth.linearityModulus 5 = 60
    ∧ thirteenthIsSmooth.linearityModulus 5 = 65
    ∧ fourteenthIsSmooth.linearityModulus 5 = 70
    ∧ fifteenthIsSmooth.linearityModulus 5 = 75
    ∧ hexadecicIsSmooth.linearityModulus 5 = 80 := by decide

/-! ### T3: Generic polynomial modulus theorems for x⁵-x⁸ -/

/-- **x⁵ generic modulus**: linearityModulus n = 5 * n (slope 5). -/
theorem quinticIsSmooth_modulus (n : Nat) :
    quinticIsSmooth.linearityModulus n = 5 * n := by
  show squareIsSmooth.linearityModulus n + cubeIsSmooth.linearityModulus n
       = 5 * n
  rw [squareIsSmooth_modulus, cubeIsSmooth_modulus]; omega

/-- **x⁶ generic modulus**: linearityModulus n = 6 * n (slope 6). -/
theorem sexticIsSmooth_modulus (n : Nat) :
    sexticIsSmooth.linearityModulus n = 6 * n := by
  show cubeIsSmooth.linearityModulus n + cubeIsSmooth.linearityModulus n
       = 6 * n
  rw [cubeIsSmooth_modulus]; omega

/-- **x⁷ generic modulus**: linearityModulus n = 7 * n (slope 7). -/
theorem septicIsSmooth_modulus (n : Nat) :
    septicIsSmooth.linearityModulus n = 7 * n := by
  show cubeIsSmooth.linearityModulus n + quarticIsSmooth.linearityModulus n
       = 7 * n
  rw [cubeIsSmooth_modulus, quarticIsSmooth_modulus]; omega

/-- **x⁸ generic modulus**: linearityModulus n = 8 * n (slope 8). -/
theorem octicIsSmooth_modulus (n : Nat) :
    octicIsSmooth.linearityModulus n = 8 * n := by
  show quarticIsSmooth.linearityModulus n + quarticIsSmooth.linearityModulus n
       = 8 * n
  rw [quarticIsSmooth_modulus]; omega

/-- **Polynomial slope coverage**: degree → modulus slope explicitly,
    for degrees 1-8.  Capstone of the full polynomial chain. -/
theorem polynomial_slope_coverage (n : Nat) :
    idIsSmooth.linearityModulus n = 1 * n
    ∧ squareIsSmooth.linearityModulus n = 2 * n
    ∧ cubeIsSmooth.linearityModulus n = 3 * n
    ∧ quarticIsSmooth.linearityModulus n = 4 * n
    ∧ quinticIsSmooth.linearityModulus n = 5 * n
    ∧ sexticIsSmooth.linearityModulus n = 6 * n
    ∧ septicIsSmooth.linearityModulus n = 7 * n
    ∧ octicIsSmooth.linearityModulus n = 8 * n := by
  refine ⟨?_, squareIsSmooth_modulus n, cubeIsSmooth_modulus n,
          quarticIsSmooth_modulus n, quinticIsSmooth_modulus n,
          sexticIsSmooth_modulus n, septicIsSmooth_modulus n,
          octicIsSmooth_modulus n⟩
  rw [Nat.one_mul]; exact idIsSmooth_modulus n

end E213.Research.Real213CutSum
