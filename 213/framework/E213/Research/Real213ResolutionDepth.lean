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

end E213.Research.Real213CutSum
