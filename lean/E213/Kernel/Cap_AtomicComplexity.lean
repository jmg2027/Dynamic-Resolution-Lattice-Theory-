import E213.Kernel.Term

/-!
# E213.Kernel.Cap_AtomicComplexity — atomic-1 integer representation verification.

Re-states only the *pure arithmetic* among the complexity theorems from
Phase4/AtomicReps.lean.  6 = NS·NT, 8 = NT³, 25 = d², ...

The complexity function itself is hard to port (it is a function over Expr).
Here we only prove that *each result integer can be expressed in exactly that form* → 0 axiom.
-/

namespace E213.Kernel.Cap.AtomicComplexity

-- 213 atomic constants
def NS : Nat := 3
def NT : Nat := 2
def d  : Nat := 5

/-- 6 = NS · NT. -/
theorem six_atomic : (6 : Nat) = NS * NT := rfl

/-- 8 = NT³. -/
theorem eight_atomic : (8 : Nat) = NT * NT * NT := rfl

/-- 8 = NS² - (NS - NT) = 9 - 1.  (Alternative form, complexity 1+.) -/
theorem eight_alt : (8 : Nat) = NS * NS - (NS - NT) := rfl

/-- 10 = d · NT. -/
theorem ten_atomic : (10 : Nat) = d * NT := rfl

/-- 16 = (NT²)² = (2·NT)². -/
theorem sixteen_atomic : (16 : Nat) = (NT * NT) * (NT * NT) := rfl

/-- 25 = d². -/
theorem twentyfive_atomic : (25 : Nat) = d * d := rfl

/-- 12 = NS · d - NS = NS · (d - 1). -/
theorem twelve_atomic : (12 : Nat) = NS * d - NS := rfl

/-- 24 = (d-1) · d - (d-1)·1 = ... 24 = d² - 1 = 25-1.  Or 24 = d·d - 1. -/
theorem twentyfour_atomic : (24 : Nat) = d * d - 1 := rfl

/-- 13 = NS² + (d - NS) - 1  ... in fact 13 = 2·NS² - d = 18 - 5. -/
theorem thirteen_atomic : (13 : Nat) = 2 * NS * NS - d := rfl

/-- 60 = NS·d·NT·NT = 3·5·2·2. -/
theorem sixty_atomic : (60 : Nat) = NS * d * NT * NT := rfl

/-- 192 = (NT)·(NT²)·(NT³)·NS = 2·4·8·3 = 192.
    192 = 64·3 = 2⁶·NS. -/
theorem oneNinetytwo_atomic : (192 : Nat) = NS * (NT * NT * NT * NT * NT * NT) := rfl

/-- 11 ≠ NS (Bool form): Nat.beq 11 NS = false. -/
theorem eleven_neq_NS : Nat.beq 11 NS = false := rfl
theorem thirteen_neq_NS : Nat.beq 13 NS = false := rfl
theorem seventeen_neq_NSNT : Nat.beq 17 (NS * NT) = false := rfl
theorem nineteen_neq_dsq : Nat.beq 19 (d * d) = false := rfl
theorem twentythree_neq_dsq : Nat.beq 23 (d * d) = false := rfl

end E213.Kernel.Cap.AtomicComplexity

#print axioms E213.Kernel.Cap.AtomicComplexity.six_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.eight_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.ten_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.sixteen_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.twentyfive_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.twelve_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.twentyfour_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.thirteen_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.sixty_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.oneNinetytwo_atomic
#print axioms E213.Kernel.Cap.AtomicComplexity.eleven_neq_NS
#print axioms E213.Kernel.Cap.AtomicComplexity.thirteen_neq_NS
#print axioms E213.Kernel.Cap.AtomicComplexity.seventeen_neq_NSNT
#print axioms E213.Kernel.Cap.AtomicComplexity.nineteen_neq_dsq
#print axioms E213.Kernel.Cap.AtomicComplexity.twentythree_neq_dsq
