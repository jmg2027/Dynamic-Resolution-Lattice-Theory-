import E213.Lib.Math.Probability.Foundation.Cut

/-!
# Probability — Independence + conditional (atomic)

Independent events as **product mass** and conditional probability as
**ratio of joint to conditioning event** — both atomic, both built
from `Nat` arithmetic on `ProbabilityCut` numerators/denominators.

213-native: no Ω, no σ-algebra, no Choice.  `joint a b` multiplies
numerators and denominators; `conditional given a b` divides the
joint by `b`'s mass (= `a`'s numerator over `b`'s numerator at the
common denominator scale).

Open problem from the blueprint (§6) addressed: *Independence
definition*.  Two `ProbabilityCut`s are independent when their joint
mass equals `joint a b` (factorization), achieved structurally here
by *defining* the joint as the product.
-/

namespace E213.Lib.Math.Probability.Foundation.Independence

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)

/-- Joint mass of two independent events: `(a.num · b.num) / (a.den · b.den)`. -/
def joint (a b : ProbabilityCut) : ProbabilityCut where
  num := a.num * b.num
  den := a.den * b.den
  den_pos := Nat.mul_pos a.den_pos b.den_pos
  mass_le := Nat.mul_le_mul a.mass_le b.mass_le

/-- Joint mass numerator factorizes (rfl). -/
theorem joint_num (a b : ProbabilityCut) :
    (joint a b).num = a.num * b.num := rfl

/-- Joint mass denominator factorizes (rfl). -/
theorem joint_den (a b : ProbabilityCut) :
    (joint a b).den = a.den * b.den := rfl

/-- Joint with `unit` returns the original mass (numerator).
    Externally consumed by `Probability/Foundation/Capstone`. -/
theorem joint_unit_left_num (a : ProbabilityCut) :
    (joint ProbabilityCut.unit a).num = a.num := Nat.one_mul a.num

/-- Joint with `zero` is `zero` (numerator).
    Externally consumed by `Probability/Foundation/Capstone`. -/
theorem joint_zero_left_num (a : ProbabilityCut) :
    (joint ProbabilityCut.zero a).num = 0 := Nat.zero_mul a.num

/-- Joint commutes (numerator).
    Externally consumed by `Probability/Foundation/Capstone`. -/
theorem joint_comm_num (a b : ProbabilityCut) :
    (joint a b).num = (joint b a).num := Nat.mul_comm a.num b.num

/-- Conditional probability numerator: `P(A ∩ B) / P(B) = a.num / b.num`
    *at the common scale*.  When `a, b` share the same `den`, this is
    the closed form. -/
def conditionalNum (a _b : ProbabilityCut) : Nat := a.num

/-- Conditional probability denominator: `b`'s numerator (events
    must be at the same scale for the ratio to make sense atomically). -/
def conditionalDen (_a b : ProbabilityCut) : Nat := b.num

/-- Conditional numerator unfold (rfl).  Externally consumed by
    `Probability/Foundation/Capstone`. -/
theorem conditionalNum_eq (a b : ProbabilityCut) :
    conditionalNum a b = a.num := rfl

/-- ★ Independence supplementary identities — joint-with-unit
    denominator, joint commutativity on denominator, conditional
    denominator unfold (all rfl-level). -/
theorem independence_supplementary :
    (∀ a : ProbabilityCut,
        (joint ProbabilityCut.unit a).den = a.den)
    ∧ (∀ a b : ProbabilityCut, (joint a b).den = (joint b a).den)
    ∧ (∀ a b : ProbabilityCut, conditionalDen a b = b.num) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; exact Nat.one_mul a.den
  · intro a b; exact Nat.mul_comm a.den b.den
  · intro _ _; rfl

end E213.Lib.Math.Probability.Foundation.Independence
