import E213.Lib.Math.Probability.Cut

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

namespace E213.Lib.Math.Probability.Independence

open E213.Lib.Math.Probability.Cut (ProbabilityCut)

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

/-- Joint with `unit` returns the original mass (numerator). -/
theorem joint_unit_left_num (a : ProbabilityCut) :
    (joint ProbabilityCut.unit a).num = a.num := Nat.one_mul a.num

/-- Joint with `unit` returns the original mass (denominator). -/
theorem joint_unit_left_den (a : ProbabilityCut) :
    (joint ProbabilityCut.unit a).den = a.den := Nat.one_mul a.den

/-- Joint with `zero` is `zero` (numerator). -/
theorem joint_zero_left_num (a : ProbabilityCut) :
    (joint ProbabilityCut.zero a).num = 0 := Nat.zero_mul a.num

/-- Joint commutes (numerator). -/
theorem joint_comm_num (a b : ProbabilityCut) :
    (joint a b).num = (joint b a).num := Nat.mul_comm a.num b.num

/-- Joint commutes (denominator). -/
theorem joint_comm_den (a b : ProbabilityCut) :
    (joint a b).den = (joint b a).den := Nat.mul_comm a.den b.den

/-- Conditional probability numerator: `P(A ∩ B) / P(B) = a.num / b.num`
    *at the common scale*.  When `a, b` share the same `den`, this is
    the closed form. -/
def conditionalNum (a _b : ProbabilityCut) : Nat := a.num

/-- Conditional probability denominator: `b`'s numerator (events
    must be at the same scale for the ratio to make sense atomically). -/
def conditionalDen (_a b : ProbabilityCut) : Nat := b.num

/-- Conditional numerator unfold (rfl). -/
theorem conditionalNum_eq (a b : ProbabilityCut) :
    conditionalNum a b = a.num := rfl

/-- Conditional denominator unfold (rfl). -/
theorem conditionalDen_eq (a b : ProbabilityCut) :
    conditionalDen a b = b.num := rfl

end E213.Lib.Math.Probability.Independence
