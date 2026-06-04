import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.Common

/-!
# GRA Number Theory Instance — The trivial (2,3) model on ℕ

This is the "base" GRA model: the carrier is ℕ itself, grade is the
identity, ⊕ is addition, ⊗ is addition (depth composition).

All 7 axioms are trivially satisfied because GRA was originally
abstracted from this very structure.  This instance serves as the
"hub" for the universality program: every other Reading is shown
isomorphic to this one.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.NumberTheory

open E213.Lib.Math.Algebra.GRA
open E213.Lib.Math.Algebra.GRA.Common
  (coprime_2_3 two_lt_three reach_23 depth_formula greedy_form)

/-- ℕ-carrier for the number theory GRA model. -/
abbrev NTCarrier := Nat

/-- Grade = identity on ℕ. -/
def ntGrade (n : NTCarrier) : Nat := n

/-- ⊕ = addition. -/
def ntOplus (a b : NTCarrier) : NTCarrier := a + b

/-- ⊗ = addition (depth composition adds grades, not multiplies). -/
def ntOtimesCorrect (a b : NTCarrier) : NTCarrier := a + b

/-- Depth = ⌈n/3⌉ (greedy on gen2=3). -/
def ntDepth (n : Nat) : Nat := (n + 2) / 3

-- ============================================================
-- Axiom proofs (all PURE)
-- ============================================================

theorem nt_gen1_lt_gen2 : (2 : Nat) < 3 := two_lt_three

theorem nt_coprime : E213.Tactic.NatHelper.gcd213 2 3 = 1 := coprime_2_3

theorem nt_grade_oplus (a b : NTCarrier) :
    ntGrade (ntOplus a b) = ntGrade a + ntGrade b := rfl

theorem nt_grade_otimes_correct (a b : NTCarrier) :
    ntGrade (ntOtimesCorrect a b) ≤ ntGrade a + ntGrade b := Nat.le.refl

/-- Reachability: ∀ n ≥ 2, ∃ a b, n = 2*a + 3*b. -/
theorem nt_reach (n : Nat) (hn : n ≥ 2) :
    ∃ a b : Nat, n = 2 * a + 3 * b := reach_23 n hn

/-- Greedy depth: ⌈n/3⌉ = (n+2)/3. -/
theorem nt_greedy (n : Nat) (_hn : n ≥ 2) :
    ntDepth n = (n + 3 - 1) / 3 := greedy_form n

/-- Depth formula: depth n = n/3 + (if n%3=0 then 0 else 1) = ⌈n/3⌉. -/
theorem nt_depth_eq (n : Nat) (_hn : n ≥ 2) :
    ntDepth n = n / 3 + (if n % 3 = 0 then 0 else 1) := depth_formula n

/-- The (2,3)-GRA model over ℕ (Number Theory reading). -/
def GRA23_NT : GRAModel where
  Carrier := NTCarrier
  grade := ntGrade
  oplus := ntOplus
  otimes := ntOtimesCorrect
  gen1 := 2
  gen2 := 3
  depth := ntDepth
  ax_gen1_lt_gen2 := nt_gen1_lt_gen2
  ax_coprime := nt_coprime
  ax_grade_oplus := nt_grade_oplus
  ax_grade_otimes := nt_grade_otimes_correct
  ax_reach := nt_reach
  ax_depth_eq := nt_depth_eq
  ax_greedy := nt_greedy

end E213.Lib.Math.Algebra.GRA.NumberTheory
