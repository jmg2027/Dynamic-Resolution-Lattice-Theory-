import E213.Meta.Nat.Gcd213

/-!
# GRA Model — Typeclass for Graded Residue Arithmetic instances

A `GRAModel` encodes the 7 axioms of Graded Residue Arithmetic (GRA)
as a Lean typeclass.  Any structure satisfying these axioms is a
"(g₁,g₂)-GRA model."

The GRA Universality Conjecture states that 5 different mathematical
domains (Number Theory, Graph Theory, Cohomology, HoTT, Higher Algebra,
Analysis) each admit a (2,3)-GRA model, and these models are pairwise
isomorphic in the GRA-model category.

This file defines:
  * `GRAModel` — the 7-axiom typeclass
  * `GRAIso` — isomorphism between two GRA models
  * Basic derived lemmas

Standard: 0 sorry, ∅-axiom (PURE).  Uses `E213.Tactic.NatHelper.gcd213`
rather than Lean-core `Nat.gcd` to avoid the well-founded-recursion
`propext` inheritance.
-/

namespace E213.Lib.Math.Algebra.GRA

open E213.Tactic.NatHelper (gcd213)

/-- A GRA model: a graded structure with two coprime generators
    satisfying the 7 GRA axioms. -/
structure GRAModel where
  /-- The carrier type of graded elements -/
  Carrier : Type
  /-- Grade function: assigns a natural number grade to each element -/
  grade : Carrier → Nat
  /-- Binary operation ⊕ (grade-additive combination) -/
  oplus : Carrier → Carrier → Carrier
  /-- Binary operation ⊗ (grade-subadditive composition) -/
  otimes : Carrier → Carrier → Carrier
  /-- First generator grade -/
  gen1 : Nat
  /-- Second generator grade -/
  gen2 : Nat
  /-- Depth function: minimum decomposition steps -/
  depth : Nat → Nat

  -- A1: Generator axiom — exactly two primitive grades, coprime
  ax_gen1_lt_gen2 : gen1 < gen2
  ax_coprime : gcd213 gen1 gen2 = 1

  -- A2: Grade addition — ⊕ is exactly grade-additive
  ax_grade_oplus : ∀ a b : Carrier, grade (oplus a b) = grade a + grade b

  -- A3: Grade composition — ⊗ is at most grade-additive
  ax_grade_otimes : ∀ a b : Carrier, grade (otimes a b) ≤ grade a + grade b

  -- A4: Universal reachability — every n ≥ gen1 is representable
  ax_reach : ∀ n : Nat, n ≥ gen1 →
    ∃ a b : Nat, n = gen1 * a + gen2 * b

  -- A5: Depth uniqueness — depth is the minimal sum a+b
  ax_depth_eq : ∀ n : Nat, n ≥ gen1 →
    depth n = Nat.div n gen2 + (if n % gen2 = 0 then 0 else 1)
    -- Simplified: depth is determined by greedy on gen2

  -- A6: Greedy optimality — using gen2 maximally is always optimal
  ax_greedy : ∀ n : Nat, n ≥ gen1 →
    depth n = (n + gen2 - 1) / gen2
    -- = ⌈n / gen2⌉

/-- The standard (2,3)-GRA parameters. -/
def GRA23_gen1 : Nat := 2
def GRA23_gen2 : Nat := 3

/-- A (2,3)-GRA model is a GRAModel with gen1=2, gen2=3. -/
structure GRA23Model extends GRAModel where
  ax_gen1_is_2 : toGRAModel.gen1 = 2
  ax_gen2_is_3 : toGRAModel.gen2 = 3

/-- Isomorphism between two GRA models: a grade-preserving bijection
    that commutes with ⊕ and ⊗. -/
structure GRAIso (M₁ M₂ : GRAModel) where
  /-- Forward map -/
  toFun : M₁.Carrier → M₂.Carrier
  /-- Inverse map -/
  invFun : M₂.Carrier → M₁.Carrier
  /-- Left inverse -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- Right inverse -/
  right_inv : ∀ y, toFun (invFun y) = y
  /-- Grade preservation -/
  grade_comm : ∀ x, M₂.grade (toFun x) = M₁.grade x
  /-- Commutes with ⊕ -/
  oplus_comm : ∀ x y, toFun (M₁.oplus x y) = M₂.oplus (toFun x) (toFun y)
  /-- Commutes with ⊗ -/
  otimes_comm : ∀ x y, toFun (M₁.otimes x y) = M₂.otimes (toFun x) (toFun y)

-- ============================================================
-- Derived lemmas
-- ============================================================

/-- GRA iso is reflexive. -/
def GRAIso.refl (M : GRAModel) : GRAIso M M where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-- GRA iso is symmetric. -/
def GRAIso.symm {M₁ M₂ : GRAModel} (iso : GRAIso M₁ M₂) : GRAIso M₂ M₁ where
  toFun := iso.invFun
  invFun := iso.toFun
  left_inv := iso.right_inv
  right_inv := iso.left_inv
  grade_comm := fun y => by
    have h := iso.grade_comm (iso.invFun y)
    rw [iso.right_inv] at h
    exact h.symm
  oplus_comm := fun x y => by
    -- Goal: iso.invFun (M₂.oplus x y) = M₁.oplus (iso.invFun x) (iso.invFun y)
    -- Strategy: apply iso.invFun to both sides of iso.oplus_comm
    have h := iso.oplus_comm (iso.invFun x) (iso.invFun y)
    -- h : iso.toFun (M₁.oplus (iso.invFun x) (iso.invFun y))
    --   = M₂.oplus (iso.toFun (iso.invFun x)) (iso.toFun (iso.invFun y))
    rw [iso.right_inv x, iso.right_inv y] at h
    -- h : iso.toFun (M₁.oplus (iso.invFun x) (iso.invFun y)) = M₂.oplus x y
    have h2 := congrArg iso.invFun h.symm
    -- h2 : iso.invFun (M₂.oplus x y) = iso.invFun (iso.toFun (M₁.oplus ...))
    rw [iso.left_inv] at h2
    exact h2
  otimes_comm := fun x y => by
    have h := iso.otimes_comm (iso.invFun x) (iso.invFun y)
    rw [iso.right_inv x, iso.right_inv y] at h
    have h2 := congrArg iso.invFun h.symm
    rw [iso.left_inv] at h2
    exact h2

/-- GRA iso is transitive. -/
def GRAIso.trans {M₁ M₂ M₃ : GRAModel}
    (iso₁₂ : GRAIso M₁ M₂) (iso₂₃ : GRAIso M₂ M₃) : GRAIso M₁ M₃ where
  toFun := iso₂₃.toFun ∘ iso₁₂.toFun
  invFun := iso₁₂.invFun ∘ iso₂₃.invFun
  left_inv := fun x => by simp [Function.comp]; rw [iso₂₃.left_inv, iso₁₂.left_inv]
  right_inv := fun y => by simp [Function.comp]; rw [iso₁₂.right_inv, iso₂₃.right_inv]
  grade_comm := fun x => by
    simp [Function.comp]
    rw [iso₂₃.grade_comm, iso₁₂.grade_comm]
  oplus_comm := fun x y => by
    simp [Function.comp]
    rw [iso₁₂.oplus_comm, iso₂₃.oplus_comm]
  otimes_comm := fun x y => by
    simp [Function.comp]
    rw [iso₁₂.otimes_comm, iso₂₃.otimes_comm]

end E213.Lib.Math.Algebra.GRA
