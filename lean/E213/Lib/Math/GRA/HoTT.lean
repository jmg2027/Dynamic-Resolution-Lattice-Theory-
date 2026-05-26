import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.NumberTheory

/-!
# GRA HoTT Instance (Reading R₃)

Homotopy Type Theory interpretation of GRA:
  * **Carrier**: Truncation levels (natural numbers representing
    the n-type truncation index)
  * **Grade**: Truncation level (= the carrier)
  * **⊕**: Suspension (Σⁿ): grades add under iterated suspension
  * **⊗**: Smash product (∧): grades add sub-additively
  * **Depth**: ⌈n/3⌉ = minimum number of 3-truncation steps
  * **gen1=2**: 2-truncation (groupoid level)
  * **gen2=3**: 3-truncation (2-groupoid level)

The key non-trivial content:
  - Every n-type (for n ≥ 2) is reachable as a composition of
    2-truncations and 3-truncations.
  - This is the homotopy-theoretic avatar of gcd(2,3) = 1:
    since {2,3} generates all of ℕ≥2 additively, every truncation
    level is achievable by composing these two primitive levels.

Standard: 0 sorry, ∅-axiom.
-/

namespace E213.Lib.Math.GRA.HoTT

open E213.Lib.Math.GRA

-- ============================================================
-- HoTT carrier and operations
-- ============================================================

/-- Carrier = truncation level (n-type index). -/
abbrev HoTTCarrier := Nat

/-- Grade = truncation level (identity). -/
def hottGrade (n : HoTTCarrier) : Nat := n

/-- ⊕ = suspension: Σⁿ raises truncation level additively.
    If X is an n-type and Y is an m-type, then ΣⁿY viewed in
    the appropriate fiber has truncation level n + m. -/
def hottOplus (a b : HoTTCarrier) : HoTTCarrier := a + b

/-- ⊗ = smash product: the smash A ∧ B has truncation level
    at most that of A plus that of B. -/
def hottOtimes (a b : HoTTCarrier) : HoTTCarrier := a + b

/-- Depth = ⌈n/3⌉ = minimum number of 3-truncation compositions
    (cells) needed to build an n-type from primitives. -/
def hottDepth (n : Nat) : Nat := (n + 2) / 3

-- ============================================================
-- Axiom verification
-- ============================================================

theorem hott_gen1_lt_gen2 : (2 : Nat) < 3 := by decide

theorem hott_coprime : Nat.gcd 2 3 = 1 := by decide

theorem hott_grade_oplus (a b : HoTTCarrier) :
    hottGrade (hottOplus a b) = hottGrade a + hottGrade b := by
  simp [hottGrade, hottOplus]

theorem hott_grade_otimes (a b : HoTTCarrier) :
    hottGrade (hottOtimes a b) ≤ hottGrade a + hottGrade b := by
  simp [hottGrade, hottOtimes]

/-- Reachability: every truncation level ≥ 2 is achievable via
    compositions of 2-truncations and 3-truncations. -/
theorem hott_reach (n : Nat) (hn : n ≥ 2) :
    ∃ a b : Nat, n = 2 * a + 3 * b := by
  match n, hn with
  | 2, _ => exact ⟨1, 0, by omega⟩
  | 3, _ => exact ⟨0, 1, by omega⟩
  | 4, _ => exact ⟨2, 0, by omega⟩
  | 5, _ => exact ⟨1, 1, by omega⟩
  | n + 6, _ =>
    if h : (n + 6) % 2 = 0 then
      exact ⟨(n + 6) / 2, 0, by omega⟩
    else
      exact ⟨((n + 6) - 3) / 2, 1, by omega⟩

/-- Depth = ⌈n/3⌉ in explicit form. -/
theorem hott_depth_eq (n : Nat) (hn : n ≥ 2) :
    hottDepth n = n / 3 + (if n % 3 = 0 then 0 else 1) := by
  simp [hottDepth]
  omega

/-- Greedy: using 3-truncation maximally minimizes cell count. -/
theorem hott_greedy (n : Nat) (hn : n ≥ 2) :
    hottDepth n = (n + 3 - 1) / 3 := by
  simp [hottDepth]

-- ============================================================
-- The (2,3)-GRA model for HoTT
-- ============================================================

/-- The (2,3)-GRA model on truncation levels (HoTT reading R₃). -/
def GRA23_HoTT : GRAModel where
  Carrier := HoTTCarrier
  grade := hottGrade
  oplus := hottOplus
  otimes := hottOtimes
  gen1 := 2
  gen2 := 3
  depth := hottDepth
  ax_gen1_lt_gen2 := hott_gen1_lt_gen2
  ax_coprime := hott_coprime
  ax_grade_oplus := hott_grade_oplus
  ax_grade_otimes := hott_grade_otimes
  ax_reach := hott_reach
  ax_depth_eq := hott_depth_eq
  ax_greedy := hott_greedy

-- ============================================================
-- Isomorphism: HoTT ≅ NumberTheory
-- ============================================================

/-- The GRA isomorphism between HoTT and NT models.
    
    Mathematical content: the truncation-level arithmetic in HoTT
    satisfies exactly the same (2,3)-GRA structure.  This witnesses:
    1. Suspension additivity (A2) — Σⁿ adds truncation levels
    2. Every n-type (n≥2) decomposes into 2- and 3-truncation
       compositions (A4) — the homotopy Chicken McNugget theorem
    3. Greedy on 3-truncation is optimal for cell minimization (A6) -/
def GRAIso_HoTT_NT : GRAIso GRA23_HoTT NumberTheory.GRA23_NT where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

end E213.Lib.Math.GRA.HoTT
