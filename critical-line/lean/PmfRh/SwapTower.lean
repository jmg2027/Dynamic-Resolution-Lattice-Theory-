/-
  PmfRh/SwapTower.lean

  SWAP TOWER — OPERADIC IDEMPOTENCE
  ==================================

  Extends SwapAnnihilation.lean (pairwise σ, 1-level) to the
  recursive tower:
    T(x) := simplex-at-each-vertex reduction on alive dimensions.

  User intuition (Mingu Jeong, 2026-04-18):
    "N점 → N심플렉스 → 각 꼭지점에 또 심플렉스 → ..."

  Theorems (0 sorry):
    base_dim_five          :  base (1,1) has dim 5
    tower_fixed_five       :  T(base) = 5
    alive_ge_five          :  every alive d ≥ 5
    unique_five_decomp     :  alive d = 5 ⇒ (a,b) = (1,1)
    tower_le_dim_succ      :  T(x) ≤ dim(x) + 1  (near non-increasing)
    tower_ge_five          :  T(x) ≥ 5
    tower_eq_five_at_five  :  dim(x) = 5 ⇒ T(x) = 5  (absorbing)
    pairwise_is_tower      :  T(x) = dIndep(x.a, x.b)  (FND_012 match)
    base_is_fixed          :  towerStep base = base.dim  (base is fixed pt)

  Pairwise σ (SwapAnnihilation.lean) is literally T restricted
  to 1 level.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import PmfRh.ChiralChannels
import PmfRh.SwapAnnihilation

set_option autoImplicit false

namespace DRLT.Foundation.SwapTower

/-! ## 1. Alive dimensions -/

/-- A live simplex dimension: d = 2a + 3b with BOTH atoms present
    (a ≥ 1 ∧ b ≥ 1).  Matches FND_012 "alive" condition. -/
structure AliveDim where
  a : Nat
  b : Nat
  ha : 1 ≤ a
  hb : 1 ≤ b

@[simp] def AliveDim.dim (x : AliveDim) : Nat := 2 * x.a + 3 * x.b

/-- Base: one of each atom ⇒ (3,2) atomic pair ⇒ d = 5. -/
def baseAlive : AliveDim where
  a := 1
  b := 1
  ha := Nat.le_refl 1
  hb := Nat.le_refl 1

theorem base_dim_five : baseAlive.dim = 5 := rfl

/-! ## 2. Tower step (swap reduction) -/

/-- One-level swap reduction = dim of σ+1 eigenspace (FND_012):
      d_indep(a, b) = 2⌈a/2⌉ + 3⌈b/2⌉
    In Nat: ⌈n/2⌉ = (n + 1) / 2. -/
def towerStep (x : AliveDim) : Nat :=
  2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2)

/-- Pairwise-σ d_indep (FND_012) as a pure Nat function. -/
def dIndep (a b : Nat) : Nat :=
  2 * ((a + 1) / 2) + 3 * ((b + 1) / 2)

/-- SwapTower's towerStep agrees with FND_012's d_indep. -/
theorem pairwise_is_tower (x : AliveDim) :
    towerStep x = dIndep x.a x.b := rfl

/-! ## 3. Fixed point at d = 5 -/

theorem tower_fixed_five : towerStep baseAlive = 5 := rfl

/-! ## 4. Alive dimension ≥ 5 -/

theorem alive_ge_five (x : AliveDim) : 5 ≤ x.dim := by
  have := x.ha; have := x.hb
  show 5 ≤ 2 * x.a + 3 * x.b
  omega

/-! ## 5. Uniqueness of (1,1) as alive decomposition of 5 -/

theorem unique_five_decomp (x : AliveDim) (h : x.dim = 5) :
    x.a = 1 ∧ x.b = 1 := by
  have := x.ha; have := x.hb
  have hdim : 2 * x.a + 3 * x.b = 5 := h
  omega

/-! ## 6. Absorption: dim = 5 ⇒ T = 5 -/

theorem tower_eq_five_at_five (x : AliveDim) (h : x.dim = 5) :
    towerStep x = 5 := by
  obtain ⟨ha, hb⟩ := unique_five_decomp x h
  show 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2) = 5
  rw [ha, hb]

/-! ## 7. Non-increasing (up to +1): T(x) ≤ dim(x) + 1 -/

/-- Auxiliary: 2 * ((a + 1) / 2) ≤ 2 * a + 1. -/
private theorem aux_a (a : Nat) : 2 * ((a + 1) / 2) ≤ 2 * a + 1 := by
  omega

/-- Auxiliary: 3 * ((b + 1) / 2) ≤ 3 * b  for b ≥ 1. -/
private theorem aux_b (b : Nat) (hb : 1 ≤ b) : 3 * ((b + 1) / 2) ≤ 3 * b := by
  omega

/-- Tower is near non-increasing: T(x) ≤ dim(x) + 1.
    The +1 comes from the 2-block ceiling when a is odd. -/
theorem tower_le_dim_succ (x : AliveDim) : towerStep x ≤ x.dim + 1 := by
  have h1 := aux_a x.a
  have h2 := aux_b x.b x.hb
  show 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2) ≤ 2 * x.a + 3 * x.b + 1
  omega

/-! ## 8. Lower bound: T(x) ≥ 5 -/

/-- For a ≥ 1: 2 * ((a + 1) / 2) ≥ 2. -/
private theorem aux_lo_a (a : Nat) (ha : 1 ≤ a) :
    2 ≤ 2 * ((a + 1) / 2) := by
  omega

/-- For b ≥ 1: 3 * ((b + 1) / 2) ≥ 3. -/
private theorem aux_lo_b (b : Nat) (hb : 1 ≤ b) :
    3 ≤ 3 * ((b + 1) / 2) := by
  omega

/-- T(x) ≥ 5 on alive dimensions (alive sector is closed under T). -/
theorem tower_ge_five (x : AliveDim) : 5 ≤ towerStep x := by
  have h1 := aux_lo_a x.a x.ha
  have h2 := aux_lo_b x.b x.hb
  show 5 ≤ 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2)
  omega

/-! ## 9. Fixed point characterization -/

/-- IsFixed: towerStep x equals the dimension. -/
def IsFixed (x : AliveDim) : Prop := towerStep x = x.dim

/-- Base (1,1) is a fixed point of T. -/
theorem base_is_fixed : IsFixed baseAlive := by
  show towerStep baseAlive = baseAlive.dim
  rfl

/-- Main theorem: every alive fixed point has dim = 5.
    Uses the fact (n+1)/2 ≤ n with equality iff n ≤ 1. -/
theorem fixed_implies_five (x : AliveDim) (h : IsFixed x) : x.dim = 5 := by
  have ha := x.ha
  have hb := x.hb
  unfold IsFixed at h
  have hstep : towerStep x = 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2) := rfl
  have hdim : x.dim = 2 * x.a + 3 * x.b := rfl
  rw [hstep, hdim] at h
  -- Equation: 2⌈a/2⌉ + 3⌈b/2⌉ = 2a + 3b, with a,b ≥ 1.
  -- Both ⌈n/2⌉ ≤ n+1 and ≥ ⌈1/2⌉ = 1.  Equality forces small cases.
  -- We need a = 1 and b = 1.
  show x.dim = 5
  rw [hdim]
  omega

/-- Corollary: base is (up to the alive constraint) the unique
    fixed point (in the sense that its dim is uniquely 5). -/
theorem fixed_point_unique_dim (x y : AliveDim)
    (hx : IsFixed x) (hy : IsFixed y) : x.dim = y.dim := by
  rw [fixed_implies_five x hx, fixed_implies_five y hy]

/-! ## 10. Strict decrease off the fixed point (OT-2) -/

/-- Off the fixed point, tower STRICTLY decreases.
    This is the monad-idempotence content of T: iterations
    cannot stall; every orbit terminates at the fixed point
    after finitely many steps. -/
theorem tower_strict_off_five (x : AliveDim) (h : 5 < x.dim) :
    towerStep x < x.dim := by
  have := x.ha; have := x.hb
  have hdim : x.dim = 2 * x.a + 3 * x.b := rfl
  rw [hdim] at h
  show 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2) < 2 * x.a + 3 * x.b
  omega

/-- IsFixed x ⟺ x.dim = 5  (full characterization of fixed points). -/
theorem fixed_iff_five (x : AliveDim) : IsFixed x ↔ x.dim = 5 := by
  constructor
  · exact fixed_implies_five x
  · intro h
    unfold IsFixed
    rw [tower_eq_five_at_five x h, h]

/-- Tower is non-increasing, with equality exactly at the fixed
    point: T(x) ≤ dim(x), and T(x) = dim(x) ↔ dim(x) = 5. -/
theorem tower_decreases_to_five (x : AliveDim) :
    towerStep x ≤ x.dim ∧ (towerStep x = x.dim ↔ x.dim = 5) := by
  have h5 : 5 ≤ x.dim := alive_ge_five x
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge 5 x.dim with h | h
    · exact Nat.le_of_lt (tower_strict_off_five x h)
    · have heq : x.dim = 5 := Nat.le_antisymm h h5
      rw [tower_eq_five_at_five x heq, heq]; exact Nat.le_refl 5
  · constructor
    · intro heq
      rcases Nat.lt_or_ge 5 x.dim with h | h
      · exact absurd heq (Nat.ne_of_lt (tower_strict_off_five x h))
      · exact Nat.le_antisymm h h5
    · intro heq
      rw [tower_eq_five_at_five x heq, heq]

/-! ## 11. Dead sector (OT-4) -/

/-- A DEAD simplex dimension: one atom is missing (a = 0 or b = 0),
    so no chiral (both-atoms) decomposition exists.  This is the
    FND_012 "dead" branch (no alive (3,2) pair). -/
structure DeadDim where
  a : Nat
  b : Nat
  missing : a = 0 ∨ b = 0
  nontrivial : 1 ≤ a + b

@[simp] def DeadDim.dim (x : DeadDim) : Nat := 2 * x.a + 3 * x.b

/-- Same d_indep formula, restricted to dead sector. -/
def deadTowerStep (x : DeadDim) : Nat :=
  2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2)

/-- A dead dim never has dim = 5 (alive barrier). -/
theorem dead_dim_ne_five (x : DeadDim) : x.dim ≠ 5 := by
  have hm := x.missing
  have hn := x.nontrivial
  show 2 * x.a + 3 * x.b ≠ 5
  rcases hm with ha | hb
  · rw [ha]; omega
  · rw [hb]; omega

/-- Dead sector CLOSED under T: missing atom stays missing. -/
theorem dead_sector_closed (x : DeadDim) :
    (x.a = 0 → deadTowerStep x = 3 * ((x.b + 1) / 2)) ∧
    (x.b = 0 → deadTowerStep x = 2 * ((x.a + 1) / 2)) := by
  refine ⟨?_, ?_⟩
  · intro ha
    show 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2) = 3 * ((x.b + 1) / 2)
    rw [ha]; omega
  · intro hb
    show 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2) = 2 * ((x.a + 1) / 2)
    rw [hb]; omega

/-- Dead tower output is NEVER 5 (so dead ↛ alive). -/
theorem dead_tower_ne_five (x : DeadDim) : deadTowerStep x ≠ 5 := by
  have hm := x.missing
  show 2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2) ≠ 5
  rcases hm with ha | hb
  · rw [ha]; omega
  · rw [hb]; omega

/-- Honest counter-claim: alive and dead dimensions can COINCIDE
    as bare numbers (e.g. alive (a=3, b=1) and dead (a=0, b=3) both
    give dim = 9).  The distinction is STRUCTURAL (which atoms are
    present), not dimensional.  This is why chirality requires the
    (3,2) alive decomposition — the dim value alone is ambiguous
    from v ≥ 6 onward (matches foundation FND's v≥6 ambiguity). -/
theorem alive_dead_dims_can_coincide :
    ∃ (x : AliveDim) (y : DeadDim), x.dim = y.dim := by
  refine ⟨⟨3, 1, ?_, ?_⟩, ⟨0, 3, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · exact Or.inl rfl
  · omega
  · rfl

end DRLT.Foundation.SwapTower
