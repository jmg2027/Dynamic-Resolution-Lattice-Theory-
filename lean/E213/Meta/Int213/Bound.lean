import E213.Meta.Int213.Core

/-!
# Meta.Int213.Bound — PURE Int bound / comparison helpers

Centralised propext-free Int helpers, specifically targeting
bound-style lemmas (≤, <, sq ≤ 1, etc.) that Lean-core handles via
propext-tainted iff machinery.

Key technique: direct `cases h` on `Int.NonNeg` (definitionally
unfolded from `Int.le`).  Since `Int.NonNeg` is an inductive Prop
whose single constructor `mk : ∀ n, NonNeg (ofNat n)` cannot match
`Int.negSucc k`, contradiction is detected automatically via Lean's
constructor injection — no propext needed.

This is the **Int-side companion** to `Meta/Tactic/NatHelper.lean`
and `Meta/Tactic/ListHelper.lean`.  Helpers here were promoted from:

  · `Lib/Math/CayleyDickson/Integer/ZOmegaUnits §5` (diophantine)

per  +  centralisation.  Existing call sites remain
compatible via `@[reducible]` aliases in the original locations.

All theorems below are **PURE**.
-/

namespace E213.Meta.Int213

/-! ## §1.  Bounded-Nat lemmas via Int.NonNeg constructor inversion -/

/-- For any Nat n with `Int.ofNat n ≤ 1`, `n = 0 ∨ n = 1`.
    PURE via direct `cases` on the underlying `Int.NonNeg`. -/
theorem ofNat_int_le_one (n : Nat) (h : (Int.ofNat n : Int) ≤ 1) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => left; rfl
  | 1 => right; rfl
  | _+2 =>
    exfalso
    cases h

/-! ## §2.  Int squared bound -/

/-- For Int x with `x * x ≤ 1`, `x ∈ {-1, 0, 1}`.

    PURE via case-split on Int constructors + `ofNat_int_le_one`.
    Foundation for diophantine bounds on quadratic number rings
    (Eisenstein, Gaussian, Hurwitz units).  Replaces Lean-core
    `Int.sq_le_one`-style chains that import propext via
    `Int.ofNat_le` iff. -/
theorem int_sq_le_one (x : Int) (h : x * x ≤ (1 : Int)) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  match x with
  | Int.ofNat n =>
    have h_nat : Int.ofNat (n * n) ≤ (1 : Int) := h
    rcases ofNat_int_le_one (n * n) h_nat with h_zero | h_one
    · have hn : n = 0 := by
        match n, h_zero with
        | 0, _ => rfl
        | k+1, hk =>
          exfalso
          have h_pos : 1 ≤ (k+1) * (k+1) := by
            have : 1 ≤ k+1 := Nat.succ_le_succ (Nat.zero_le k)
            exact Nat.mul_le_mul this this
          rw [hk] at h_pos
          exact absurd h_pos (by decide)
      rw [hn]; right; left; rfl
    · have hn : n = 1 := by
        match n, h_one with
        | 0, hk => exact absurd hk (by decide)
        | 1, _ => rfl
        | k+2, hk => exact absurd hk (by
            have : 4 ≤ (k+2) * (k+2) := by
              have : 2 ≤ k+2 := Nat.le_add_left _ _
              exact Nat.mul_le_mul this this
            exact absurd (Nat.le_trans this (Nat.le_of_eq hk)) (by decide))
      rw [hn]; right; right; rfl
  | Int.negSucc n =>
    have h_nat : Int.ofNat ((n+1) * (n+1)) ≤ (1 : Int) := h
    rcases ofNat_int_le_one ((n+1) * (n+1)) h_nat with h_zero | h_one
    · exfalso
      have h_pos : 1 ≤ (n+1) * (n+1) := by
        have : 1 ≤ n+1 := Nat.succ_le_succ (Nat.zero_le n)
        exact Nat.mul_le_mul this this
      rw [h_zero] at h_pos
      exact absurd h_pos (by decide)
    · have hn : n = 0 := by
        match n, h_one with
        | 0, _ => rfl
        | k+1, hk => exact absurd hk (by
            have : 4 ≤ (k+2) * (k+2) := by
              have : 2 ≤ k+2 := Nat.le_add_left _ _
              exact Nat.mul_le_mul this this
            exact absurd (Nat.le_trans this (Nat.le_of_eq hk)) (by decide))
      rw [hn]; left; rfl

/-! ## §3.  4·normSq polynomial identity (Eisenstein diophantine bound) -/

/-- (x+y)² = x² + (xy + yx) + y² — FOIL expansion via Int213 ring axioms. -/
private theorem sq_add_int (x y : Int) :
    (x + y) * (x + y) = x*x + (x*y + y*x) + y*y := by
  rw [add_mul, mul_add, mul_add]
  rw [add_assoc (x*x) (x*y) (y*x + y*y), ← add_assoc (x*y) (y*x) (y*y),
      ← add_assoc (x*x) (x*y + y*x) (y*y)]

/-- (x + -y)² = x² + (-(xy) + -(yx)) + y² — same FOIL with sign handling. -/
private theorem sq_sub_int (x y : Int) :
    (x + -y) * (x + -y) = x*x + (-(x*y) + -(y*x)) + y*y := by
  have ha : x * (-y) = -(x*y) := mul_neg x y
  have hb : (-y) * x = -(y*x) := neg_mul y x
  have hc : (-y) * (-y) = y*y := by
    show (-y) * (-y) = y*y
    rw [mul_neg, neg_mul, Int.neg_neg]
  rw [sq_add_int x (-y), ha, hb, hc]

/-- ★★★ **4·normSq ring identity** — the algebraic identity behind
    the diophantine bound on Eisenstein units:

      `(2a − b)² + 3·b² = 4·(a² − ab + b²)`

    Since `(2a − b)² ≥ 0` (always), `4·normSq ≥ 3·b²`, hence when
    `normSq = 1` we get `3·b² ≤ 4`, i.e. `b² ≤ 1`.

    PURE polynomial identity via Int213.Core ring axioms.  Used in
    `ZOmegaUnits.lean §6` for the diophantine completeness
    `∀ u : ZOmega, u.normSq = 1 → u ∈ units6`. -/
theorem four_normSq_ring_identity (a b : Int) :
    (2 * a + -b) * (2 * a + -b) + 3 * (b * b)
    = 4 * (a * a + -(a * b) + b * b) := by
  rw [sq_sub_int (2*a) b]
  have h1 : (2*a) * (2*a) = 4 * (a*a) := by
    show 2 * a * (2 * a) = 4 * (a * a)
    rw [mul_assoc 2 a (2*a), ← mul_assoc a 2 a, mul_comm a 2, mul_assoc 2 a a,
        ← mul_assoc 2 2 (a*a)]
    rfl
  have h2 : (2*a) * b = 2 * (a*b) := mul_assoc 2 a b
  have h3 : b * (2*a) = 2 * (a*b) := by rw [mul_comm b (2*a), mul_assoc]
  rw [h1, h2, h3]
  have h4 : -(2 * (a*b)) + -(2 * (a*b)) = -(4 * (a*b)) := by
    show -(2 * (a*b)) + -(2 * (a*b)) = -(4 * (a*b))
    rw [show (4 : Int) * (a*b) = (2 + 2) * (a*b) from rfl, add_mul, neg_add]
  rw [h4]
  have h5 : b*b + 3*(b*b) = 4*(b*b) := by
    show b*b + 3*(b*b) = 4*(b*b)
    rw [show (4 : Int) * (b*b) = (1 + 3) * (b*b) from rfl, add_mul, Int.one_mul]
  rw [add_assoc (4*(a*a) + -(4*(a*b))) (b*b) (3*(b*b)), h5]
  rw [mul_add, mul_add, mul_neg]

/-! ## §4.  Diophantine helpers — bounds for Eisenstein completeness -/

/-- Int squared is always non-negative.  PURE via `Int.NonNeg.mk`. -/
theorem int_sq_nonneg : ∀ (x : Int), 0 ≤ x * x := by
  intro x
  match x with
  | Int.ofNat n => exact ⟨n * n⟩
  | Int.negSucc n => exact ⟨(n+1) * (n+1)⟩

/-- For Int y with `3*y² ≤ 4`, `y² ≤ 1`.  PURE via case on Int
    constructors + Nat decide-bounded cases. -/
theorem three_sq_le_four_implies (y : Int) (h : 3 * (y * y) ≤ 4) :
    y * y ≤ 1 := by
  match h_y : y with
  | Int.ofNat n =>
    have h_nat : Int.ofNat (3 * (n*n)) ≤ (4 : Int) := h
    match n with
    | 0 => decide
    | 1 => decide
    | k+2 =>
      exfalso
      have h4 : 4 ≤ (k+2) * (k+2) := by
        have hge : 2 ≤ k+2 := Nat.le_add_left _ _
        exact Nat.mul_le_mul hge hge
      have : 12 ≤ 3 * ((k+2) * (k+2)) := Nat.mul_le_mul_left 3 h4
      cases h_nat
  | Int.negSucc n =>
    have h_nat : Int.ofNat (3 * ((n+1)*(n+1))) ≤ (4 : Int) := h
    match n with
    | 0 => decide
    | k+1 =>
      exfalso
      have h4 : 4 ≤ (k+2) * (k+2) := by
        have hge : 2 ≤ k+2 := Nat.le_add_left _ _
        exact Nat.mul_le_mul hge hge
      have : 12 ≤ 3 * ((k+2) * (k+2)) := Nat.mul_le_mul_left 3 h4
      cases h_nat

/-- For Int x, y with `x + y = c` and `0 ≤ x`, `y ≤ c`.  PURE.
    Used to bound `3*y² ≤ 4` from `(2re-im)² + 3*im² = 4` (with
    `(2re-im)² ≥ 0`).  Direct via `Int.NonNeg` def-unfolding. -/
theorem le_of_add_eq_of_nonneg {x y c : Int}
    (h_sum : x + y = c) (h_x : 0 ≤ x) : y ≤ c := by
  -- y ≤ c ↔ Int.NonNeg (c - y).  From c = x + y: c - y = x.
  -- So Int.NonNeg (c - y) = Int.NonNeg x, which is h_x by Int.le defn.
  show Int.NonNeg (c - y)
  rw [← h_sum]
  -- now: NonNeg ((x + y) - y) = NonNeg (x + y + -y) = NonNeg (x + (y + -y)) = NonNeg (x + 0)
  show Int.NonNeg (x + y + -y)
  rw [add_assoc, add_neg_cancel]
  -- now: NonNeg (x + 0)
  show Int.NonNeg (x + 0)
  -- x + 0 = x for Int (via add_zero / def)
  have h_x_zero : x + (0 : Int) = x := by
    rw [show (0 : Int) = -x + x from (add_left_neg x).symm]
    rw [← add_assoc, add_neg_cancel]
    show 0 + x = x
    exact zero_add x
  rw [h_x_zero]
  -- now: Int.NonNeg x from h_x : 0 ≤ x via def-unfolding.
  -- 0 ≤ x = Int.NonNeg (x - 0).  x - 0 = x + (-0) = x + 0 (rfl) = x (Int.add_zero).
  have h_x_sub : x - 0 = x := by
    show x + -0 = x
    show x + 0 = x
    exact Int.add_zero x
  exact h_x_sub ▸ h_x

end E213.Meta.Int213
