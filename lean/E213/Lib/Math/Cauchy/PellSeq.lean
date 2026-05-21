import E213.Lib.Math.Irrational.Sqrt2Cut
import E213.Lens.Cardinality
import E213.Meta.Tactic.NatHelper

/-!
# PellSeq: Pell sequence Raw construction

Mingu (priority): "demonstration that a Raw sequence satisfying
abLens.view (xs n) = Pell solutions can actually be constructed."

## Core

1. **Surjectivity of abLens** (a, b ≥ 1): for any (a, b) ∈ ℕ⁺ × ℕ⁺
   there exists a Raw r with abLens.view r = (a, b).
2. **Pell recursion**: x_{n+1} = x_n + 2 y_n, y_{n+1} = x_n + y_n
   (starting from (1, 1)).  Maintains the Pell invariant.
3. **Pell Raw sequence**: construct a Raw for each (x_n, y_n).

This captures the Dedekind cut of √2 not abstractly but as a
**constructive witness**.
-/

namespace E213.Lib.Math.Cauchy.PellSeq

open E213.Theory E213.Lens E213.Lens.Instances.AB E213.Lib.Math.Irrational.Sqrt2Cut

/-- Pell sequence (fundamental recursion preserving x² - 2y² = 1):
    (x, y) → (3x + 4y, 2x + 3y).
    Start (3, 2): (3, 2), (17, 12), (99, 70), (577, 408), ...
    All satisfy x² = 2y² + 1 (IsPellSol). -/
def pellPair : Nat → Nat × Nat
  | 0 => (3, 2)
  | n + 1 =>
      let p := pellPair n
      (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)

def pellX (n : Nat) : Nat := (pellPair n).1
def pellY (n : Nat) : Nat := (pellPair n).2

/-- Helper: collapse `n*z + n*z = (2*n)*z` in monomial form. -/
private theorem two_n_mul (n z : Nat) : n * z + n * z = (2 * n) * z := by
  rw [Nat.two_mul, E213.Tactic.NatHelper.add_mul]

/-- Expand (3x + 4y)². -/
private theorem expand_3x4y (x y : Nat) :
    (3 * x + 4 * y) * (3 * x + 4 * y)
      = 9 * (x * x) + 24 * (x * y) + 16 * (y * y) := by
  have h1 : (3 * x + 4 * y) * (3 * x + 4 * y)
          = (3 * x) * (3 * x) + (3 * x) * (4 * y)
            + ((4 * y) * (3 * x) + (4 * y) * (4 * y)) := by
    rw [E213.Tactic.NatHelper.add_mul, Nat.mul_add, Nat.mul_add]
  rw [h1]
  have e1 : (3 * x) * (3 * x) = 9 * (x * x) := by rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213]
  have e2 : (3 * x) * (4 * y) = 12 * (x * y) := by rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213]
  have e3 : (4 * y) * (3 * x) = 12 * (x * y) := by
    rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213, Nat.mul_comm y x]
  have e4 : (4 * y) * (4 * y) = 16 * (y * y) := by rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213]
  rw [e1, e2, e3, e4]
  -- Goal: 9*(x*x) + 12*(x*y) + (12*(x*y) + 16*(y*y))
  --     = 9*(x*x) + 24*(x*y) + 16*(y*y)
  rw [← Nat.add_assoc (9*(x*x) + 12*(x*y)) (12*(x*y)) (16*(y*y)),
      Nat.add_assoc (9*(x*x)) (12*(x*y)) (12*(x*y)),
      two_n_mul 12 (x*y)]

/-- Expand (2x + 3y)². -/
private theorem expand_2x3y (x y : Nat) :
    (2 * x + 3 * y) * (2 * x + 3 * y)
      = 4 * (x * x) + 12 * (x * y) + 9 * (y * y) := by
  have h1 : (2 * x + 3 * y) * (2 * x + 3 * y)
          = (2 * x) * (2 * x) + (2 * x) * (3 * y)
            + ((3 * y) * (2 * x) + (3 * y) * (3 * y)) := by
    rw [E213.Tactic.NatHelper.add_mul, Nat.mul_add, Nat.mul_add]
  rw [h1]
  have e1 : (2 * x) * (2 * x) = 4 * (x * x) := by rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213]
  have e2 : (2 * x) * (3 * y) = 6 * (x * y) := by rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213]
  have e3 : (3 * y) * (2 * x) = 6 * (x * y) := by
    rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213, Nat.mul_comm y x]
  have e4 : (3 * y) * (3 * y) = 9 * (y * y) := by rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213]
  rw [e1, e2, e3, e4]
  rw [← Nat.add_assoc (4*(x*x) + 6*(x*y)) (6*(x*y)) (9*(y*y)),
      Nat.add_assoc (4*(x*x)) (6*(x*y)) (6*(x*y)),
      two_n_mul 6 (x*y)]

/-- Helper: linear-in-(M,N) bivariate canonical form for the Pell
    identity.  After substitution by `h`, both sides reduce to
    `34*N + 24*M + 9`.  PURE Nat arithmetic chain. -/
private theorem pell_step_canonical (M N : Nat) :
    9*(2*N+1) + 24*M + 16*N = 2*(4*(2*N+1) + 12*M + 9*N) + 1 := by
  -- Reduce LHS to 34*N + 24*M + 9.
  have hL : 9*(2*N+1) + 24*M + 16*N = 34*N + (24*M + 9) := by
    rw [Nat.mul_add 9 (2*N) 1, Nat.mul_one,
        ← E213.Tactic.NatHelper.mul_assoc 9 2 N,
        show (9 : Nat) * 2 = 18 from rfl]
    -- Goal: 18*N + 9 + 24*M + 16*N = 34*N + (24*M + 9)
    rw [Nat.add_assoc (18*N + 9) (24*M) (16*N),
        Nat.add_comm (24*M) (16*N),
        ← Nat.add_assoc (18*N + 9) (16*N) (24*M),
        Nat.add_assoc (18*N) 9 (16*N),
        Nat.add_comm 9 (16*N),
        ← Nat.add_assoc (18*N) (16*N) 9,
        ← E213.Tactic.NatHelper.add_mul 18 16 N,
        show (18+16 : Nat) = 34 from rfl,
        Nat.add_assoc (34*N) 9 (24*M),
        Nat.add_comm 9 (24*M),
        ← Nat.add_assoc (34*N) (24*M) 9]
  -- Reduce RHS to 34*N + (24*M + 9).
  have hR : 2*(4*(2*N+1) + 12*M + 9*N) + 1 = 34*N + (24*M + 9) := by
    rw [Nat.mul_add 4 (2*N) 1, Nat.mul_one,
        ← E213.Tactic.NatHelper.mul_assoc 4 2 N,
        show (4 : Nat) * 2 = 8 from rfl]
    -- Goal: 2*(8*N + 4 + 12*M + 9*N) + 1 = 34*N + (24*M + 9)
    rw [Nat.mul_add 2 (8*N + 4 + 12*M) (9*N),
        Nat.mul_add 2 (8*N + 4) (12*M),
        Nat.mul_add 2 (8*N) 4,
        ← E213.Tactic.NatHelper.mul_assoc 2 8 N,
        ← E213.Tactic.NatHelper.mul_assoc 2 12 M,
        ← E213.Tactic.NatHelper.mul_assoc 2 9 N,
        show (2 : Nat) * 8 = 16 from rfl,
        show (2 : Nat) * 4 = 8 from rfl,
        show (2 : Nat) * 12 = 24 from rfl,
        show (2 : Nat) * 9 = 18 from rfl]
    -- Goal: 16*N + 8 + 24*M + 18*N + 1 = 34*N + (24*M + 9)
    rw [Nat.add_assoc (16*N + 8 + 24*M) (18*N) 1,
        Nat.add_assoc (16*N + 8) (24*M) (18*N + 1),
        Nat.add_comm (24*M) (18*N + 1),
        ← Nat.add_assoc (16*N + 8) (18*N + 1) (24*M),
        ← Nat.add_assoc (16*N + 8) (18*N) 1,
        Nat.add_assoc (16*N) 8 (18*N),
        Nat.add_comm 8 (18*N),
        ← Nat.add_assoc (16*N) (18*N) 8,
        ← E213.Tactic.NatHelper.add_mul 16 18 N,
        show (16+18 : Nat) = 34 from rfl,
        Nat.add_assoc (34*N + 8) 1 (24*M),
        Nat.add_comm 1 (24*M),
        ← Nat.add_assoc (34*N + 8) (24*M) 1,
        Nat.add_assoc (34*N) 8 (24*M),
        Nat.add_comm 8 (24*M),
        ← Nat.add_assoc (34*N) (24*M) 8,
        Nat.add_assoc (34*N + 24*M) 8 1,
        show (8+1 : Nat) = 9 from rfl,
        Nat.add_assoc (34*N) (24*M) 9]
  rw [hL, hR]

/-- **Pell step**: the invariant is preserved by the recursion. -/
theorem pell_step (x y : Nat) (h : x * x = 2 * (y * y) + 1) :
    (3 * x + 4 * y) * (3 * x + 4 * y)
      = 2 * ((2 * x + 3 * y) * (2 * x + 3 * y)) + 1 := by
  rw [expand_3x4y, expand_2x3y, h]
  exact pell_step_canonical (x*y) (y*y)

/-- **Pell invariant**: x_n² = 2 y_n² + 1. -/
theorem pell_invariant (n : Nat) : IsPellSol (pellX n) (pellY n) := by
  induction n with
  | zero =>
      show pellX 0 * pellX 0 = 2 * pellY 0 * pellY 0 + 1
      decide
  | succ k ih =>
      unfold IsPellSol at ih ⊢
      -- ih : pellX k * pellX k = 2 * pellY k * pellY k + 1
      have h_norm : pellX k * pellX k = 2 * (pellY k * pellY k) + 1 := by
        have heq : 2 * pellY k * pellY k = 2 * (pellY k * pellY k) :=
          E213.Tactic.NatHelper.mul_assoc 2 (pellY k) (pellY k)
        rw [heq] at ih; exact ih
      have h_step := pell_step (pellX k) (pellY k) h_norm
      show (3 * pellX k + 4 * pellY k) * (3 * pellX k + 4 * pellY k)
        = 2 * (2 * pellX k + 3 * pellY k) * (2 * pellX k + 3 * pellY k) + 1
      rw [E213.Tactic.NatHelper.mul_assoc 2 (2 * pellX k + 3 * pellY k)
            (2 * pellX k + 3 * pellY k)]
      exact h_step


open E213.Theory E213.Lens E213.Lens.Instances.AB

private theorem abLens_a : abLens.view Raw.a = (1, 0) := rfl
private theorem abLens_b : abLens.view Raw.b = (0, 1) := rfl

private theorem abLens_slash (x y : Raw) (h : x ≠ y) :
    abLens.view (Raw.slash x y h)
      = ((abLens.view x).1 + (abLens.view y).1,
         (abLens.view x).2 + (abLens.view y).2) := by
  apply Raw.fold_slash
  intro u v
  show (u.1 + v.1, u.2 + v.2) = (v.1 + u.1, v.2 + u.2)
  rw [Nat.add_comm u.1 v.1, Nat.add_comm u.2 v.2]

-- abLens_surjective is now defined AFTER abLens_witness (below) as a
-- direct PURE consequence, eliminating ~13 omega/simp uses.



/-- Constructive Σ-version: abLens_witness is an explicit Raw function.
    Constructive version of abLens_surjective — no Classical. -/
def abLens_witness (s : Nat) : ∀ (a b : Nat),
    a + b = s → 1 ≤ a → 1 ≤ b → {r : Raw // abLens.view r = (a, b)} := by
  induction s with
  | zero =>
      intro a b hsum ha _
      -- a + b = 0, but a ≥ 1 means a + b ≥ 1.  Contradiction.
      exfalso
      have : 1 ≤ 0 := hsum ▸ Nat.le_trans ha (Nat.le_add_right a b)
      exact absurd this (by decide)
  | succ n ih =>
      intro a b hsum ha hb
      by_cases h_ab : a = 1 ∧ b = 1
      · refine ⟨Raw.slash Raw.a Raw.b (by decide), ?_⟩
        rw [abLens_slash, abLens_a, abLens_b]
        show (1 + 0, 0 + 1) = (a, b)
        rw [h_ab.1, h_ab.2]
      · by_cases h_a2 : a ≥ 2
        · -- a ≥ 2 → recurse on (a-1, b)
          have ha_ne : a ≠ 0 := by
            intro hz; rw [hz] at ha; exact absurd ha (by decide)
          have ha' : 1 ≤ a - 1 := E213.Tactic.NatHelper.le_pred_of_succ_le h_a2
          have hsum' : (a - 1) + b = n := by
            have h1 : a - 1 + b + 1 = a + b := by
              rw [Nat.add_assoc, Nat.add_comm b 1, ← Nat.add_assoc,
                  E213.Tactic.NatHelper.sub_one_add_one ha_ne]
            exact Nat.succ.inj (h1.trans hsum)
          let ⟨r, hr⟩ := ih (a - 1) b hsum' ha' hb
          have hne : Raw.a ≠ r := by
            intro heq
            have := congrArg abLens.view heq
            rw [abLens_a, hr] at this
            have h0 : (0 : Nat) = b := congrArg Prod.snd this
            exact absurd (h0 ▸ hb) (by decide)
          refine ⟨Raw.slash Raw.a r hne, ?_⟩
          rw [abLens_slash, abLens_a, hr]
          show ((1 + (a - 1) : Nat), (0 + b : Nat)) = (a, b)
          rw [Nat.add_comm 1 (a-1),
              E213.Tactic.NatHelper.sub_one_add_one ha_ne,
              Nat.zero_add]
        · -- a < 2, a ≥ 1 → a = 1.  Then b ≥ 2 (since not (1,1)).
          have ha1 : a = 1 := by
            cases a with
            | zero => exact absurd ha (by decide)
            | succ k =>
              cases k with
              | zero => rfl
              | succ k' => exact absurd h_a2 (by
                  show ¬ 2 ≤ k' + 1 + 1 → False
                  intro h; exact h (Nat.succ_le_succ (Nat.succ_le_succ
                    (Nat.zero_le k'))))
          have hb2 : b ≥ 2 := by
            cases b with
            | zero => exact absurd hb (by decide)
            | succ k =>
              cases k with
              | zero => exact absurd (h_ab ⟨ha1, rfl⟩) (fun x => x)
              | succ k' => exact Nat.succ_le_succ (Nat.succ_le_succ
                  (Nat.zero_le k'))
          have hb_ne : b ≠ 0 := by
            intro hz; rw [hz] at hb; exact absurd hb (by decide)
          have hb' : 1 ≤ b - 1 := E213.Tactic.NatHelper.le_pred_of_succ_le hb2
          have hsum' : a + (b - 1) = n := by
            have h1 : a + (b - 1) + 1 = a + b := by
              rw [Nat.add_assoc,
                  E213.Tactic.NatHelper.sub_one_add_one hb_ne]
            exact Nat.succ.inj (h1.trans hsum)
          let ⟨r, hr⟩ := ih a (b - 1) hsum' ha hb'
          have hne : Raw.b ≠ r := by
            intro heq
            have := congrArg abLens.view heq
            rw [abLens_b, hr] at this
            have h0 : (0 : Nat) = a := congrArg Prod.fst this
            exact absurd (h0 ▸ ha) (by decide)
          refine ⟨Raw.slash Raw.b r hne, ?_⟩
          rw [abLens_slash, abLens_b, hr]
          show ((0 + a : Nat), (1 + (b - 1) : Nat)) = (a, b)
          rw [Nat.zero_add, Nat.add_comm 1 (b-1),
              E213.Tactic.NatHelper.sub_one_add_one hb_ne]

/-- abLens surjective on positive (a, b).  PURE via abLens_witness —
    directly extract the Σ-typed witness into an ∃-typed claim. -/
theorem abLens_surjective (s a b : Nat) (hsum : a + b = s) (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ∃ r : Raw, abLens.view r = (a, b) :=
  let ⟨r, hr⟩ := abLens_witness s a b hsum ha hb
  ⟨r, hr⟩



/-- Pell X positivity. -/
theorem pellX_pos (n : Nat) : 1 ≤ pellX n := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 1 ≤ 3 * (pellPair k).1 + 4 * (pellPair k).2
      have hxk : 1 ≤ (pellPair k).1 := ih
      have h3 : 3 ≤ 3 * (pellPair k).1 := by
        have := Nat.mul_le_mul_left 3 hxk
        rwa [Nat.mul_one] at this
      exact Nat.le_trans (by decide : 1 ≤ 3)
        (Nat.le_trans h3 (Nat.le_add_right _ _))

/-- Pell Y positivity. -/
theorem pellY_pos (n : Nat) : 1 ≤ pellY n := by
  induction n with
  | zero => decide
  | succ k _ =>
      show 1 ≤ 2 * (pellPair k).1 + 3 * (pellPair k).2
      have hxk : 1 ≤ (pellPair k).1 := pellX_pos k
      have h2 : 2 ≤ 2 * (pellPair k).1 := by
        have := Nat.mul_le_mul_left 2 hxk
        rwa [Nat.mul_one] at this
      exact Nat.le_trans (by decide : 1 ≤ 2)
        (Nat.le_trans h2 (Nat.le_add_right _ _))

/-- **Pell Raw sequence**: for each n, abLens.view (pellRaw n)
    = (pellX n, pellY n). -/
def pellRaw (n : Nat) : {r : Raw // abLens.view r = (pellX n, pellY n)} :=
  abLens_witness (pellX n + pellY n) (pellX n) (pellY n) rfl
    (pellX_pos n) (pellY_pos n)

theorem pellRaw_view (n : Nat) :
    abLens.view (pellRaw n).val = (pellX n, pellY n) :=
  (pellRaw n).property

/-- **√2 demonstration**: preservation of IsPellSol by the Pell Raw
    sequence.  Sqrt2Cut.pell_orderProj_above applies directly. -/
theorem pellRaw_isPellSol (n : Nat) :
    IsPellSol (abLens.view (pellRaw n).val).1
              (abLens.view (pellRaw n).val).2 := by
  rw [pellRaw_view]
  exact pell_invariant n


open E213.Lib.Math.Cauchy.Archimedean

/-- Lower bound for Pell Y: y_n ≥ n + 2 (linear growth). -/
theorem pellY_lb (n : Nat) : pellY n ≥ n + 2 := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 2 * (pellPair k).1 + 3 * (pellPair k).2 ≥ k + 1 + 2
      have hY : (pellPair k).2 ≥ k + 2 := ih
      -- Chain: k+3 ≤ k+6 ≤ 2k+6+k = 3*(k+2) ≤ 3*y ≤ 2x + 3y
      have h_3y : 3 * (k + 2) ≤ 3 * (pellPair k).2 := Nat.mul_le_mul_left 3 hY
      have h_3y_unfold : 3 * (k + 2) = k + 6 + 2 * k := by
        rw [Nat.mul_add 3 k 2,
            show 3 * k = k + 2 * k from by
              rw [show 3 = 1 + 2 from rfl, E213.Tactic.NatHelper.add_mul,
                  Nat.one_mul],
            show (3 : Nat) * 2 = 6 from rfl,
            Nat.add_assoc k (2*k) 6, Nat.add_comm (2*k) 6,
            ← Nat.add_assoc]
      have h_kp3_le : k + 1 + 2 ≤ 3 * (k + 2) := by
        rw [h_3y_unfold]
        show k + 3 ≤ k + 6 + 2 * k
        exact Nat.le_trans
          (Nat.add_le_add_left (by decide : (3 : Nat) ≤ 6) k)
          (Nat.le_add_right _ _)
      exact Nat.le_trans h_kp3_le (Nat.le_trans h_3y (Nat.le_add_left _ _))

/-- **√2 cut from Pell Raw seq (above)**: when 2k² < m², orderProj is
    true from a sufficiently large N. -/
theorem pellRaw_cut_above (m k : Nat) (hk : k ≥ 1) (hmsq : 2 * k * k < m * m) :
    ∃ N, ∀ n, n ≥ N →
      orderProj m k (abLens.view (pellRaw n).val) = true := by
  refine ⟨k, ?_⟩
  intro n hn
  rw [pellRaw_view]
  -- pellY n ≥ n + 2 ≥ n ≥ k
  have hyn : pellY n ≥ k :=
    Nat.le_trans hn (Nat.le_trans (Nat.le_add_right n 2) (pellY_lb n))
  have hyn_sq : k * k ≤ pellY n * pellY n := Nat.mul_le_mul hyn hyn
  exact pell_orderProj_above (pellX n) (pellY n) m k
    (pell_invariant n) hmsq hyn_sq

/-- **√2 cut from Pell Raw seq (below)**: when m² < 2k², orderProj is
    false for all n. -/
theorem pellRaw_cut_below (m k : Nat) (hk : k ≥ 1) (hmsq : m * m < 2 * k * k)
    (n : Nat) :
    orderProj m k (abLens.view (pellRaw n).val) = false := by
  rw [pellRaw_view]
  exact pell_orderProj_below (pellX n) (pellY n) m k
    (pell_invariant n) hk hmsq

end E213.Lib.Math.Cauchy.PellSeq
