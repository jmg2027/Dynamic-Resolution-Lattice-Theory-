import E213.Math.Irrational.Sqrt2Cut
import E213.Infinity.LensCardinality

/-!
# Research.PellSeq: Pell sequence Raw construction

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

namespace E213.Math.Cauchy.PellSeq

open E213.Firmware E213.Hypervisor E213.Research.ABLens E213.Research.Sqrt2Cut

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

/-- Expand (3x + 4y)². -/
private theorem expand_3x4y (x y : Nat) :
    (3 * x + 4 * y) * (3 * x + 4 * y)
      = 9 * (x * x) + 24 * (x * y) + 16 * (y * y) := by
  have h1 : (3 * x + 4 * y) * (3 * x + 4 * y)
          = (3 * x) * (3 * x) + (3 * x) * (4 * y)
            + ((4 * y) * (3 * x) + (4 * y) * (4 * y)) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  rw [h1]
  have e1 : (3 * x) * (3 * x) = 9 * (x * x) := by rw [Nat.mul_mul_mul_comm]
  have e2 : (3 * x) * (4 * y) = 12 * (x * y) := by rw [Nat.mul_mul_mul_comm]
  have e3 : (4 * y) * (3 * x) = 12 * (x * y) := by
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm y x]
  have e4 : (4 * y) * (4 * y) = 16 * (y * y) := by rw [Nat.mul_mul_mul_comm]
  rw [e1, e2, e3, e4]; omega

/-- Expand (2x + 3y)². -/
private theorem expand_2x3y (x y : Nat) :
    (2 * x + 3 * y) * (2 * x + 3 * y)
      = 4 * (x * x) + 12 * (x * y) + 9 * (y * y) := by
  have h1 : (2 * x + 3 * y) * (2 * x + 3 * y)
          = (2 * x) * (2 * x) + (2 * x) * (3 * y)
            + ((3 * y) * (2 * x) + (3 * y) * (3 * y)) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  rw [h1]
  have e1 : (2 * x) * (2 * x) = 4 * (x * x) := by rw [Nat.mul_mul_mul_comm]
  have e2 : (2 * x) * (3 * y) = 6 * (x * y) := by rw [Nat.mul_mul_mul_comm]
  have e3 : (3 * y) * (2 * x) = 6 * (x * y) := by
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm y x]
  have e4 : (3 * y) * (3 * y) = 9 * (y * y) := by rw [Nat.mul_mul_mul_comm]
  rw [e1, e2, e3, e4]; omega

/-- **Pell step**: the invariant is preserved by the recursion. -/
theorem pell_step (x y : Nat) (h : x * x = 2 * (y * y) + 1) :
    (3 * x + 4 * y) * (3 * x + 4 * y)
      = 2 * ((2 * x + 3 * y) * (2 * x + 3 * y)) + 1 := by
  rw [expand_3x4y, expand_2x3y]
  -- Goal: 9 * (x*x) + 24 * (x*y) + 16 * (y*y) = 2 * (4*(x*x) + 12*(x*y) + 9*(y*y)) + 1
  -- = 8*(x*x) + 24*(x*y) + 18*(y*y) + 1
  -- iff (x*x) = 2*(y*y) + 1 (= h after normalizing).
  omega

/-- **Pell invariant**: x_n² = 2 y_n² + 1. -/
theorem pell_invariant (n : Nat) : IsPellSol (pellX n) (pellY n) := by
  induction n with
  | zero =>
      unfold IsPellSol pellX pellY pellPair
      decide
  | succ k ih =>
      unfold IsPellSol at *
      have h_norm : pellX k * pellX k = 2 * (pellY k * pellY k) + 1 := by
        have : 2 * pellY k * pellY k = 2 * (pellY k * pellY k) := by
          rw [Nat.mul_assoc]
        omega
      have h_step := pell_step (pellX k) (pellY k) h_norm
      show pellX (k + 1) * pellX (k + 1) = 2 * pellY (k + 1) * pellY (k + 1) + 1
      unfold pellX pellY pellPair
      simp only
      rw [Nat.mul_assoc]
      exact h_step

end E213.Math.Cauchy.PellSeq

namespace E213.Math.Cauchy.PellSeq

open E213.Firmware E213.Hypervisor E213.Research.ABLens

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

/-- abLens surjective on positive (a, b).  Strong induction on a + b. -/
theorem abLens_surjective : ∀ (s a b : Nat),
    a + b = s → 1 ≤ a → 1 ≤ b → ∃ r : Raw, abLens.view r = (a, b) := by
  intro s
  induction s with
  | zero => intro a b hsum ha hb; exact False.elim (by omega)
  | succ n ih =>
      intro a b hsum ha hb
      by_cases h_ab : a = 1 ∧ b = 1
      · refine ⟨Raw.slash Raw.a Raw.b (by decide), ?_⟩
        rw [abLens_slash, abLens_a, abLens_b]
        simp [h_ab.1, h_ab.2]
      · -- (a, b) ≠ (1, 1).  Either a ≥ 2 or b ≥ 2.
        by_cases h_a2 : a ≥ 2
        · -- Recurse on (a-1, b)
          have ha' : 1 ≤ a - 1 := by omega
          have hsum' : (a - 1) + b = n := by omega
          obtain ⟨r, hr⟩ := ih (a - 1) b hsum' ha' hb
          have hne : Raw.a ≠ r := by
            intro heq
            have := congrArg abLens.view heq
            rw [abLens_a, hr] at this
            -- (1, 0) = (a-1, b).  But b ≥ 1, so b ≠ 0.
            have h0 : (0 : Nat) = b := by
              have := congrArg Prod.snd this
              exact this
            omega
          refine ⟨Raw.slash Raw.a r hne, ?_⟩
          rw [abLens_slash, abLens_a, hr]
          simp; omega
        · -- a = 1, b ≥ 2
          have ha1 : a = 1 := by omega
          have hb2 : b ≥ 2 := by
            by_cases hb_eq : b = 1
            · exfalso; exact h_ab ⟨ha1, hb_eq⟩
            · omega
          have hb' : 1 ≤ b - 1 := by omega
          have hsum' : a + (b - 1) = n := by omega
          obtain ⟨r, hr⟩ := ih a (b - 1) hsum' ha hb'
          have hne : Raw.b ≠ r := by
            intro heq
            have := congrArg abLens.view heq
            rw [abLens_b, hr] at this
            -- (0, 1) = (a, b-1).  a ≥ 1, so 0 ≠ a.
            have h0 : (0 : Nat) = a := by
              have := congrArg Prod.fst this
              exact this
            omega
          refine ⟨Raw.slash Raw.b r hne, ?_⟩
          rw [abLens_slash, abLens_b, hr]
          simp; omega

end E213.Math.Cauchy.PellSeq

namespace E213.Math.Cauchy.PellSeq

open E213.Firmware E213.Hypervisor E213.Research.ABLens

/-- Constructive Σ-version: abLens_witness is an explicit Raw function.
    Constructive version of abLens_surjective — no Classical. -/
def abLens_witness (s : Nat) : ∀ (a b : Nat),
    a + b = s → 1 ≤ a → 1 ≤ b → {r : Raw // abLens.view r = (a, b)} := by
  induction s with
  | zero => intro a b hsum ha hb; exact False.elim (by omega)
  | succ n ih =>
      intro a b hsum ha hb
      by_cases h_ab : a = 1 ∧ b = 1
      · refine ⟨Raw.slash Raw.a Raw.b (by decide), ?_⟩
        rw [abLens_slash, abLens_a, abLens_b]
        simp [h_ab.1, h_ab.2]
      · by_cases h_a2 : a ≥ 2
        · have ha' : 1 ≤ a - 1 := by omega
          have hsum' : (a - 1) + b = n := by omega
          let ⟨r, hr⟩ := ih (a - 1) b hsum' ha' hb
          have hne : Raw.a ≠ r := by
            intro heq
            have := congrArg abLens.view heq
            rw [abLens_a, hr] at this
            have h0 : (0 : Nat) = b := congrArg Prod.snd this
            omega
          refine ⟨Raw.slash Raw.a r hne, ?_⟩
          rw [abLens_slash, abLens_a, hr]
          simp; omega
        · have ha1 : a = 1 := by omega
          have hb2 : b ≥ 2 := by
            by_cases hb_eq : b = 1
            · exact False.elim (h_ab ⟨ha1, hb_eq⟩)
            · omega
          have hb' : 1 ≤ b - 1 := by omega
          have hsum' : a + (b - 1) = n := by omega
          let ⟨r, hr⟩ := ih a (b - 1) hsum' ha hb'
          have hne : Raw.b ≠ r := by
            intro heq
            have := congrArg abLens.view heq
            rw [abLens_b, hr] at this
            have h0 : (0 : Nat) = a := congrArg Prod.fst this
            omega
          refine ⟨Raw.slash Raw.b r hne, ?_⟩
          rw [abLens_slash, abLens_b, hr]
          simp; omega

end E213.Math.Cauchy.PellSeq

namespace E213.Math.Cauchy.PellSeq

open E213.Firmware E213.Hypervisor E213.Research.ABLens E213.Research.Sqrt2Cut

/-- Pell X positivity. -/
theorem pellX_pos (n : Nat) : 1 ≤ pellX n := by
  induction n with
  | zero => unfold pellX pellPair; decide
  | succ k ih =>
      show 1 ≤ pellX (k + 1)
      unfold pellX pellPair
      simp only
      have hxk : 1 ≤ (pellPair k).1 := ih
      omega

/-- Pell Y positivity. -/
theorem pellY_pos (n : Nat) : 1 ≤ pellY n := by
  induction n with
  | zero => unfold pellY pellPair; decide
  | succ k _ =>
      show 1 ≤ pellY (k + 1)
      unfold pellY pellPair
      simp only
      have hxk : 1 ≤ (pellPair k).1 := pellX_pos k
      omega

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

end E213.Math.Cauchy.PellSeq

namespace E213.Math.Cauchy.PellSeq

open E213.Firmware E213.Hypervisor E213.Research.ABLens E213.Research.Sqrt2Cut
open E213.Research.ArchimedeanCauchy

/-- Lower bound for Pell Y: y_n ≥ n + 2 (linear growth). -/
theorem pellY_lb (n : Nat) : pellY n ≥ n + 2 := by
  induction n with
  | zero => unfold pellY pellPair; decide
  | succ k ih =>
      show pellY (k + 1) ≥ k + 1 + 2
      unfold pellY pellPair
      simp only
      have hX : 1 ≤ (pellPair k).1 := pellX_pos k
      have hY : (pellPair k).2 ≥ k + 2 := ih
      omega

/-- **√2 cut from Pell Raw seq (above)**: when 2k² < m², orderProj is
    true from a sufficiently large N. -/
theorem pellRaw_cut_above (m k : Nat) (hk : k ≥ 1) (hmsq : 2 * k * k < m * m) :
    ∃ N, ∀ n, n ≥ N →
      orderProj m k (abLens.view (pellRaw n).val) = true := by
  refine ⟨k, ?_⟩
  intro n hn
  rw [pellRaw_view]
  -- pellY n ≥ n + 2 ≥ k + 2 > k, so pellY n² ≥ k²
  have hyn : pellY n ≥ k := by
    have := pellY_lb n
    omega
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

end E213.Math.Cauchy.PellSeq
