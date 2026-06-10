import E213.Lib.Math.NumberSystems.Real213.AbCutSeq
import E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake
import E213.Lib.Math.Analysis.Cauchy.PellSeq
import E213.Meta.Nat.PolyNat
import E213.Meta.Nat.PureNat
import E213.Meta.Nat.NatRing213

/-!
# CubeRootTwoCut — ∛2: the degree-3 form-margin modulus (the algebraic exit from the rate race)

The modulus ladder's algebraic pillar, at degree 3.  For the transcendental
instances (e, Liouville) the total modulus comes from the **rate race** — the
cross-determinant `W` staying below the denominator's growth
(`holonomic_modulus.md`); ζ(3)'s factorial-cleared presentation *loses* that race
(`Zeta3Cut.zeta3_presentation_overtakes`).  This file shows the algebraic
mechanism is **different in kind**: for ∛2 the side-decision against a probe
`m/k` reduces to the all-additive comparison

    `ε_i · k³ < d_i³`

where `ε_i` is the presentation's cube-slack — the **degree-3 form margin**
`|m³ − 2k³| ≥ 1` arriving for free as the `+1` of `Nat` strictness, with the
probe appearing through `k³`.  No cross-determinant, no `W`-vs-`d` race: *any*
presentation whose cube-slack shrinks gets a total modulus.  The degree-2 shadow
of the same schema is already in the repo: `FibCassiniNat.qb_lt_pk` squares the
φ-comparison down to `4·k² < b²` — `ε·k² < d²` with constant slack.  Here the
exponent climbs to 3 and the mechanism is isolated.

Concretely, with the dyadic bisection presentation (`cbrtNum i / 2^i`, the
cube-bracket invariant `cbrtNum_inv`):

  * slack bound `ε_i ≤ 24·4^i` against `d_i³ = 8^i` (`cbrt_margin`) — the
    comparison is won at `i ≈ 3k`, giving the **total ∅-axiom modulus
    `N(m,k) = 3k+5`** (`cbrtCauchySeq`), linear in `k` like e's — but produced
    by the *form*, not the rate certificate;
  * the completed limit **equals the frozen closed-form cut**
    `decide (2k³ ≤ m³)` (`cbrt_limit_eq_form`) — the dynamic fold lands exactly
    on the algebraic relation, the degree-3 analog of
    `FibCassiniNat.cs_eq_phiCut`;
  * bracket `5/4 < ∛2 ≤ 13/10`.

So ∛2 joins φ, e, Liouville in the unconditional class — the first degree-3
member — and the ladder's structure clarifies: **algebraic degree `s` enters as
the probe-exponent `k^s` in the schedule, and the form-margin makes the modulus
presentation-robust; the rate race (and its presentation-dependence) is the
transcendental-only regime.**

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut

open E213.Theory (Raw)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.Analysis.Cauchy.Archimedean (orderProj)
open E213.Lib.Math.Analysis.Cauchy.PellSeq (abLens_witness)
open E213.Lib.Math.Analysis.Cauchy.MonotonicBounded (IsAbMonotonic IsAbPositiveB)
open E213.Lib.Math.NumberSystems.Real213 (AbCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)
open E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake (two_pow_ge_succ two_pow_ge_self)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Meta.Nat.PolyNat (poly_id)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_left nat_mul_lt_mul_right)
open E213.Tactic.NatHelper (add_mul mul_assoc mul_left_comm mul_mul_mul_comm_213
  le_of_add_le_add_left lt_of_lt_le lt_of_le_lt add_sub_of_le)

/-! ## §0 — cube arithmetic -/

/-- `n³`, spelled multiplicatively. -/
def cube (n : Nat) : Nat := n*n*n

theorem cube_double (a : Nat) : cube (2*a) = 8 * cube a :=
  poly_id (.mul (.mul (.mul (.C 2) .X) (.mul (.C 2) .X)) (.mul (.C 2) .X))
          (.mul (.C 8) (.mul (.mul .X .X) .X))
          rfl a

theorem cube_succ (a : Nat) : cube (a+1) = cube a + (3*a*a + 3*a + 1) :=
  poly_id (.mul (.mul (.add .X (.C 1)) (.add .X (.C 1))) (.add .X (.C 1)))
          (.add (.mul (.mul .X .X) .X)
                (.add (.add (.mul (.mul (.C 3) .X) .X) (.mul (.C 3) .X)) (.C 1)))
          rfl a

theorem cube_mul (x y : Nat) : cube (x*y) = cube x * cube y := by
  show x*y*(x*y)*(x*y) = x*x*x*(y*y*y)
  rw [mul_mul_mul_comm_213 x y x y, mul_mul_mul_comm_213 (x*x) (y*y) x y]

theorem cube_le {x y : Nat} (h : x ≤ y) : cube x ≤ cube y :=
  Nat.mul_le_mul (Nat.mul_le_mul h h) h

theorem cube_lt {x y : Nat} (h : x < y) : cube x < cube y := by
  have hy : 0 < y := Nat.lt_of_le_of_lt (Nat.zero_le x) h
  have hyy : 0 < y*y := Nat.mul_pos hy hy
  have h1 : cube x ≤ y*y*x :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_of_lt h) (Nat.le_of_lt h)) (Nat.le_refl x)
  have h2 : y*y*x < y*y*y := by
    rw [mul_assoc y y x, mul_assoc y y y]
    exact nat_mul_lt_mul_left hy (nat_mul_lt_mul_left hy h)
  exact lt_of_le_lt h1 h2

theorem pow_three (x : Nat) : x^3 = cube x := by
  show x^3 = x*x*x
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

private theorem two_pow_pos (i : Nat) : 1 ≤ 2^i :=
  Nat.le_trans (Nat.succ_le_succ (Nat.zero_le i)) (two_pow_ge_succ i)

private theorem cube_two_pow (k : Nat) : cube ((2:Nat)^k) = 2^(3*k) := by
  induction k with
  | zero => decide
  | succ t ih =>
    have h1 : (2:Nat)^(t+1) = 2 * 2^t := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h1, cube_double, ih, Nat.mul_succ 3 t, pow_add 2 (3*t) 3,
        Nat.mul_comm 8 ((2:Nat)^(3*t)), show (8:Nat) = 2^3 from by decide]

private theorem two_pow_le_two_pow {a b : Nat} (h : a ≤ b) : (2:Nat)^a ≤ 2^b := by
  rw [← add_sub_of_le h, pow_add 2 a (b-a)]
  have h1 : (2:Nat)^a * 1 ≤ 2^a * 2^(b-a) :=
    Nat.mul_le_mul_left _ (two_pow_pos (b-a))
  rw [Nat.mul_one] at h1
  exact h1

/-! ## §1 — the dyadic bisection presentation of ∛2

`cbrtNum i / 2^i`: at each layer double the denominator and take the upper
midpoint exactly when its cube still fits under `2·(2^{i+1})³`. -/

/-- The dyadic ∛2 numerator: bisection on the cube bracket. -/
def cbrtNum : Nat → Nat
  | 0 => 1
  | i+1 => if cube (2 * cbrtNum i + 1) ≤ 2 * cube (2^(i+1))
           then 2 * cbrtNum i + 1 else 2 * cbrtNum i

theorem cbrtNum_succ (i : Nat) :
    cbrtNum (i+1) = if cube (2 * cbrtNum i + 1) ≤ 2 * cube (2^(i+1))
                    then 2 * cbrtNum i + 1 else 2 * cbrtNum i := rfl

private theorem cube_two_pow_succ (i : Nat) : cube ((2:Nat)^(i+1)) = 8 * cube (2^i) := by
  rw [Nat.pow_succ, Nat.mul_comm (2^i) 2, cube_double]

/-- ★ **The cube-bracket invariant**: at every layer the numerator's cube sits
    under `2·d³` and the successor's cube above — `cbrtNum i / 2^i` is the best
    dyadic approximant from below. -/
theorem cbrtNum_inv : ∀ i, cube (cbrtNum i) ≤ 2 * cube (2^i)
    ∧ 2 * cube (2^i) < cube (cbrtNum i + 1)
  | 0 => ⟨by decide, by decide⟩
  | i+1 => by
    have ih := cbrtNum_inv i
    by_cases h : cube (2 * cbrtNum i + 1) ≤ 2 * cube (2^(i+1))
    · refine ⟨?_, ?_⟩
      · rw [cbrtNum_succ, if_pos h]; exact h
      · rw [cbrtNum_succ, if_pos h]
        have h2 : 2 * cbrtNum i + 1 + 1 = 2 * (cbrtNum i + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        rw [h2, cube_double, cube_two_pow_succ, mul_left_comm 2 8 (cube (2^i))]
        exact nat_mul_lt_mul_left (by decide) ih.2
    · refine ⟨?_, ?_⟩
      · rw [cbrtNum_succ, if_neg h, cube_double, cube_two_pow_succ,
            mul_left_comm 2 8 (cube (2^i))]
        exact Nat.mul_le_mul_left 8 ih.1
      · rw [cbrtNum_succ, if_neg h]
        exact Nat.lt_of_not_le h

theorem cbrtNum_pos : ∀ i, 1 ≤ cbrtNum i
  | 0 => Nat.le_refl 1
  | i+1 => by
    have ih := cbrtNum_pos i
    have h2 : 1 ≤ 2 * cbrtNum i :=
      Nat.le_trans ih (Nat.le_mul_of_pos_left _ (by decide))
    rw [cbrtNum_succ]
    by_cases h : cube (2 * cbrtNum i + 1) ≤ 2 * cube (2^(i+1))
    · rw [if_pos h]; exact Nat.le_trans h2 (Nat.le_succ _)
    · rw [if_neg h]; exact h2

/-- The numerator stays under twice the denominator (`∛2 < 2`). -/
theorem cbrtNum_lt : ∀ i, cbrtNum i < 2 * 2^i
  | 0 => by decide
  | i+1 => by
    have ih := cbrtNum_lt i
    have key : 2 * cbrtNum i + 1 < 2 * 2^(i+1) := by
      have h1 : 2 * (cbrtNum i + 1) ≤ 2 * (2 * 2^i) := Nat.mul_le_mul_left 2 ih
      have h2 : 2 * cbrtNum i + 1 < 2 * (cbrtNum i + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        exact Nat.add_lt_add_left (by decide) _
      have h3 : (2:Nat) * (2 * 2^i) = 2 * 2^(i+1) := by
        rw [Nat.pow_succ, Nat.mul_comm (2^i) 2]
      exact lt_of_lt_le h2 (h3 ▸ h1)
    rw [cbrtNum_succ]
    by_cases h : cube (2 * cbrtNum i + 1) ≤ 2 * cube (2^(i+1))
    · rw [if_pos h]; exact key
    · rw [if_neg h]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) key

/-- One bisection step never decreases the value: `2·aᵢ ≤ aᵢ₊₁`. -/
theorem cbrtNum_step_ge (i : Nat) : 2 * cbrtNum i ≤ cbrtNum (i+1) := by
  rw [cbrtNum_succ]
  by_cases h : cube (2 * cbrtNum i + 1) ≤ 2 * cube (2^(i+1))
  · rw [if_pos h]; exact Nat.le_succ _
  · rw [if_neg h]; exact Nat.le_refl _

/-! ## §2 — the form margin: cube-slack `ε_i ≤ 24·(2^i)²` -/

/-- ★★ **The cube-slack bound**: `2·d³ ≤ a³ + 24·(2^i)²` — the presentation's
    distance-to-2 in cube terms is quadratically small against the cubic
    denominator.  From the bracket invariant via `(a+1)³ = a³ + 3a² + 3a + 1`
    and `a < 2^{i+1}`. -/
theorem cbrt_margin (i : Nat) :
    2 * cube (2^i) ≤ cube (cbrtNum i) + 24 * (2^i * 2^i) := by
  have h1 : 2 * cube (2^i) < cube (cbrtNum i + 1) := (cbrtNum_inv i).2
  rw [cube_succ (cbrtNum i)] at h1
  have hassoc : cube (cbrtNum i) + (3*cbrtNum i*cbrtNum i + 3*cbrtNum i + 1)
      = (cube (cbrtNum i) + (3*cbrtNum i*cbrtNum i + 3*cbrtNum i)) + 1 :=
    (Nat.add_assoc _ _ 1).symm
  rw [hassoc] at h1
  have h2 : 2 * cube (2^i) ≤ cube (cbrtNum i) + (3*cbrtNum i*cbrtNum i + 3*cbrtNum i) :=
    Nat.le_of_lt_succ h1
  refine Nat.le_trans h2 (Nat.add_le_add_left ?_ _)
  -- 3a² + 3a ≤ 24·(2^i)², from a < 2·2^i (so a ≤ 2·2^i) and 1 ≤ a
  have ha : cbrtNum i ≤ 2 * 2^i := Nat.le_of_lt (cbrtNum_lt i)
  have hlin : 3*cbrtNum i ≤ 3*cbrtNum i*cbrtNum i := by
    rw [mul_assoc 3 (cbrtNum i) (cbrtNum i)]
    exact Nat.mul_le_mul_left 3 (Nat.le_mul_of_pos_left _ (cbrtNum_pos i))
  have hsum : 3*cbrtNum i*cbrtNum i + 3*cbrtNum i ≤ 6*(cbrtNum i*cbrtNum i) := by
    have h6 : (6:Nat)*(cbrtNum i*cbrtNum i)
        = 3*(cbrtNum i*cbrtNum i) + 3*(cbrtNum i*cbrtNum i) :=
      add_mul 3 3 (cbrtNum i*cbrtNum i)
    rw [h6, ← mul_assoc 3 (cbrtNum i) (cbrtNum i)]
    exact Nat.add_le_add_left hlin _
  have hsq : cbrtNum i * cbrtNum i ≤ (2*2^i) * (2*2^i) := Nat.mul_le_mul ha ha
  have hfour : (2*2^i) * (2*2^i) = 4 * (2^i * 2^i) := mul_mul_mul_comm_213 2 (2^i) 2 (2^i)
  refine Nat.le_trans hsum ?_
  have h24 : (24:Nat) * (2^i * 2^i) = 6 * (4 * (2^i * 2^i)) := mul_assoc 6 4 _
  rw [h24]
  exact Nat.mul_le_mul_left 6 (hfour ▸ hsq)

/-- ★★ **The degree-3 schedule**: past layer `3k+5` the cube-slack times the
    probe's cubic weight is beaten by the denominator's cube —
    `24·(2^i)²·k³ < (2^i)³`.  The probe enters as `k³`: the form's degree is the
    exponent of the schedule. -/
theorem cbrt_schedule (k i : Nat) (hi : 3*k+5 ≤ i) :
    24 * (2^i * 2^i) * cube k < cube (2^i) := by
  have hkey : 24 * cube k < 2^i := by
    have hcpos : 0 < cube (2^k) :=
      Nat.lt_of_lt_of_le (by decide) (cube_le (two_pow_pos k))
    have h1 : 24 * cube k ≤ 24 * cube (2^k) :=
      Nat.mul_le_mul_left 24 (cube_le (two_pow_ge_self k))
    have h2 : 24 * cube (2^k) < 2^5 * cube (2^k) :=
      nat_mul_lt_mul_right hcpos (by decide)
    have h3 : (2:Nat)^5 * cube (2^k) = 2^(3*k+5) := by
      rw [pow_add 2 (3*k) 5, ← cube_two_pow k, Nat.mul_comm (2^5) (cube (2^k))]
    have h4 : (2:Nat)^(3*k+5) ≤ 2^i := two_pow_le_two_pow hi
    exact lt_of_le_lt h1 (lt_of_lt_le h2 (h3 ▸ h4))
  have hL : 24 * (2^i * 2^i) * cube k = (2^i * 2^i) * (24 * cube k) := by
    rw [mul_assoc 24 (2^i * 2^i) (cube k), mul_left_comm 24 (2^i * 2^i) (cube k)]
  have hR : cube ((2:Nat)^i) = (2^i * 2^i) * 2^i := rfl
  rw [hL, hR]
  have hPpos : 0 < (2:Nat)^i * 2^i :=
    Nat.lt_of_lt_of_le (by decide) (Nat.mul_le_mul (two_pow_pos i) (two_pow_pos i))
  exact nat_mul_lt_mul_left hPpos hkey

/-! ## §3 — side decision against any probe (the form does the work) -/

/-- ★★★ **True side** (`m/k ≥ ∛2`, i.e. `2k³ ≤ m³`): every layer cut is true —
    the convergents never overshoot.  Pure cube monotonicity. -/
theorem cbrt_true_side (m k n : Nat) (hm : 2 * cube k ≤ cube m) :
    cbrtNum n * k ≤ 2^n * m := by
  by_cases hle : cbrtNum n * k ≤ 2^n * m
  · exact hle
  · exfalso
    have h1 : 2^n * m < cbrtNum n * k := Nat.lt_of_not_le hle
    have h2 : cube (2^n) * cube m < cube (cbrtNum n) * cube k := by
      rw [← cube_mul, ← cube_mul]; exact cube_lt h1
    have h3 : cube (cbrtNum n) * cube k ≤ 2 * cube (2^n) * cube k :=
      Nat.mul_le_mul_right _ (cbrtNum_inv n).1
    have h4 : 2 * cube (2^n) * cube k = cube (2^n) * (2 * cube k) := by
      rw [mul_assoc 2 (cube (2^n)) (cube k), mul_left_comm 2 (cube (2^n)) (cube k)]
    have h5 : cube (2^n) * (2 * cube k) ≤ cube (2^n) * cube m :=
      Nat.mul_le_mul_left _ hm
    exact Nat.lt_irrefl _
      (lt_of_lt_le h2 (Nat.le_trans h3 (Nat.le_trans (Nat.le_of_eq h4) h5)))

/-- ★★★ **False side** (`m/k < ∛2`, i.e. `m³ + 1 ≤ 2k³`): past layer `3k+5` the
    cut is false.  All-additive: if the cut were true, cubing and inserting the
    margin (`cbrt_margin`) and the probe bound forces `d³ ≤ ε·k³`, contradicting
    the schedule.  The `+1` of `Nat` strictness IS the degree-3 form margin
    `|m³ − 2k³| ≥ 1`. -/
theorem cbrt_false_side (m k n : Nat) (hb : cube m + 1 ≤ 2 * cube k)
    (hn : 3*k+5 ≤ n) : ¬ (cbrtNum n * k ≤ 2^n * m) := by
  intro hle
  -- cube both sides of the supposed cut
  have h1 : cube (cbrtNum n) * cube k ≤ cube (2^n) * cube m := by
    rw [← cube_mul, ← cube_mul]; exact cube_le hle
  -- margin × k³ : 2d³·k³ ≤ a³·k³ + ε·k³ ≤ d³·m³ + ε·k³
  have h2 : 2 * cube (2^n) * cube k
      ≤ cube (2^n) * cube m + 24 * (2^n * 2^n) * cube k := by
    have := Nat.mul_le_mul_right (cube k) (cbrt_margin n)
    rw [add_mul (cube (cbrtNum n)) (24 * (2^n * 2^n)) (cube k)] at this
    exact Nat.le_trans this (Nat.add_le_add_right h1 _)
  -- probe bound × d³ : m³·d³ + d³ ≤ 2k³·d³ = 2d³·k³
  have h3 : cube (2^n) * cube m + cube (2^n) ≤ 2 * cube (2^n) * cube k := by
    have := Nat.mul_le_mul_left (cube (2^n)) hb
    rw [Nat.mul_add (cube (2^n)) (cube m) 1, Nat.mul_one] at this
    have hsh : cube ((2:Nat)^n) * (2 * cube k) = 2 * cube (2^n) * cube k := by
      rw [mul_left_comm (cube (2^n)) 2 (cube k), ← mul_assoc 2 (cube (2^n)) (cube k)]
    exact hsh ▸ this
  -- combine and cancel:  d³ ≤ ε·k³, contradicting the schedule
  have h4 : cube (2^n) * cube m + cube (2^n)
      ≤ cube (2^n) * cube m + 24 * (2^n * 2^n) * cube k :=
    Nat.le_trans h3 h2
  have h5 : cube ((2:Nat)^n) ≤ 24 * (2^n * 2^n) * cube k :=
    le_of_add_le_add_left h4
  exact Nat.lt_irrefl _ (lt_of_le_lt h5 (cbrt_schedule k n hn))

/-! ## §4 — the `AbCutSeq` and the total modulus `N(m,k) = 3k+5` -/

/-- The ∛2 convergent Raw at layer `n`: `(cbrtNum n, 2^n)`. -/
def cbrtRaw (n : Nat) :
    {r : Raw // abLens.view r = (cbrtNum n, 2^n)} :=
  abLens_witness (cbrtNum n + 2^n) (cbrtNum n) (2^n) rfl (cbrtNum_pos n) (two_pow_pos n)

theorem cbrtRaw_view (n : Nat) :
    abLens.view (cbrtRaw n).val = (cbrtNum n, 2^n) := (cbrtRaw n).property

def cbrtRawSeq : Nat → Raw := fun n => (cbrtRaw n).val

theorem cbrt_isAbMonotonic : IsAbMonotonic cbrtRawSeq := by
  intro n
  show (abLens.view (cbrtRaw n).val).1 * (abLens.view (cbrtRaw (n+1)).val).2
     ≤ (abLens.view (cbrtRaw (n+1)).val).1 * (abLens.view (cbrtRaw n).val).2
  rw [cbrtRaw_view, cbrtRaw_view]
  show cbrtNum n * 2^(n+1) ≤ cbrtNum (n+1) * 2^n
  have h1 : cbrtNum n * 2^(n+1) = (2 * cbrtNum n) * 2^n := by
    rw [Nat.pow_succ, Nat.mul_comm (2^n) 2, mul_left_comm (cbrtNum n) 2 (2^n),
        ← mul_assoc 2 (cbrtNum n) (2^n)]
  rw [h1]
  exact Nat.mul_le_mul_right _ (cbrtNum_step_ge n)

theorem cbrt_isAbPositiveB : IsAbPositiveB cbrtRawSeq := by
  intro n
  show 1 ≤ (abLens.view (cbrtRaw n).val).2
  rw [cbrtRaw_view]
  exact two_pow_pos n

/-- ★★★ **∛2's bisection convergents as an `AbCutSeq`.** -/
def cbrtAb : AbCutSeq := ⟨cbrtRawSeq, cbrt_isAbMonotonic, cbrt_isAbPositiveB⟩

/-- **∛2's cut at layer `n`**: `decide (cbrtNum n · k ≤ 2^n · m)`. -/
def cbrtCut (n : Nat) : Nat → Nat → Bool := cbrtAb.cut n

theorem cbrtCut_valid (n : Nat) : ValidCut (cbrtCut n) := cbrtAb.cut_valid n

theorem cbrtCut_eq (n m k : Nat) :
    cbrtCut n m k = decide (cbrtNum n * k ≤ 2^n * m) := by
  show orderProj m k (abLens.view (cbrtRaw n).val) = _
  rw [cbrtRaw_view]; rfl

/-- ★★★ **The total ∅-axiom modulus `N(m,k) = 3k+5`** — ∛2's cut sequence is a
    `CauchyCutSeq` with the modulus a *constructed field*, like φ, e, and the
    Liouville constant; unlike them, the certificate is the **degree-3 form
    margin**, not a cross-determinant rate. -/
def cbrtCauchySeq : CauchyCutSeq where
  cs := cbrtCut
  N := fun _ k => 3*k+5
  cauchy := by
    intro m k i j hi hj
    by_cases hm : 2 * cube k ≤ cube m
    · rw [cbrtCut_eq, cbrtCut_eq,
          decide_eq_true (cbrt_true_side m k i hm),
          decide_eq_true (cbrt_true_side m k j hm)]
    · have hb : cube m + 1 ≤ 2 * cube k := Nat.lt_of_not_le hm
      rw [cbrtCut_eq, cbrtCut_eq,
          decide_eq_false (cbrt_false_side m k i hb hi),
          decide_eq_false (cbrt_false_side m k j hb hj)]

/-! ## §5 — the fold lands on the frozen form cut -/

/-- **The frozen (closed-form) ∛2 cut**: `decide (2k³ ≤ m³)` — the degree-3
    algebraic relation read directly as a cut, no layers, no modulus.  The
    degree-3 analog of φ's `masterCut`. -/
def cbrt2Cut : Nat → Nat → Bool := fun m k => decide (2 * cube k ≤ cube m)

/-- ★★★ **The dynamic fold lands exactly on the frozen cut**: the completed
    limit of the bisection sequence *is* the closed-form cut, at every probe.
    Degree-3 analog of `FibCassiniNat.cs_eq_phiCut` /
    `PhiCauchyLimit.phiCauchy_limit_eq_phiCut`. -/
theorem cbrt_limit_eq_form (m k : Nat) :
    cbrtCauchySeq.limit m k = cbrt2Cut m k := by
  show cbrtCut (3*k+5) m k = cbrt2Cut m k
  by_cases hm : 2 * cube k ≤ cube m
  · rw [cbrtCut_eq, decide_eq_true (cbrt_true_side m k (3*k+5) hm),
        show cbrt2Cut m k = true from decide_eq_true hm]
  · have hb : cube m + 1 ≤ 2 * cube k := Nat.lt_of_not_le hm
    rw [cbrtCut_eq, decide_eq_false (cbrt_false_side m k (3*k+5) hb (Nat.le_refl _)),
        show cbrt2Cut m k = false from decide_eq_false hm]

/-- ★★★ **The frozen cut is a valid real** — transported pointwise from the
    completed limit's validity along `cbrt_limit_eq_form`. -/
theorem cbrt2Cut_valid : ValidCut cbrt2Cut where
  upM := fun m1 m2 k h hm => by
    rw [← cbrt_limit_eq_form] at hm ⊢
    exact (cbrtCauchySeq.limit_valid (fun i => cbrtCut_valid i)).upM m1 m2 k h hm
  dnK := fun m k1 k2 h hm => by
    rw [← cbrt_limit_eq_form] at hm ⊢
    exact (cbrtCauchySeq.limit_valid (fun i => cbrtCut_valid i)).dnK m k1 k2 h hm

/-- ★★ **Bracket `5/4 < ∛2 ≤ 13/10`**: `2·4³ = 128 > 125 = 5³` and
    `2·10³ = 2000 ≤ 2197 = 13³`. -/
theorem cbrt2_bracket : cbrt2Cut 5 4 = false ∧ cbrt2Cut 13 10 = true :=
  ⟨by decide, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut
