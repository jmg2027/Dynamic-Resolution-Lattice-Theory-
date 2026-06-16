import E213.Lib.Math.Logic.LLPO
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCut
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# vein-C CALIBRATION: the real sign dichotomy ⟹ LLPO (analytic LLPO)

The exact Intermediate Value Theorem / bisection's "is f(m) ≤ 0 or ≥ 0?" step is
an omniscience act.  We pin it precisely: deciding `cutLe x zero ∨ cutLe zero x`
for *every* corpus real `x : Nat → Nat → Bool` implies `LLPO`.

LLPO/the dichotomy are HYPOTHESES (Prop variables), never axioms — so the
calibration is genuinely ∅-axiom.

## The encoding

Given an at-most-one-true `f : Nat → Bool`, build a real `y_f` whose sign relative
to the constant `1` decides the even/odd LLPO disjunction:

  `y_f = 1 + Σ_{i} c_i`,  `c_i = +2^{-(i+1)}` if `f i` fires at even `i`,
  `−2^{-(i+1)}` if at odd `i`, `0` otherwise.

Because at most one `i` fires, `y_f ∈ {1, 1+2^{-(n+1)}, 1−2^{-(n+1)}}`, always a
positive rational — representable as a non-negative `Nat/Nat` cut.  Working with
`y_f` shifted by `+1` keeps the whole construction inside the corpus's
non-negative-rational cuts (`constCut a b = decide(a*k ≤ b*m)`, value `b/a`).
-/

namespace E213.Lib.Math.Logic.RealDichotomyLLPO

open E213.Lib.Math.Logic (LLPO parity parity_two_mul parity_two_mul_add_one)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutLe cutEq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)

/-! ## §1 — the partial-sum numerator `P f n` over denominator `2^n`

`P f n` is the numerator of `y_f`'s layer-`n` approximant `P f n / 2^n`.
Recursion: doubling the denominator doubles the numerator; a fire at index `n`
(value `±2^{-(n+1)}` = numerator `±1` at the *new* denominator `2^{n+1}`) adjusts
by `+1` (even) or `−1` (odd).  The `−1` is safe because `2 * P f n ≥ 2 ≥ 1`. -/

/-- Layer-`n` numerator of `y_f` over denominator `2^n`.
    Doubling the denominator doubles the numerator; a fire at index `n` adds the
    new term `±2^{-(n+1)}` = numerator `±1` (even `+1`, odd `−1`); no fire leaves
    it. -/
def P (f : Nat → Bool) : Nat → Nat
  | 0     => 1
  | n + 1 =>
    if f n = true then
      (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1)
    else 2 * P f n

/-- The numerator is always ≥ 1 (so `y_f` is a positive rational at every layer). -/
theorem P_pos (f : Nat → Bool) : ∀ n, 1 ≤ P f n
  | 0     => Nat.le_refl 1
  | n + 1 => by
    show 1 ≤ (if f n = true then
        (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) else 2 * P f n)
    have h2 : 2 ≤ 2 * P f n :=
      Nat.le_trans (Nat.le_of_eq (Nat.mul_one 2).symm) (Nat.mul_le_mul_left 2 (P_pos f n))
    cases hf : f n with
    | false =>
      show 1 ≤ 2 * P f n
      exact Nat.le_trans (by decide) h2
    | true =>
      show 1 ≤ (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1)
      cases hp : parity n with
      | true =>
        show 1 ≤ 2 * P f n - 1
        exact Nat.le_trans (Nat.le_of_eq (by decide : (1:Nat) = 2 - 1))
          (Nat.sub_le_sub_right h2 1)
      | false =>
        show 1 ≤ 2 * P f n + 1
        exact Nat.succ_le_succ (Nat.zero_le _)

/-- `2 ≤ 2 * P f n`: the doubled numerator is at least 2. -/
theorem two_le_twoP (f : Nat → Bool) (n : Nat) : 2 ≤ 2 * P f n :=
  Nat.le_trans (Nat.le_of_eq (Nat.mul_one 2).symm) (Nat.mul_le_mul_left 2 (P_pos f n))

/-! ## §2 — `P f L` vs `2^L`: the sign of `y_f − 1`

No fire below `L` ⟹ `P f L = 2^L` (value `= 1`); an even fire ⟹ `P f L > 2^L`
(value `> 1`); an odd fire ⟹ `P f L < 2^L` (value `< 1`).  These are the three
sign verdicts, each driven by the unique fire. -/

/-- No fire at any index below `L` keeps the numerator at exactly `2^L` (value 1). -/
theorem P_eq_pow_of_noFire (f : Nat → Bool) :
    ∀ L, (∀ i, i < L → f i = false) → P f L = 2 ^ L
  | 0,     _  => rfl
  | L + 1, h => by
    show (if f L = true then
        (if parity L = true then 2 * P f L - 1 else 2 * P f L + 1) else 2 * P f L) = 2 ^ (L + 1)
    have hfL : f L = false := h L (Nat.lt_succ_self L)
    rw [hfL]
    show 2 * P f L = 2 ^ (L + 1)
    rw [P_eq_pow_of_noFire f L (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self L)))]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ L) 2]

/-- `2 * a < 2 * b` from `a < b`, additively (avoids the dirty `Nat.mul_lt_mul_left`). -/
theorem two_mul_lt {a b : Nat} (h : a < b) : 2 * a < 2 * b := by
  rw [Nat.two_mul a, Nat.two_mul b]; exact Nat.add_lt_add h h

/-- Doubling preserves strict `>`: `2^L < x → 2^(L+1) < 2*x`. -/
theorem pow_lt_double {L x : Nat} (h : 2 ^ L < x) : 2 ^ (L + 1) < 2 * x := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ L) 2]; exact two_mul_lt h

/-! ### Even fire ⟹ value > 1 (`2^L < P f L` for `L > n`) -/

/-- After an even fire at `n` (with no later fire), `P f L > 2^L` for every `L > n`.
    Induct on the offset `t = L − (n+1)`: base `P f (n+1) = 2^{n+1}+1`, step doubles. -/
theorem P_gt_pow_even (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = false)
    (hbefore : ∀ i, i < n → f i = false)
    (hafter : ∀ i, n < i → f i = false) :
    ∀ t, 2 ^ (n + 1 + t) < P f (n + 1 + t) := by
  intro t
  induction t with
  | zero =>
    -- P f (n+1) = 2 * 2^n + 1 = 2^{n+1} + 1
    have hbase : P f (n + 1) = 2 * 2 ^ n + 1 := by
      show (if f n = true then
          (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) else 2 * P f n)
          = 2 * 2 ^ n + 1
      rw [hfn]
      show (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) = 2 * 2 ^ n + 1
      rw [hpar]
      show 2 * P f n + 1 = 2 * 2 ^ n + 1
      rw [P_eq_pow_of_noFire f n hbefore]
    show 2 ^ (n + 1 + 0) < P f (n + 1 + 0)
    rw [Nat.add_zero, hbase, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
    exact Nat.lt_succ_self _
  | succ t ih =>
    -- index n+1+t > n, so no fire there: P f (n+1+(t+1)) = 2 * P f (n+1+t)
    have hidx : n < n + 1 + t := Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
      (Nat.le_add_right (n + 1) t)
    have hnofire : f (n + 1 + t) = false := hafter _ hidx
    have hstep : P f (n + 1 + t + 1) = 2 * P f (n + 1 + t) := by
      show (if f (n + 1 + t) = true then
          (if parity (n + 1 + t) = true then 2 * P f (n + 1 + t) - 1
            else 2 * P f (n + 1 + t) + 1) else 2 * P f (n + 1 + t)) = 2 * P f (n + 1 + t)
      rw [hnofire]; rfl
    show 2 ^ (n + 1 + t + 1) < P f (n + 1 + t + 1)
    rw [hstep]
    exact pow_lt_double ih

/-- Doubling preserves strict `<` toward `2^{L+1}`: `x < 2^L → 2*x < 2^(L+1)`. -/
theorem double_lt_pow {L x : Nat} (h : x < 2 ^ L) : 2 * x < 2 ^ (L + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ L) 2]; exact two_mul_lt h

/-! ### Odd fire ⟹ value < 1 (`P f L < 2^L` for `L > n`) -/

/-- After an odd fire at `n` (with no later fire), `P f L < 2^L` for every `L > n`.
    Base `P f (n+1) = 2^{n+1} − 1 < 2^{n+1}`; step doubles, preserving `<`. -/
theorem P_lt_pow_odd (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbefore : ∀ i, i < n → f i = false)
    (hafter : ∀ i, n < i → f i = false) :
    ∀ t, P f (n + 1 + t) < 2 ^ (n + 1 + t) := by
  intro t
  induction t with
  | zero =>
    -- P f (n+1) = 2 * 2^n - 1 = 2^{n+1} - 1
    have hbase : P f (n + 1) = 2 * 2 ^ n - 1 := by
      show (if f n = true then
          (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) else 2 * P f n)
          = 2 * 2 ^ n - 1
      rw [hfn]
      show (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) = 2 * 2 ^ n - 1
      rw [hpar]
      show 2 * P f n - 1 = 2 * 2 ^ n - 1
      rw [P_eq_pow_of_noFire f n hbefore]
    show P f (n + 1 + 0) < 2 ^ (n + 1 + 0)
    rw [Nat.add_zero, hbase, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
    -- 2*2^n - 1 < 2*2^n
    exact Nat.sub_lt (Nat.mul_pos (by decide) (Nat.pos_pow_of_pos n (by decide))) (by decide)
  | succ t ih =>
    have hidx : n < n + 1 + t := Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
      (Nat.le_add_right (n + 1) t)
    have hnofire : f (n + 1 + t) = false := hafter _ hidx
    have hstep : P f (n + 1 + t + 1) = 2 * P f (n + 1 + t) := by
      show (if f (n + 1 + t) = true then
          (if parity (n + 1 + t) = true then 2 * P f (n + 1 + t) - 1
            else 2 * P f (n + 1 + t) + 1) else 2 * P f (n + 1 + t)) = 2 * P f (n + 1 + t)
      rw [hnofire]; rfl
    show P f (n + 1 + t + 1) < 2 ^ (n + 1 + t + 1)
    rw [hstep]
    exact double_lt_pow ih

/-! ### Exact closed forms (additive — no subtraction)

`P f (n+1+t) = 2^(n+1+t) + 2^t`  (even fire),
`P f (n+1+t) + 2^t = 2^(n+1+t)`  (odd fire).
These exact forms drive the separating-probe arithmetic. -/

/-- Even-fire exact numerator: `P f (n+1+t) = 2^(n+1+t) + 2^t`. -/
theorem P_even_exact (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = false)
    (hbefore : ∀ i, i < n → f i = false)
    (hafter : ∀ i, n < i → f i = false) :
    ∀ t, P f (n + 1 + t) = 2 ^ (n + 1 + t) + 2 ^ t := by
  intro t
  induction t with
  | zero =>
    show P f (n + 1 + 0) = 2 ^ (n + 1 + 0) + 2 ^ 0
    rw [Nat.add_zero]
    show P f (n + 1) = 2 ^ (n + 1) + 1
    show (if f n = true then
        (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) else 2 * P f n)
        = 2 ^ (n + 1) + 1
    rw [hfn]; show (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) = 2 ^ (n + 1) + 1
    rw [hpar]; show 2 * P f n + 1 = 2 ^ (n + 1) + 1
    rw [P_eq_pow_of_noFire f n hbefore, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
  | succ t ih =>
    have hidx : n < n + 1 + t := Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
      (Nat.le_add_right (n + 1) t)
    have hnofire : f (n + 1 + t) = false := hafter _ hidx
    have hstep : P f (n + 1 + t + 1) = 2 * P f (n + 1 + t) := by
      show (if f (n + 1 + t) = true then
          (if parity (n + 1 + t) = true then 2 * P f (n + 1 + t) - 1
            else 2 * P f (n + 1 + t) + 1) else 2 * P f (n + 1 + t)) = 2 * P f (n + 1 + t)
      rw [hnofire]; rfl
    show P f (n + 1 + t + 1) = 2 ^ (n + 1 + t + 1) + 2 ^ (t + 1)
    rw [hstep, ih, Nat.mul_add, Nat.pow_succ 2 (n + 1 + t), Nat.pow_succ 2 t,
        Nat.mul_comm (2 ^ (n + 1 + t)) 2, Nat.mul_comm (2 ^ t) 2]

/-- Odd-fire exact numerator (additive form): `P f (n+1+t) + 2^t = 2^(n+1+t)`. -/
theorem P_odd_exact (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbefore : ∀ i, i < n → f i = false)
    (hafter : ∀ i, n < i → f i = false) :
    ∀ t, P f (n + 1 + t) + 2 ^ t = 2 ^ (n + 1 + t) := by
  intro t
  induction t with
  | zero =>
    show P f (n + 1 + 0) + 2 ^ 0 = 2 ^ (n + 1 + 0)
    rw [Nat.add_zero]
    show P f (n + 1) + 1 = 2 ^ (n + 1)
    have hbase : P f (n + 1) = 2 * 2 ^ n - 1 := by
      show (if f n = true then
          (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) else 2 * P f n)
          = 2 * 2 ^ n - 1
      rw [hfn]; show (if parity n = true then 2 * P f n - 1 else 2 * P f n + 1) = 2 * 2 ^ n - 1
      rw [hpar]; show 2 * P f n - 1 = 2 * 2 ^ n - 1
      rw [P_eq_pow_of_noFire f n hbefore]
    rw [hbase, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
    -- (2*2^n - 1) + 1 = 2*2^n  via Nat.succ_pred_eq_of_pos
    exact Nat.succ_pred_eq_of_pos (Nat.mul_pos (by decide) (Nat.pos_pow_of_pos n (by decide)))
  | succ t ih =>
    have hidx : n < n + 1 + t := Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
      (Nat.le_add_right (n + 1) t)
    have hnofire : f (n + 1 + t) = false := hafter _ hidx
    have hstep : P f (n + 1 + t + 1) = 2 * P f (n + 1 + t) := by
      show (if f (n + 1 + t) = true then
          (if parity (n + 1 + t) = true then 2 * P f (n + 1 + t) - 1
            else 2 * P f (n + 1 + t) + 1) else 2 * P f (n + 1 + t)) = 2 * P f (n + 1 + t)
      rw [hnofire]; rfl
    show P f (n + 1 + t + 1) + 2 ^ (t + 1) = 2 ^ (n + 1 + t + 1)
    rw [hstep, Nat.pow_succ 2 t, Nat.pow_succ 2 (n + 1 + t), Nat.mul_comm (2 ^ t) 2,
        Nat.mul_comm (2 ^ (n + 1 + t)) 2, ← Nat.mul_add]
    exact congrArg (2 * ·) ih

/-! ## §3 — the encoded cut, the constant `1`, and uniqueness extraction -/

/-- The encoded real `y_f` as a corpus cut.  At resolution `k` it reads the
    layer-`(k+1)` approximant `P f (k+1) / 2^(k+1)` (a `constCut`, value
    `P f (k+1) / 2^(k+1)`). -/
def yf (f : Nat → Bool) : Nat → Nat → Bool :=
  fun m k => constCut (P f (k + 1)) (2 ^ (k + 1)) m k

/-- The constant `1` as a cut: `constCut 1 1`, value `1`. -/
def one : Nat → Nat → Bool := constCut 1 1

/-- `one m k = decide (k ≤ m)`. -/
theorem one_eq (m k : Nat) : one m k = decide (k ≤ m) := by
  show decide (1 * k ≤ 1 * m) = decide (k ≤ m)
  rw [Nat.one_mul, Nat.one_mul]

/-- `yf f m k = decide (P f (k+1) * k ≤ 2^(k+1) * m)`. -/
theorem yf_eq (f : Nat → Bool) (m k : Nat) :
    yf f m k = decide (P f (k + 1) * k ≤ 2 ^ (k + 1) * m) := rfl

/-- Strict right-multiplication by a positive: `a < b → 0 < c → a*c < b*c`. -/
theorem mul_lt_mul_right_pos {a b c : Nat} (h : a < b) (hc : 0 < c) : a * c < b * c :=
  Nat.lt_of_lt_of_le
    (Nat.lt_add_of_pos_right hc)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right c h)

/-- From an at-most-one-true `f` with a fire at `n`, every index `< n` is `false`. -/
theorem before_false (f : Nat → Bool)
    (hone : ∀ m n, f m = true → f n = true → m = n) (n : Nat) (hfn : f n = true) :
    ∀ i, i < n → f i = false :=
  fun i hi => E213.Lib.Math.Logic.ne_true_imp_false (f i)
    (fun hfi => absurd (hone i n hfi hfn) (Nat.ne_of_lt hi))

/-- From an at-most-one-true `f` with a fire at `n`, every index `> n` is `false`. -/
theorem after_false (f : Nat → Bool)
    (hone : ∀ m n, f m = true → f n = true → m = n) (n : Nat) (hfn : f n = true) :
    ∀ i, n < i → f i = false :=
  fun i hi => E213.Lib.Math.Logic.ne_true_imp_false (f i)
    (fun hfi => absurd (hone i n hfi hfn).symm (Nat.ne_of_lt hi))

/-! ## §4 — the two sign lemmas

`cutLe (yf f) one → ∀ k, f(2k) = false` (`y_f ≤ 1` ⟹ no even fire), and
`cutLe one (yf f) → ∀ k, f(2k+1) = false` (`1 ≤ y_f` ⟹ no odd fire). -/

/-- **Even sign lemma**: if the encoded real is `≤ 1`, no even index fires.
    An even fire at `n = 2j` makes `y_f > 1`, so at probe `(n+1, n+1)` (where
    `one` reads `true`) the cut `yf` reads `false`, contradicting `cutLe (yf f) one`. -/
theorem noEvenFire_of_le (f : Nat → Bool)
    (hone : ∀ m n, f m = true → f n = true → m = n)
    (hle : cutLe (yf f) one) : ∀ j, f (2 * j) = false := by
  intro j
  apply E213.Lib.Math.Logic.ne_true_imp_false
  intro hfn
  -- fire at n = 2*j, even
  have hpar : parity (2 * j) = false := parity_two_mul j
  have hbef := before_false f hone (2 * j) hfn
  have haft := after_false f hone (2 * j) hfn
  -- yf at (2j+1, 2j+1) is false
  have hgt : 2 ^ (2 * j + 1 + 1) < P f (2 * j + 1 + 1) :=
    P_gt_pow_even f (2 * j) hfn hpar hbef haft 1
  have hstrict : 2 ^ (2 * j + 1 + 1) * (2 * j + 1) < P f (2 * j + 1 + 1) * (2 * j + 1) :=
    mul_lt_mul_right_pos hgt (Nat.succ_le_succ (Nat.zero_le _))
  have hyf_false : yf f (2 * j + 1) (2 * j + 1) = false := by
    rw [yf_eq]
    exact decide_eq_false (Nat.not_le.mpr hstrict)
  -- one at (2j+1, 2j+1) is true
  have hone_true : one (2 * j + 1) (2 * j + 1) = true := by
    rw [one_eq]; exact decide_eq_true (Nat.le_refl _)
  -- cutLe forces yf = true: contradiction
  have := hle (2 * j + 1) (2 * j + 1) hone_true
  rw [hyf_false] at this
  exact Bool.noConfusion this

/-- **Odd-fire separating probe** (the technical heart of the odd sign lemma).
    For an odd fire at `n`, at resolution `k = n+1+2^{n+1}` and `m = n+2^{n+1}`
    the encoded cut reads `true` (`y_f ≤ m/k`).  Set `S = 2^{n+1}`; then
    `k+1 = (n+1)+(S+1)`, so `P_odd_exact` gives `P f(k+1) + 2^{S+1} = 2^{k+1}`,
    and `2^{k+1} = S·2^{S+1}` cancels the gap exactly. -/
theorem odd_probe_yf_true (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    yf f (n + 2 ^ (n + 1)) (n + 1 + 2 ^ (n + 1)) = true := by
  rw [yf_eq]
  apply decide_eq_true
  -- abbreviations as plain lets
  -- hexact : P f (k+1) + 2^(S+1) = 2^(k+1),  with k = n+1+S, S = 2^(n+1)
  have hexact :
      P f (n + 1 + 2 ^ (n + 1) + 1) + 2 ^ (2 ^ (n + 1) + 1)
        = 2 ^ (n + 1 + 2 ^ (n + 1) + 1) :=
    P_odd_exact f n hfn hpar hbef haft (2 ^ (n + 1) + 1)
  -- 2^(k+1) = 2^(n+1) * 2^(S+1)
  have hpk :
      (2 : Nat) ^ (n + 1 + 2 ^ (n + 1) + 1)
        = 2 ^ (n + 1) * 2 ^ (2 ^ (n + 1) + 1) := by
    rw [Nat.add_assoc (n + 1) (2 ^ (n + 1)) 1,
        E213.Meta.Nat.PureNat.pow_add 2 (n + 1) (2 ^ (n + 1) + 1)]
  -- Q ≤ 2^(n+1) * 2^(S+1)
  have hQ_le :
      P f (n + 1 + 2 ^ (n + 1) + 1) ≤ 2 ^ (n + 1) * 2 ^ (2 ^ (n + 1) + 1) := by
    rw [← hpk]; exact Nat.le.intro hexact
  -- 2^(n+1) * 2^(S+1) ≤ 2^(S+1) * (n + 2^(n+1))
  have hEm :
      2 ^ (n + 1) * 2 ^ (2 ^ (n + 1) + 1)
        ≤ 2 ^ (2 ^ (n + 1) + 1) * (n + 2 ^ (n + 1)) := by
    rw [Nat.mul_comm (2 ^ (n + 1)) (2 ^ (2 ^ (n + 1) + 1))]
    exact Nat.mul_le_mul_left _ (Nat.le_add_left (2 ^ (n + 1)) n)
  -- Q * k = Q * m + Q   (k = m + 1)
  have hk_eq : n + 1 + 2 ^ (n + 1) = (n + 2 ^ (n + 1)) + 1 :=
    Nat.add_right_comm n 1 (2 ^ (n + 1))
  have hQk :
      P f (n + 1 + 2 ^ (n + 1) + 1) * (n + 1 + 2 ^ (n + 1))
        = P f (n + 1 + 2 ^ (n + 1) + 1) * (n + 2 ^ (n + 1))
          + P f (n + 1 + 2 ^ (n + 1) + 1) := by
    rw [hk_eq, Nat.mul_add, Nat.mul_one]
  -- assemble: P f(k+1) * k ≤ 2^(k+1) * m
  rw [hQk, ← hexact, E213.Tactic.NatHelper.add_mul]
  exact Nat.add_le_add_left (Nat.le_trans hQ_le hEm) _

/-- **Odd sign lemma**: if the encoded real is `≥ 1`, no odd index fires.
    An odd fire at `n = 2j+1` makes `y_f = 1 − 2^{-(n+1)} < 1`.  At the fine
    resolution `k = n+1+2^{n+1}`, `m = k−1`, `one` reads `false` (`m < k`) while
    `yf` reads `true` (`y_f ≤ m/k`), contradicting `cutLe one (yf f)`.  The
    separating point needs denominator `~2^{n+1}` because the gap
    `1 − y_f = 2^{-(n+1)}` is that fine — this is the omniscience cost. -/
theorem noOddFire_of_ge (f : Nat → Bool)
    (hone : ∀ m n, f m = true → f n = true → m = n)
    (hge : cutLe one (yf f)) : ∀ j, f (2 * j + 1) = false := by
  intro j
  apply E213.Lib.Math.Logic.ne_true_imp_false
  intro hfn
  have hpar : parity (2 * j + 1) = true := parity_two_mul_add_one j
  have hbef := before_false f hone (2 * j + 1) hfn
  have haft := after_false f hone (2 * j + 1) hfn
  have hyf_true :
      yf f (2 * j + 1 + 2 ^ (2 * j + 1 + 1)) (2 * j + 1 + 1 + 2 ^ (2 * j + 1 + 1)) = true :=
    odd_probe_yf_true f (2 * j + 1) hfn hpar hbef haft
  have hone_false :
      one (2 * j + 1 + 2 ^ (2 * j + 1 + 1)) (2 * j + 1 + 1 + 2 ^ (2 * j + 1 + 1)) = false := by
    rw [one_eq]
    apply decide_eq_false
    -- ¬ ( (n+1) + S ≤ n + S ), i.e. ¬ (m+1 ≤ m)
    rw [Nat.add_right_comm (2 * j + 1) 1 (2 ^ (2 * j + 1 + 1))]
    exact Nat.not_le.mpr (Nat.lt_succ_self _)
  have := hge _ _ hyf_true
  rw [hone_false] at this
  exact Bool.noConfusion this

/-! ## §4b — converse positive bounds (for `LLPO ⟹` the encoded dichotomy)

No even fire ⟹ `P f L ≤ 2^L` (value ≤ 1); no odd fire ⟹ `2^L ≤ P f L`
(value ≥ 1).  An even index never fires ⟹ a step is at most a doubling; an odd
index never fires ⟹ a step is at least a doubling. -/

/-- No even fire ⟹ each step is at most a doubling: `P f (L+1) ≤ 2 * P f L`. -/
theorem P_step_le_of_noEven (f : Nat → Bool) (hev : ∀ j, f (2 * j) = false) (L : Nat) :
    P f (L + 1) ≤ 2 * P f L := by
  show (if f L = true then
      (if parity L = true then 2 * P f L - 1 else 2 * P f L + 1) else 2 * P f L) ≤ 2 * P f L
  cases hf : f L with
  | false => exact Nat.le_refl _
  | true =>
    -- f L = true ⟹ L is odd (even L would give f L = false)
    cases hpar : parity L with
    | true => show 2 * P f L - 1 ≤ 2 * P f L; exact Nat.sub_le _ _
    | false =>
      -- parity L = false ⟹ L = 2j ⟹ f L = false, contradiction with hf
      exact absurd hf (by
        cases (E213.Lib.Math.Logic.even_or_odd L) with
        | inl he => exact he.elim (fun j hj => hj ▸ (hev j) ▸ Bool.noConfusion)
        | inr ho => exact ho.elim (fun j hj =>
            absurd (hj ▸ hpar) (by rw [parity_two_mul_add_one j]; exact Bool.noConfusion)))

/-- No odd fire ⟹ each step is at least a doubling: `2 * P f L ≤ P f (L+1)`. -/
theorem P_step_ge_of_noOdd (f : Nat → Bool) (hod : ∀ j, f (2 * j + 1) = false) (L : Nat) :
    2 * P f L ≤ P f (L + 1) := by
  show 2 * P f L ≤ (if f L = true then
      (if parity L = true then 2 * P f L - 1 else 2 * P f L + 1) else 2 * P f L)
  cases hf : f L with
  | false => exact Nat.le_refl _
  | true =>
    cases hpar : parity L with
    | false => show 2 * P f L ≤ 2 * P f L + 1; exact Nat.le_add_right _ _
    | true =>
      -- parity L = true ⟹ L = 2j+1 ⟹ f L = false, contradiction
      exact absurd hf (by
        cases (E213.Lib.Math.Logic.even_or_odd L) with
        | inr ho => exact ho.elim (fun j hj => hj ▸ (hod j) ▸ Bool.noConfusion)
        | inl he => exact he.elim (fun j hj =>
            absurd (hj ▸ hpar) (by rw [parity_two_mul j]; exact Bool.noConfusion)))

/-- No even fire ⟹ `P f L ≤ 2^L` (the encoded value is ≤ 1). -/
theorem P_le_pow_of_noEven (f : Nat → Bool) (hev : ∀ j, f (2 * j) = false) :
    ∀ L, P f L ≤ 2 ^ L
  | 0     => Nat.le_refl 1
  | L + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ L) 2]
    exact Nat.le_trans (P_step_le_of_noEven f hev L)
      (Nat.mul_le_mul_left 2 (P_le_pow_of_noEven f hev L))

/-- No odd fire ⟹ `2^L ≤ P f L` (the encoded value is ≥ 1). -/
theorem pow_le_P_of_noOdd (f : Nat → Bool) (hod : ∀ j, f (2 * j + 1) = false) :
    ∀ L, 2 ^ L ≤ P f L
  | 0     => Nat.le_refl 1
  | L + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ L) 2]
    exact Nat.le_trans (Nat.mul_le_mul_left 2 (pow_le_P_of_noOdd f hod L))
      (P_step_ge_of_noOdd f hod L)

/-- No even fire ⟹ `cutLe (yf f) one` (value ≤ 1 ≤ m/k whenever `one` fires). -/
theorem le_of_noEven (f : Nat → Bool) (hev : ∀ j, f (2 * j) = false) :
    cutLe (yf f) one := by
  intro m k hk
  -- one m k = true ⟹ k ≤ m
  rw [one_eq] at hk
  have hkm : k ≤ m := of_decide_eq_true hk
  rw [yf_eq]
  apply decide_eq_true
  -- P f(k+1) * k ≤ 2^(k+1) * k ≤ 2^(k+1) * m
  exact Nat.le_trans
    (Nat.mul_le_mul_right k (P_le_pow_of_noEven f hev (k + 1)))
    (Nat.mul_le_mul_left (2 ^ (k + 1)) hkm)

/-- No odd fire ⟹ `cutLe one (yf f)` (value ≥ 1 ≥ m/k whenever `yf` fires). -/
theorem ge_of_noOdd (f : Nat → Bool) (hod : ∀ j, f (2 * j + 1) = false) :
    cutLe one (yf f) := by
  intro m k hk
  -- yf f m k = true ⟹ P f(k+1)*k ≤ 2^(k+1)*m
  rw [yf_eq] at hk
  have hyf : P f (k + 1) * k ≤ 2 ^ (k + 1) * m := of_decide_eq_true hk
  rw [one_eq]
  apply decide_eq_true
  -- want k ≤ m.  From 2^(k+1)*k ≤ P f(k+1)*k ≤ 2^(k+1)*m  ⟹ k ≤ m.
  have h1 : 2 ^ (k + 1) * k ≤ 2 ^ (k + 1) * m :=
    Nat.le_trans (Nat.mul_le_mul_right k (pow_le_P_of_noOdd f hod (k + 1))) hyf
  exact Nat.le_of_mul_le_mul_left h1 (Nat.pos_pow_of_pos (k + 1) (by decide))

/-! ## §5 — the calibration: real sign-dichotomy ⟹ LLPO

The corpus real type is `RealCut = Nat → Nat → Bool` (a cut function), so the
"real sign dichotomy" is exactly: for *every* such cut `x`, decide `x ≤ 1 ∨ 1 ≤ x`.
Because the construction lives in the corpus's non-negative-rational cuts, the
threshold is the constant `1` (`y_f = 1 + x_f`, the `+1`-shift of the
sign-at-`0` test); `cutLe x one` is "`x ≤ 1`" i.e. the shifted "`x_f ≤ 0`".

This is the precise reason the **exact** Intermediate Value Theorem / bisection's
"is `f(mid) ≤ 0` or `≥ 0`?" step is not ∅-axiom: that sign decision *is* this
dichotomy, and the dichotomy implies `LLPO` (an omniscience act).  The corpus's
*approximate* IVT (`cutEq … 0` root certificates) stays ∅-axiom precisely because
it never makes this exact decision. -/

/-- **Real sign dichotomy**: every corpus real (cut function) is `≤ 1` or `≥ 1`. -/
def RealDichotomy : Prop := ∀ x : Nat → Nat → Bool, cutLe x one ∨ cutLe one x

/-- ★★★ **The real sign dichotomy implies LLPO** — the analytic-LLPO calibration.
    Feed the dichotomy hypothesis the encoded real `y_f`; its sign decides the
    even/odd disjunction:
      `cutLe (yf f) one` ⟹ no even fire (`∀ k, f(2k) = false`);
      `cutLe one (yf f)` ⟹ no odd fire (`∀ k, f(2k+1) = false`).
    ∅-axiom: `RealDichotomy` is a `Prop` hypothesis, never an axiom. -/
theorem llpo_of_realDichotomy (hdich : RealDichotomy) : LLPO :=
  fun f hone =>
    (hdich (yf f)).elim
      (fun hle => Or.inl (noEvenFire_of_le f hone hle))
      (fun hge => Or.inr (noOddFire_of_ge f hone hge))

/-- **Encoded-real sign dichotomy** for a single at-most-one-true `f`. -/
def EncodedDichotomy (f : Nat → Bool) : Prop := cutLe (yf f) one ∨ cutLe one (yf f)

/-- ★★ **Converse (on the encoded reals): LLPO ⟹ the encoded dichotomy.**
    LLPO gives "no even fire" or "no odd fire"; each positively bounds the
    encoded value (≤ 1 resp. ≥ 1), yielding the corresponding `cutLe`.  Together
    with `llpo_of_realDichotomy` this is the two-sided calibration:
    *the encoded sign-decision is exactly LLPO*. -/
theorem encodedDichotomy_of_llpo (hllpo : LLPO) (f : Nat → Bool)
    (hone : ∀ m n, f m = true → f n = true → m = n) : EncodedDichotomy f :=
  (hllpo f hone).elim
    (fun hev => Or.inl (le_of_noEven f hev))
    (fun hod => Or.inr (ge_of_noOdd f hod))

end E213.Lib.Math.Logic.RealDichotomyLLPO
