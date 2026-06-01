import E213.Lib.Math.Cauchy.DepthExponentRecursion
import E213.Lib.Math.Cauchy.DepthDoubleExp
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# DepthClosure — the finite-coordinate class is closed under × and the exponent axis

A real, in the tower, is a divergence trajectory with a coordinate (its difference /
ratio depth).  `DepthExponentRecursion` showed the exponent axis lifts a difference
coordinate to a ratio coordinate one tier up (value-height = 1 + exponent-height).
This file proves the trajectories of *finite* coordinate form a class **closed** under
the tower's operations — the tower-native form of holonomic closure — and that the
closure **breaks** exactly at the exponential boundary (`DepthDoubleExp`).

The mechanism is the linearity of the difference operator.

  * `diffN_add` — `diff` is additive on monotone sequences, so every iterated
    difference distributes: `diffN d (e₁+e₂) = diffN d e₁ + diffN d e₂` (pointwise, no
    `funext`).  Hence:
  * ★ `finDiffDepth_add` — the finite-difference-depth class is closed under `+`
    (the floor of a sum is reached by the deeper of the two summands, `max d₁ d₂`).
  * ★ `expSeq_mul` — `c^{e₁+e₂} = c^{e₁}·c^{e₂}`: a sum of exponents is a **product** of
    values.  So closure of exponents under `+` is closure of the exponential values
    under `×`:
  * ★★★ `value_mul_closed` — the product of two finite-ratio-depth exponential values
    is again a finite-ratio-depth value (it is `c^{e₁+e₂}`).
  * ★★ `value_exp_closed` (`value_finRatio_of_finDiff`) — the exponent axis itself:
    a finite-difference-depth exponent yields a finite-ratio-depth value, one tier up.
  * ★★★ `exp_axis_breaks` — the boundary.  `twoPow = 2^n` is **not** of finite
    difference depth (`twoPow_not_finDiff`), and its value `2^{2^n}` has **no** finite
    ratio depth (`DepthDoubleExp.dexp_not_const`).  Closure under the exponent axis
    holds up to the boundary and fails at it.
  * ★★★ `rate_carrying_tower_closure` bundles the four.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthClosure

open E213.Lib.Math.Cauchy.DivergenceLadder (diff isConst)
open E213.Lib.Math.Cauchy.DepthTower (diffN ratioN)
open E213.Lib.Math.Cauchy.DepthExponentRecursion
  (expSeq totMono value_floor_of_exponent_floor)
open E213.Lib.Math.Cauchy.DepthDoubleExp (twoPow diffN_twoPow dexp_not_const)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Tactic.NatHelper (add_sub_add_of_le le_max_left le_max_right)

/-! ## §1 — `diff` is additive on monotone sequences -/

/-- A forward difference of a sum splits on monotone summands:
    `diff (e₁+e₂) n = diff e₁ n + diff e₂ n`. -/
theorem diff_add (e₁ e₂ : Nat → Nat) (h₁ : ∀ n, e₁ n ≤ e₁ (n+1))
    (h₂ : ∀ n, e₂ n ≤ e₂ (n+1)) (n : Nat) :
    diff (fun m => e₁ m + e₂ m) n = diff e₁ n + diff e₂ n := by
  show (e₁ (n+1) + e₂ (n+1)) - (e₁ n + e₂ n) = (e₁ (n+1) - e₁ n) + (e₂ (n+1) - e₂ n)
  exact add_sub_add_of_le (h₁ n) (h₂ n)

/-- ★ **Every iterated difference distributes over a sum** of totally-monotone
    sequences: `diffN d (e₁+e₂) n = diffN d e₁ n + diffN d e₂ n` (pointwise). -/
theorem diffN_add (e₁ e₂ : Nat → Nat) (htm₁ : totMono e₁) (htm₂ : totMono e₂) :
    ∀ d n, diffN d (fun m => e₁ m + e₂ m) n = diffN d e₁ n + diffN d e₂ n := by
  intro d
  induction d with
  | zero => intro n; rfl
  | succ d ih =>
    intro n
    show diffN d (fun m => e₁ m + e₂ m) (n+1) - diffN d (fun m => e₁ m + e₂ m) n
       = (diffN d e₁ (n+1) - diffN d e₁ n) + (diffN d e₂ (n+1) - diffN d e₂ n)
    rw [ih (n+1), ih n]
    exact add_sub_add_of_le (htm₁ d n) (htm₂ d n)

/-- Total monotonicity is preserved under `+`. -/
theorem totMono_add (e₁ e₂ : Nat → Nat) (htm₁ : totMono e₁) (htm₂ : totMono e₂) :
    totMono (fun m => e₁ m + e₂ m) := by
  intro j n
  rw [diffN_add e₁ e₂ htm₁ htm₂ j n, diffN_add e₁ e₂ htm₁ htm₂ j (n+1)]
  exact Nat.add_le_add (htm₁ j n) (htm₂ j n)

/-! ## §2 — the index algebra of `diffN`, and "floors stay floored" -/

/-- `diffN (a+b) s = diffN a (diffN b s)` (pointwise). -/
theorem diffN_index_add : ∀ (a b : Nat) (s : Nat → Nat) (n : Nat),
    diffN (a + b) s n = diffN a (diffN b s) n
  | 0,   b, s, n => by rw [Nat.zero_add]; rfl
  | a+1, b, s, n => by
    rw [Nat.succ_add]
    show diffN (a+b) s (n+1) - diffN (a+b) s n
       = diffN a (diffN b s) (n+1) - diffN a (diffN b s) n
    rw [diffN_index_add a b s (n+1), diffN_index_add a b s n]

/-- One difference of a constant sequence is constant (the zero sequence). -/
theorem isConst_diff (s : Nat → Nat) (h : isConst s) : isConst (diff s) := by
  intro n
  show s (n+1) - s n = s (0+1) - s 0
  rw [h (n+1), h n, h (0+1), h 0]

/-- Any number of differences of a constant sequence stay constant. -/
theorem isConst_diffN (s : Nat → Nat) (h : isConst s) : ∀ t, isConst (diffN t s)
  | 0   => h
  | t+1 => isConst_diff (diffN t s) (isConst_diffN s h t)

/-- Once the `d`-th difference is constant, every deeper difference is too. -/
theorem floor_up (e : Nat → Nat) (d d' : Nat) (hd : d ≤ d')
    (h : isConst (diffN d e)) : isConst (diffN d' e) := by
  obtain ⟨t, ht⟩ := Nat.le.dest hd
  subst ht
  intro n
  have hc := isConst_diffN (diffN d e) h t
  have ea : ∀ m, diffN (d + t) e m = diffN t (diffN d e) m := by
    intro m; rw [Nat.add_comm d t]; exact diffN_index_add t d e m
  rw [ea n, ea 0]; exact hc n

/-! ## §3 — finite difference depth, closed under `+` -/

/-- A sequence has **finite difference depth** if some iterated difference is constant
    (a finite coordinate on the difference axis). -/
def FinDiffDepth (e : Nat → Nat) : Prop := ∃ d, isConst (diffN d e)

/-- ★ **Closure of the finite-difference-depth class under `+`.**  The sum of two
    finite-depth sequences floors at the deeper depth `max d₁ d₂`. -/
theorem finDiffDepth_add (e₁ e₂ : Nat → Nat) (htm₁ : totMono e₁) (htm₂ : totMono e₂)
    (h₁ : FinDiffDepth e₁) (h₂ : FinDiffDepth e₂) :
    FinDiffDepth (fun m => e₁ m + e₂ m) := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  refine ⟨Nat.max d₁ d₂, ?_⟩
  have f₁ := floor_up e₁ d₁ (Nat.max d₁ d₂) (le_max_left d₁ d₂) hd₁
  have f₂ := floor_up e₂ d₂ (Nat.max d₁ d₂) (le_max_right d₁ d₂) hd₂
  intro n
  rw [diffN_add e₁ e₂ htm₁ htm₂ (Nat.max d₁ d₂) n,
      diffN_add e₁ e₂ htm₁ htm₂ (Nat.max d₁ d₂) 0, f₁ n, f₂ n]

/-! ## §4 — the value side: × closure and the exponent axis -/

/-- A value has **finite ratio depth** if some iterated ratio-lift is constant. -/
def FinRatioDepth (v : Nat → Nat) : Prop := ∃ h, isConst (ratioN h v)

/-- ★ A sum of exponents is a product of values: `c^{e₁+e₂} = c^{e₁}·c^{e₂}`. -/
theorem expSeq_mul (c : Nat) (e₁ e₂ : Nat → Nat) (n : Nat) :
    expSeq c (fun m => e₁ m + e₂ m) n = expSeq c e₁ n * expSeq c e₂ n :=
  pow_add c (e₁ n) (e₂ n)

/-- ★★ **The exponent axis is closed up to the boundary.**  A finite-difference-depth
    exponent yields a finite-ratio-depth value — the value sits one axis above its
    exponent (`value_floor_of_exponent_floor`). -/
theorem value_finRatio_of_finDiff (c : Nat) (hc : 1 ≤ c) (e : Nat → Nat)
    (htm : totMono e) (h : FinDiffDepth e) : FinRatioDepth (expSeq c e) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, value_floor_of_exponent_floor c hc e htm d hd⟩

/-- ★★★ **The exponential-value class is closed under `×`.**  The product of two
    finite-ratio-depth values `c^{e₁}·c^{e₂}` is itself a finite-ratio-depth value,
    because it equals `c^{e₁+e₂}` and the exponent sum stays finite-difference-depth
    (`finDiffDepth_add`).  So φ, e, and any finite-coordinate real generate a whole
    family under multiplication, for free. -/
theorem value_mul_closed (c : Nat) (hc : 1 ≤ c) (e₁ e₂ : Nat → Nat)
    (htm₁ : totMono e₁) (htm₂ : totMono e₂)
    (h₁ : FinDiffDepth e₁) (h₂ : FinDiffDepth e₂) :
    FinRatioDepth (expSeq c (fun m => e₁ m + e₂ m))
    ∧ (∀ n, expSeq c (fun m => e₁ m + e₂ m) n = expSeq c e₁ n * expSeq c e₂ n) :=
  ⟨value_finRatio_of_finDiff c hc _ (totMono_add e₁ e₂ htm₁ htm₂)
      (finDiffDepth_add e₁ e₂ htm₁ htm₂ h₁ h₂),
   expSeq_mul c e₁ e₂⟩

/-! ## §5 — the boundary: the exponent axis breaks at the exponential -/

/-- `twoPow = 2^n` has **no** finite difference depth — every difference fixes it
    (`diffN_twoPow`) and it is not constant (`2^1 ≠ 2^0`). -/
theorem twoPow_not_finDiff : ¬ FinDiffDepth twoPow := by
  rintro ⟨d, hd⟩
  have h := hd 1
  rw [diffN_twoPow d 1, diffN_twoPow d 0] at h
  exact absurd h (by decide)

/-- ★★★ **The exponent axis closure breaks at the boundary.**  The double exponential
    `2^{2^n}` — whose exponent `2^n` is itself *not* of finite difference depth — has
    **no** finite ratio depth (`DepthDoubleExp.dexp_not_const`).  Closure under the
    exponent axis holds for finite-coordinate exponents and fails exactly at the
    exponential exponent. -/
theorem exp_axis_breaks : ¬ FinRatioDepth (expSeq 2 twoPow) := by
  rintro ⟨h, hh⟩
  exact dexp_not_const h hh

/-! ## §6 — the closure, bundled -/

/-- ★★★ **Tower-native closure of the rate-carrying (finite-coordinate) class.**
    Closed under `×` (product of values = exponent of a sum, still finite ratio depth)
    and under the exponent axis (finite difference depth ⟹ finite ratio depth, one
    tier up), and the exponent-axis closure breaks exactly at the exponential boundary
    (`twoPow` is not finite difference depth, `2^{2^n}` is not finite ratio depth).
    This is holonomic closure made internal to the resolution tower, with the
    boundary the same `2^{2^n}` of the overtake layer. -/
theorem rate_carrying_tower_closure :
    (∀ c, 1 ≤ c → ∀ e₁ e₂, totMono e₁ → totMono e₂ →
        FinDiffDepth e₁ → FinDiffDepth e₂ →
        FinRatioDepth (expSeq c (fun m => e₁ m + e₂ m)))
    ∧ (∀ c, 1 ≤ c → ∀ e, totMono e → FinDiffDepth e → FinRatioDepth (expSeq c e))
    ∧ ¬ FinDiffDepth twoPow
    ∧ ¬ FinRatioDepth (expSeq 2 twoPow) :=
  ⟨fun c hc e₁ e₂ h₁ h₂ f₁ f₂ => (value_mul_closed c hc e₁ e₂ h₁ h₂ f₁ f₂).1,
   value_finRatio_of_finDiff,
   twoPow_not_finDiff,
   exp_axis_breaks⟩

end E213.Lib.Math.Cauchy.DepthClosure
