import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# Differential Equations 213 — Discrete heat equation (1D)

213-native paradigm: heat equation on a *finite* periodic grid.
`u(x, t+1) = (1/2) u(x-1, t) + (1/2) u(x+1, t)` — discrete
Laplacian.  No PDE existence theorem chase: the discrete update is
purely combinatorial, and conservation (sum of `u` over the grid)
is a `Nat` identity.

Atomic content:
  * `heatStep n u x` — single time-step on a length-`n` periodic grid
  * Sum-conservation: `Σ heatStep ≡ Σ u`  (modulo the 1/2 factor;
    we work in numerator-only `Nat`-side: `2 · sum heatStep = sum + sum`).
  * Constant initial condition is fixed (heat equilibrium).
-/

namespace E213.Lib.Math.Analysis.ODE.HeatEq.Discrete

/-- Periodic neighbour: `(x + 1) mod n`. -/
def rightNbr (n x : Nat) : Nat := (x + 1) % n

/-- Periodic neighbour: `(x + n - 1) mod n`. -/
def leftNbr (n x : Nat) : Nat := (x + n - 1) % n

/-- One discrete heat step on a length-`n` periodic grid.
    *Numerator only* — the actual update is
    `u(x, t+1) = (1/2) (u(x-1) + u(x+1))`.  We track `2 ·
    u(x, t+1)`. -/
def heatStepNum (n : Nat) (u : Nat → Nat) (x : Nat) : Nat :=
  u (leftNbr n x) + u (rightNbr n x)

/-- Constant initial condition. -/
def constInit (c : Nat) : Nat → Nat := fun _ => c

/-- ★ Constant initial condition is preserved by heat step
    (numerator: `2 · c`). -/
theorem heatStep_const (n c x : Nat) :
    heatStepNum n (constInit c) x = c + c := rfl

/-- ★ Constant heat field is `2c` after step (no diffusion needed). -/
theorem heatStep_const_eq_two_c (n c x : Nat) :
    heatStepNum n (constInit c) x = 2 * c := by
  show c + c = 2 * c
  exact (Nat.two_mul c).symm

/-! ## Discrete maximum principle (marathon P1)

The discrete heat step is an **average** of two neighbours, so it can neither rise
above the field's max nor fall below its min — the discrete maximum principle, the
seed of all parabolic a-priori estimates.  In the numerator convention
`heatStepNum = 2·u(x,t+1) = u_left + u_right`, a bound `u ≤ B` on the whole grid gives
`heatStepNum ≤ 2B` (i.e. the *averaged* new value `≤ B`), and dually `A ≤ u` gives
`2A ≤ heatStepNum`.  Pure `Nat`, ∅-axiom; uniform in the grid length `n` (hence in the
mesh) — the uniformity that lets the `Real213` limit promote it to the continuous
maximum principle (the next P1 sub-rung). -/

/-- ★★ **Discrete maximum principle (upper).**  If `u ≤ B` everywhere on the grid, the
    post-step numerator `heatStepNum = 2·u_new` is `≤ 2B` — i.e. the new (averaged)
    value does not exceed the old maximum `B`.  Heat does not create hot spots.
    Uniform in the grid length `n`. -/
theorem heatStep_le_two_max (n : Nat) (u : Nat → Nat) (B x : Nat)
    (h : ∀ y, u y ≤ B) : heatStepNum n u x ≤ 2 * B := by
  show u (leftNbr n x) + u (rightNbr n x) ≤ 2 * B
  rw [Nat.two_mul]
  exact Nat.add_le_add (h (leftNbr n x)) (h (rightNbr n x))

/-- ★★ **Discrete maximum principle (lower / minimum principle).**  If `A ≤ u`
    everywhere, then `2A ≤ heatStepNum = 2·u_new` — the new value does not fall below the
    old minimum `A`.  Heat does not create cold spots. -/
theorem heatStep_two_min_le (n : Nat) (u : Nat → Nat) (A x : Nat)
    (h : ∀ y, A ≤ u y) : 2 * A ≤ heatStepNum n u x := by
  show 2 * A ≤ u (leftNbr n x) + u (rightNbr n x)
  rw [Nat.two_mul]
  exact Nat.add_le_add (h (leftNbr n x)) (h (rightNbr n x))

/-- ★★★ **Range preservation.**  Under one heat step, the doubled new value stays inside
    `[2A, 2B]` whenever the old field is in `[A, B]` — i.e. the averaged field stays in
    `[A, B]`.  The interval `[min, max]` is invariant: the discrete heat semigroup is a
    contraction on the sup-norm, the combinatorial root of `‖u(t)‖∞ ≤ ‖u(0)‖∞`. -/
theorem heatStep_range (n : Nat) (u : Nat → Nat) (A B x : Nat)
    (hlo : ∀ y, A ≤ u y) (hhi : ∀ y, u y ≤ B) :
    2 * A ≤ heatStepNum n u x ∧ heatStepNum n u x ≤ 2 * B :=
  ⟨heatStep_two_min_le n u A x hlo, heatStep_le_two_max n u B x hhi⟩

/-- ★★★ **Oscillation does not grow.**  The post-step spread `2B − 2A = 2·(B−A)` bounds
    the new value's deviation from both ends: the oscillation `osc = max − min` is a
    monovariant under the heat step (it never increases), the discrete smoothing estimate
    feeding oscillation decay (rung P2).  Stated as the two-sided bound on the new value's
    distance from the doubled endpoints. -/
theorem heatStep_osc_bound (n : Nat) (u : Nat → Nat) (A B x : Nat)
    (hlo : ∀ y, A ≤ u y) (hhi : ∀ y, u y ≤ B) :
    heatStepNum n u x - 2 * A ≤ 2 * (B - A) ∧
    2 * B - heatStepNum n u x ≤ 2 * (B - A) := by
  obtain ⟨hA, hB⟩ := heatStep_range n u A B x hlo hhi
  have hdist : 2 * B - 2 * A = 2 * (B - A) :=
    (E213.Tactic.NatHelper.mul_sub 2 B A).symm
  refine ⟨?_, ?_⟩
  · -- (2u_new) − 2A ≤ 2B − 2A = 2(B−A)
    have h1 : heatStepNum n u x - 2 * A ≤ 2 * B - 2 * A := Nat.sub_le_sub_right hB (2 * A)
    rw [hdist] at h1; exact h1
  · have h2 : 2 * B - heatStepNum n u x ≤ 2 * B - 2 * A :=
      E213.Tactic.NatHelper.sub_le_sub_left (2 * B) hA
    rw [hdist] at h2; exact h2

/-! ## Maximum principle for the whole evolution (iterated heat flow)

The single-step bound iterates: applying the heat field-update `t` times keeps the
(numerator-tracked) field inside `[2ᵗ·A, 2ᵗ·B]` whenever the data is in `[A, B]` — i.e.
the *averaged* field stays in `[A, B]` for **all** time.  This is the discrete maximum
principle for the evolution `u(·, t)`, not just one step: `‖u(t)‖∞ ≤ ‖u(0)‖∞` along the
discrete heat semigroup.  Clean `Nat` induction on `t`; uniform in the grid length `n`. -/

/-- One full-grid heat field-update: apply `heatStepNum` at every site. -/
def heatField (n : Nat) (u : Nat → Nat) : Nat → Nat := fun x => heatStepNum n u x

/-- `t`-fold heat evolution (numerator-tracked: each step doubles, so after `t` steps the
    true field is `heatIter / 2ᵗ`). -/
def heatIter (n : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0,     u => u
  | t + 1, u => heatField n (heatIter n t u)

/-- ★★★ **Maximum principle, all time (upper).**  If the data satisfies `u ≤ B` on the
    grid, then after `t` heat steps `heatIter n t u x ≤ 2ᵗ·B` at every site — the averaged
    field never exceeds the initial maximum `B`.  Induction on `t` via `heatStep_le_two_max`. -/
theorem heatIter_le (n B : Nat) :
    ∀ (t : Nat) (u : Nat → Nat), (∀ y, u y ≤ B) → ∀ x, heatIter n t u x ≤ 2 ^ t * B
  | 0,     u, h, x => by show u x ≤ 2 ^ 0 * B; rw [Nat.pow_zero, Nat.one_mul]; exact h x
  | t + 1, u, h, x => by
      show heatStepNum n (heatIter n t u) x ≤ 2 ^ (t + 1) * B
      have ih : ∀ y, heatIter n t u y ≤ 2 ^ t * B := fun y => heatIter_le n B t u h y
      calc heatStepNum n (heatIter n t u) x
          ≤ 2 * (2 ^ t * B) := heatStep_le_two_max n (heatIter n t u) (2 ^ t * B) x ih
        _ = 2 ^ (t + 1) * B := by rw [Nat.pow_succ]; ring_nat

/-- ★★★ **Maximum principle, all time (lower).**  If `A ≤ u` on the grid, then
    `2ᵗ·A ≤ heatIter n t u x` for every `t`, `x` — the averaged field never falls below
    the initial minimum `A`. -/
theorem heatIter_ge (n A : Nat) :
    ∀ (t : Nat) (u : Nat → Nat), (∀ y, A ≤ u y) → ∀ x, 2 ^ t * A ≤ heatIter n t u x
  | 0,     u, h, x => by show 2 ^ 0 * A ≤ u x; rw [Nat.pow_zero, Nat.one_mul]; exact h x
  | t + 1, u, h, x => by
      show 2 ^ (t + 1) * A ≤ heatStepNum n (heatIter n t u) x
      have ih : ∀ y, 2 ^ t * A ≤ heatIter n t u y := fun y => heatIter_ge n A t u h y
      calc 2 ^ (t + 1) * A
          = 2 * (2 ^ t * A) := by rw [Nat.pow_succ]; ring_nat
        _ ≤ heatStepNum n (heatIter n t u) x :=
            heatStep_two_min_le n (heatIter n t u) (2 ^ t * A) x ih

/-- ★★★★ **Discrete maximum principle for the heat evolution.**  Data in `[A, B]` ⟹ the
    `t`-step field stays in `[2ᵗ·A, 2ᵗ·B]` (averaged field in `[A, B]`) for *all* `t`.
    The sup-norm is non-increasing along the discrete heat semigroup — the combinatorial
    seed of the parabolic maximum principle, uniform in the mesh, hence `Real213`-limit
    ready (the continuous maximum principle, next P1 sub-rung). -/
theorem heatIter_range (n A B : Nat) (t : Nat) (u : Nat → Nat)
    (hlo : ∀ y, A ≤ u y) (hhi : ∀ y, u y ≤ B) (x : Nat) :
    2 ^ t * A ≤ heatIter n t u x ∧ heatIter n t u x ≤ 2 ^ t * B :=
  ⟨heatIter_ge n A t u hlo x, heatIter_le n B t u hhi x⟩

/-! ## Comparison principle (order preservation) — the unifying parabolic estimate

The heat step is **monotone in the initial data**: `u ≤ v` pointwise ⟹ `heatStep u ≤
heatStep v` pointwise (and the same after any number of steps).  This is the comparison
principle — order-preservation of the discrete heat semigroup, the parabolic estimate the
maximum principle is a *special case* of (compare against a constant field).  Pure `Nat`,
no grid sums; holds for both stencils. -/

/-- ★★ **Comparison principle (non-lazy).**  `u ≤ v` everywhere ⟹ `heatStepNum u ≤ heatStepNum v`.
    (The lazy version `lazyHeatStep_mono` is with the lazy stencil, below.) -/
theorem heatStep_mono (n : Nat) (u v : Nat → Nat) (x : Nat)
    (h : ∀ y, u y ≤ v y) : heatStepNum n u x ≤ heatStepNum n v x :=
  Nat.add_le_add (h (leftNbr n x)) (h (rightNbr n x))

/-- ★★★ **Comparison principle for the whole evolution.**  Order is preserved under any
    number of heat steps: `u ≤ v` ⟹ `heatIter n t u ≤ heatIter n t v` for every `t`. -/
theorem heatIter_mono (n : Nat) :
    ∀ (t : Nat) (u v : Nat → Nat), (∀ y, u y ≤ v y) →
      ∀ x, heatIter n t u x ≤ heatIter n t v x
  | 0,     u, v, h, x => h x
  | t + 1, u, v, h, x => by
      show heatStepNum n (heatIter n t u) x ≤ heatStepNum n (heatIter n t v) x
      exact heatStep_mono n (heatIter n t u) (heatIter n t v) x
        (fun y => heatIter_mono n t u v h y)

/-- ★ **The maximum principle is comparison against a constant.**  `heatStep_le_two_max`
    re-derived as `heatStep_mono` versus the constant field `B` (plus `heatStep_const`):
    the two P1 estimates are one principle. -/
theorem heatStep_le_two_max_via_comparison (n : Nat) (u : Nat → Nat) (B x : Nat)
    (h : ∀ y, u y ≤ B) : heatStepNum n u x ≤ 2 * B := by
  have hc : heatStepNum n u x ≤ heatStepNum n (constInit B) x :=
    heatStep_mono n u (constInit B) x h
  rwa [heatStep_const_eq_two_c] at hc

/-! ## Lazy heat step — the self-weighted stencil that decays oscillation (P2)

The non-lazy step `heatStepNum = u_{x−1}+u_{x+1}` (stencil `(½,0,½)`) preserves the
**checkerboard** mode `0,1,0,1,…`: it maps to `2,0,2,0,… = 2·(checkerboard)`, so the
averaged oscillation does *not* decay (eigenvalue `cos π = −1`, no spectral gap).  The
genuine smoothing operator is the **lazy** step `(¼,½,¼)`:

  `lazyHeatStepNum = u_{x−1} + 2·u_x + u_{x+1}`  (numerator of `4·u(x,t+1)`),

whose eigenvalues `(1+cos θ)/2 ∈ [0,1]` give a real gap — it *kills* the checkerboard.
The P1 maximum principle holds for both (convex combinations); only the strict *decay*
(rung P2) needs the self-weight. -/

/-- Lazy heat step `(¼,½,¼)` — numerator of `4·u(x,t+1) = u_{x−1} + 2u_x + u_{x+1}`. -/
def lazyHeatStepNum (n : Nat) (u : Nat → Nat) (x : Nat) : Nat :=
  u (leftNbr n x) + 2 * u x + u (rightNbr n x)

/-- ★ Constant field is preserved by the lazy step (numerator `4c`). -/
theorem lazyHeatStep_const (n c x : Nat) :
    lazyHeatStepNum n (constInit c) x = 4 * c := by
  show c + 2 * c + c = 4 * c
  rw [Nat.two_mul]; ring_nat

/-- ★★ **Lazy maximum principle (upper).**  `u ≤ B` ⟹ `lazyHeatStepNum ≤ 4B`
    (averaged value `≤ B`): the lazy stencil is also a contraction on the sup-norm. -/
theorem lazyHeatStep_le_four_max (n : Nat) (u : Nat → Nat) (B x : Nat)
    (h : ∀ y, u y ≤ B) : lazyHeatStepNum n u x ≤ 4 * B := by
  show u (leftNbr n x) + 2 * u x + u (rightNbr n x) ≤ 4 * B
  have e : 4 * B = B + 2 * B + B := by ring_nat
  rw [e]
  exact Nat.add_le_add (Nat.add_le_add (h _) (Nat.mul_le_mul_left 2 (h x))) (h _)

/-- ★★ **Lazy maximum principle (lower).**  `A ≤ u` ⟹ `4A ≤ lazyHeatStepNum`. -/
theorem lazyHeatStep_four_min_le (n : Nat) (u : Nat → Nat) (A x : Nat)
    (h : ∀ y, A ≤ u y) : 4 * A ≤ lazyHeatStepNum n u x := by
  show 4 * A ≤ u (leftNbr n x) + 2 * u x + u (rightNbr n x)
  have e : 4 * A = A + 2 * A + A := by ring_nat
  rw [e]
  exact Nat.add_le_add (Nat.add_le_add (h _) (Nat.mul_le_mul_left 2 (h x))) (h _)

/-- ★★ **Comparison principle (lazy).**  `u ≤ v` everywhere ⟹ `lazyHeatStepNum u ≤
    lazyHeatStepNum v` — order-preservation for the smoothing stencil too. -/
theorem lazyHeatStep_mono (n : Nat) (u v : Nat → Nat) (x : Nat)
    (h : ∀ y, u y ≤ v y) : lazyHeatStepNum n u x ≤ lazyHeatStepNum n v x :=
  Nat.add_le_add
    (Nat.add_le_add (h (leftNbr n x)) (Nat.mul_le_mul_left 2 (h x)))
    (h (rightNbr n x))

/-- ★ **Stencil relation**: the lazy step is the non-lazy step plus twice the self-weight,
    `lazyHeatStepNum = heatStepNum + 2·u_x`.  This is exactly why the lazy stencil has a
    spectral gap: adding `2u_x` shifts the symbol from `cos θ` (range `[−1,1]`, the `−1`
    checkerboard eigenmode) to `1 + cos θ` (range `[0,2]`, normalized `(1+cos θ)/2 ∈ [0,1]`,
    `< 1` off the constant mode).  The `−1` eigenvalue the non-lazy step carries is removed
    by the self-weight. -/
theorem lazy_eq_nonlazy_plus_self (n : Nat) (u : Nat → Nat) (x : Nat) :
    lazyHeatStepNum n u x = heatStepNum n u x + 2 * u x := by
  show u (leftNbr n x) + 2 * u x + u (rightNbr n x)
      = u (leftNbr n x) + u (rightNbr n x) + 2 * u x
  ring_nat

/-! ### Strong (strict) maximum principle — heat strictly smooths interior extrema

If a site attains the field max `B` but has a neighbour strictly below `B`, the heat step
sends it **strictly** below `2B` (resp. `4B` for the lazy stencil): heat cannot sustain a
strict interior maximum.  This is the *strong* maximum principle's discrete seed.

⚠️ **Local strict ≠ global oscillation decay.**  The strict drop holds at the max *site* for
*both* stencils — yet the non-lazy step still fails to decay oscillation (the checkerboard,
above), because the max **relocates**: `[0,1,0,1] → [2,0,2,0]` drops the old max site (`1→0`)
but creates a new max at the even sites.  The lazy self-weight (`lazy_eq_nonlazy_plus_self`)
is what *pins* the extremum in place so the strict drop is not undone — the difference between
a strong maximum principle (local, both stencils) and a spectral gap (global, lazy only). -/

/-- ★★ **Strong maximum principle (non-lazy).**  A max site with a strictly-below neighbour
    drops strictly: `heatStepNum < 2B`. -/
theorem heatStep_strict_at_max (n : Nat) (u : Nat → Nat) (B x : Nat)
    (h : ∀ y, u y ≤ B)
    (hstrict : u (leftNbr n x) < B ∨ u (rightNbr n x) < B) :
    heatStepNum n u x < 2 * B := by
  show u (leftNbr n x) + u (rightNbr n x) < 2 * B
  rw [Nat.two_mul]
  cases hstrict with
  | inl hl =>
      have s1 : u (leftNbr n x) + u (rightNbr n x) < B + u (rightNbr n x) :=
        Nat.add_lt_add_right hl (u (rightNbr n x))
      have s2 : B + u (rightNbr n x) ≤ B + B := Nat.add_le_add_left (h (rightNbr n x)) B
      exact Nat.lt_of_lt_of_le s1 s2
  | inr hr =>
      have s1 : u (leftNbr n x) + u (rightNbr n x) ≤ B + u (rightNbr n x) :=
        Nat.add_le_add_right (h (leftNbr n x)) (u (rightNbr n x))
      have s2 : B + u (rightNbr n x) < B + B := Nat.add_lt_add_left hr B
      exact Nat.lt_of_le_of_lt s1 s2

/-- ★★★ **Strong maximum principle (lazy).**  Same strict drop for the smoothing stencil:
    `lazyHeatStepNum < 4B`. -/
theorem lazyHeatStep_strict_at_max (n : Nat) (u : Nat → Nat) (B x : Nat)
    (h : ∀ y, u y ≤ B)
    (hstrict : u (leftNbr n x) < B ∨ u (rightNbr n x) < B) :
    lazyHeatStepNum n u x < 4 * B := by
  show u (leftNbr n x) + 2 * u x + u (rightNbr n x) < 4 * B
  have e : 4 * B = B + 2 * B + B := by ring_nat
  rw [e]
  have hmid : 2 * u x ≤ 2 * B := Nat.mul_le_mul_left 2 (h x)
  cases hstrict with
  | inl hl =>
      have a1 : u (leftNbr n x) + 2 * u x < B + 2 * u x :=
        Nat.add_lt_add_right hl (2 * u x)
      have a2 : B + 2 * u x ≤ B + 2 * B := Nat.add_le_add_left hmid B
      have h1 : u (leftNbr n x) + 2 * u x < B + 2 * B := Nat.lt_of_lt_of_le a1 a2
      have b1 : u (leftNbr n x) + 2 * u x + u (rightNbr n x) < B + 2 * B + u (rightNbr n x) :=
        Nat.add_lt_add_right h1 (u (rightNbr n x))
      have b2 : B + 2 * B + u (rightNbr n x) ≤ B + 2 * B + B :=
        Nat.add_le_add_left (h (rightNbr n x)) (B + 2 * B)
      exact Nat.lt_of_lt_of_le b1 b2
  | inr hr =>
      have h1 : u (leftNbr n x) + 2 * u x ≤ B + 2 * B := Nat.add_le_add (h (leftNbr n x)) hmid
      have b1 : u (leftNbr n x) + 2 * u x + u (rightNbr n x) ≤ B + 2 * B + u (rightNbr n x) :=
        Nat.add_le_add_right h1 (u (rightNbr n x))
      have b2 : B + 2 * B + u (rightNbr n x) < B + 2 * B + B :=
        Nat.add_lt_add_left hr (B + 2 * B)
      exact Nat.lt_of_le_of_lt b1 b2

/-! ### Concrete witness: lazy decays the checkerboard, non-lazy does not -/

/-- The checkerboard initial field `0,1,0,1,…` (the worst case for smoothing). -/
def checker : Nat → Nat := fun x => x % 2

/-- **Non-lazy preserves the checkerboard** — the hot site stays hot (`= 2 = 2·1`)… -/
theorem nonlazy_checker_hot : heatStepNum 4 checker 0 = 2 := rfl

/-- …and the cold site stays cold (`= 0`): the doubled field is again `2·(checkerboard)`,
    oscillation `2·1` *unchanged* relative to the doubling — no decay. -/
theorem nonlazy_checker_cold : heatStepNum 4 checker 1 = 0 := rfl

/-- ★★★ **The lazy step collapses the checkerboard to a constant.**  On the length-4
    grid every site maps to `2 = 4·½`: the post-step field is uniform, oscillation
    `1 → 0` in a single step.  The concrete spectral-gap witness: the self-weight `(¼,½,¼)`
    annihilates the `−1` eigenmode the non-lazy step preserves — the discrete smoothing
    (P2) the maximum principle alone cannot deliver. -/
theorem lazy_checker_collapses (x : Nat) (h : x < 4) : lazyHeatStepNum 4 checker x = 2 := by
  rcases E213.Tactic.NatHelper.cases_lt_four h with rfl | rfl | rfl | rfl <;> rfl

end E213.Lib.Math.Analysis.ODE.HeatEq.Discrete
