import E213.Meta.Int213
import E213.Meta.Int213.PolyIntMTactic

/-!
# Ollivier–Ricci curvature — A6 core, rung 5 (∅-axiom)

The last discrete-curvature rung: **Ollivier–Ricci** curvature, defined by *optimal transport*
`κ(x,y) = 1 − W₁(m_x, m_y)/d(x,y)` (`m_x` the one-step random-walk measure at `x`, `W₁` the
Wasserstein-1 / earth-mover distance).  The mathematical heart is **Kantorovich duality**: `W₁` is
both a `min` over transport plans (couplings) and a `max` over `1`-Lipschitz potentials.  This file
proves the **weak-duality** direction — every dual-feasible potential value is `≤` every coupling's
cost — which is what pins `W₁` (and hence `κ`) when a coupling and a potential meet.

Worked over ℤ on a finite index set `{0,…,n−1}` (signed potentials/costs).  Infrastructure: an
integer grid sum `gridSumZ` + Fubini (sum-swap).  All zero-axiom.

A6 discrete Ricci-flow ladder, rung 5.
-/

namespace E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci

open E213.Meta.Int213

/-! ## §1 — integer grid sum -/

/-- `gridSumZ n f = Σ_{x<n} f x` over ℤ. -/
def gridSumZ : Nat → (Nat → Int) → Int
  | 0,     _ => 0
  | n + 1, f => gridSumZ n f + f n

theorem gridSumZ_succ (n : Nat) (f : Nat → Int) :
    gridSumZ (n + 1) f = gridSumZ n f + f n := rfl

theorem gridSumZ_congr (n : Nat) (f g : Nat → Int) (h : ∀ x, x < n → f x = g x) :
    gridSumZ n f = gridSumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [gridSumZ_succ, gridSumZ_succ, h m (Nat.lt_succ_self m),
        ih (fun x hx => h x (Nat.lt_succ_of_lt hx))]

/-- The zero function sums to `0`. -/
theorem gridSumZ_zero_fn : ∀ n, gridSumZ n (fun _ => (0 : Int)) = 0
  | 0 => rfl
  | n + 1 => by show gridSumZ n (fun _ => 0) + 0 = 0; rw [gridSumZ_zero_fn n, Int.add_zero]

theorem gridSumZ_add (n : Nat) (f g : Nat → Int) :
    gridSumZ n (fun x => f x + g x) = gridSumZ n f + gridSumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show gridSumZ m (fun x => f x + g x) + (f m + g m)
        = (gridSumZ m f + f m) + (gridSumZ m g + g m)
    rw [ih]; ring_intZ

/-- Pull a scalar out: `Σ (c · f) = c · Σ f`. -/
theorem gridSumZ_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    gridSumZ n (fun x => c * f x) = c * gridSumZ n f := by
  induction n with
  | zero => show (0 : Int) = c * 0; rw [Int.mul_zero]
  | succ m ih => show gridSumZ m (fun x => c * f x) + c * f m = c * (gridSumZ m f + f m)
                 rw [ih]; ring_intZ

/-- Monotonicity: pointwise `f ≤ g` ⟹ `Σ f ≤ Σ g`. -/
theorem gridSumZ_le (n : Nat) (f g : Nat → Int) (h : ∀ x, x < n → f x ≤ g x) :
    gridSumZ n f ≤ gridSumZ n g := by
  induction n with
  | zero => exact Order.le_refl 0
  | succ m ih =>
    rw [gridSumZ_succ, gridSumZ_succ]
    exact Order.le_trans
      (Order.add_le_add_right (ih (fun x hx => h x (Nat.lt_succ_of_lt hx))) (f m))
      (Order.add_le_add_left (h m (Nat.lt_succ_self m)) (gridSumZ m g))

/-- **Fubini**: `Σ_x Σ_y g x y = Σ_y Σ_x g x y`. -/
theorem gridSumZ_fubini (n m : Nat) (g : Nat → Nat → Int) :
    gridSumZ n (fun x => gridSumZ m (fun y => g x y))
      = gridSumZ m (fun y => gridSumZ n (fun x => g x y)) := by
  induction n with
  | zero =>
    show (0 : Int) = gridSumZ m (fun y => gridSumZ 0 (fun x => g x y))
    rw [gridSumZ_congr m (fun y => gridSumZ 0 (fun x => g x y)) (fun _ => 0) (fun _ _ => rfl),
        gridSumZ_zero_fn m]
  | succ p ih =>
    show gridSumZ p (fun x => gridSumZ m (fun y => g x y)) + gridSumZ m (fun y => g p y)
        = gridSumZ m (fun y => gridSumZ (p + 1) (fun x => g x y))
    rw [ih,
        gridSumZ_congr m (fun y => gridSumZ (p + 1) (fun x => g x y))
          (fun y => gridSumZ p (fun x => g x y) + g p y) (fun y _ => gridSumZ_succ p _),
        gridSumZ_add m (fun y => gridSumZ p (fun x => g x y)) (fun y => g p y)]

theorem gridSumZ_sub (n : Nat) (f g : Nat → Int) :
    gridSumZ n (fun x => f x - g x) = gridSumZ n f - gridSumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show gridSumZ m (fun x => f x - g x) + (f m - g m)
        = (gridSumZ m f + f m) - (gridSumZ m g + g m)
    rw [ih]; ring_intZ

/-- Sum of a constant: `Σ_{x<n} c = n · c`. -/
theorem gridSumZ_const (n : Nat) (c : Int) :
    gridSumZ n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => show (0 : Int) = (0 : Int) * c; exact (zero_mul c).symm
  | succ m ih =>
    show gridSumZ m (fun _ => c) + c = ((m : Int) + 1) * c
    rw [ih]; ring_intZ

/-- Non-negativity: a pointwise-non-negative function has a non-negative grid sum
    (the `f = 0` special case of `gridSumZ_le`). -/
theorem gridSumZ_nonneg (n : Nat) (f : Nat → Int) (h : ∀ x, x < n → 0 ≤ f x) :
    0 ≤ gridSumZ n f := by
  have hle := gridSumZ_le n (fun _ => 0) f h
  rwa [gridSumZ_zero_fn] at hle

/-- Indicator sum vanishes below the spike: `a ≥ n` ⟹ `Σ_{i<n} [i=a]·v = 0` (no `i < n`
    hits the spike `a`). -/
theorem gridSumZ_delta_zero (n a : Nat) (v : Int) (ha : n ≤ a) :
    gridSumZ n (fun i => if i = a then v else 0) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hma : ¬ m = a := Nat.ne_of_lt ha
    rw [gridSumZ_succ, ih (Nat.le_of_succ_le ha), if_neg hma, Int.add_zero]

/-- Indicator (Kronecker-`δ`) sum: `a < n` ⟹ `Σ_{i<n} [i=a]·v = v`. -/
theorem gridSumZ_delta (n a : Nat) (v : Int) (ha : a < n) :
    gridSumZ n (fun i => if i = a then v else 0) = v := by
  induction n with
  | zero => exact absurd ha (Nat.not_lt_zero a)
  | succ m ih =>
    rw [gridSumZ_succ]
    by_cases hma : m = a
    · subst hma
      rw [gridSumZ_delta_zero m m v (Nat.le_refl m), if_pos rfl, zero_add]
    · have ha' : a < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ha) (fun h => hma h.symm)
      rw [ih ha', if_neg hma, Int.add_zero]

/-- Weighted indicator sum: `a < n` ⟹ `Σ_{i<n} [i=a]·g i = g a` (the dual/marginal
    pairing against a Kronecker-`δ` potential). -/
theorem gridSumZ_delta_weight (n a : Nat) (g : Nat → Int) (ha : a < n) :
    gridSumZ n (fun i => (if i = a then (1 : Int) else 0) * g i) = g a := by
  rw [gridSumZ_congr n (fun i => (if i = a then (1 : Int) else 0) * g i)
        (fun i => if i = a then g a else 0)
        (fun i _ => by
          dsimp only
          by_cases hi : i = a
          · rw [if_pos hi, if_pos hi, PolyIntM.one_mulZ, hi]
          · rw [if_neg hi, if_neg hi, zero_mul])]
  exact gridSumZ_delta n a (g a) ha

/-! ## §2 — Kantorovich weak duality (the transport core) -/

/-- Row marginal of a transport plan `π`: `μ x = Σ_y π x y`. -/
def rowMarg (n : Nat) (pi : Nat → Nat → Int) (x : Nat) : Int := gridSumZ n (fun y => pi x y)

/-- Column marginal: `ν y = Σ_x π x y`. -/
def colMarg (n : Nat) (pi : Nat → Nat → Int) (y : Nat) : Int := gridSumZ n (fun x => pi x y)

/-- Total transport cost `Σ_x Σ_y d(x,y)·π(x,y)`. -/
def transportCost (n : Nat) (d : Nat → Nat → Int) (pi : Nat → Nat → Int) : Int :=
  gridSumZ n (fun x => gridSumZ n (fun y => d x y * pi x y))

/-- Dual (potential) value `Σ_x f(x)·μ(x) − Σ_y f(y)·ν(y)`. -/
def dualValue (n : Nat) (f : Nat → Int) (pi : Nat → Nat → Int) : Int :=
  gridSumZ n (fun x => f x * rowMarg n pi x) - gridSumZ n (fun y => f y * colMarg n pi y)

/-- ★★★★★ **Kantorovich weak duality.**  For a transport plan `π ≥ 0` and a `1`-Lipschitz potential
    `f` (`f x − f y ≤ d x y`), the dual value is at most the transport cost:

      `Σ_x f(x)·μ(x) − Σ_y f(y)·ν(y)  ≤  Σ_x Σ_y d(x,y)·π(x,y)`.

    The `W₁`-dual ≤ `W₁`-primal direction of optimal transport — the engine of Ollivier–Ricci
    curvature, pinning `W₁(m_x,m_y)` (hence `κ`) when a plan and a potential meet.  Proof: express
    both single sums as double sums via the marginals, swap one (Fubini), combine to
    `Σ_x Σ_y (f x − f y)·π x y`, bound termwise by `d x y·π x y`. -/
theorem kantorovich_weak_duality (n : Nat) (d : Nat → Nat → Int) (f : Nat → Int)
    (pi : Nat → Nat → Int)
    (hpi : ∀ x y, x < n → y < n → 0 ≤ pi x y)
    (hlip : ∀ x y, f x - f y ≤ d x y) :
    dualValue n f pi ≤ transportCost n d pi := by
  unfold dualValue transportCost rowMarg colMarg
  have e1 : gridSumZ n (fun x => f x * gridSumZ n (fun y => pi x y))
      = gridSumZ n (fun x => gridSumZ n (fun y => f x * pi x y)) := by
    apply gridSumZ_congr; intro x _; rw [gridSumZ_mul_left]
  have e2 : gridSumZ n (fun y => f y * gridSumZ n (fun x => pi x y))
      = gridSumZ n (fun x => gridSumZ n (fun y => f y * pi x y)) := by
    rw [gridSumZ_congr n (fun y => f y * gridSumZ n (fun x => pi x y))
          (fun y => gridSumZ n (fun x => f y * pi x y)) (fun y _ => (gridSumZ_mul_left n (f y) _).symm)]
    exact gridSumZ_fubini n n (fun y x => f y * pi x y)
  have hAB : gridSumZ n (fun x => gridSumZ n (fun y => (f x - f y) * pi x y))
      = gridSumZ n (fun x => gridSumZ n (fun y => f x * pi x y))
        - gridSumZ n (fun x => gridSumZ n (fun y => f y * pi x y)) := by
    rw [← gridSumZ_sub n (fun x => gridSumZ n (fun y => f x * pi x y))
          (fun x => gridSumZ n (fun y => f y * pi x y))]
    apply gridSumZ_congr; intro x _
    rw [← gridSumZ_sub n (fun y => f x * pi x y) (fun y => f y * pi x y)]
    apply gridSumZ_congr; intro y _; ring_intZ
  rw [e1, e2, ← hAB]
  apply gridSumZ_le; intro x hx
  apply gridSumZ_le; intro y hy
  exact OrderMul.mul_le_mul_right_nonneg (hlip x y) (pi x y) (hpi x y hx hy)

/-! ## §3 — Ollivier–Ricci curvature -/

/-- Ollivier–Ricci curvature numerator on an edge with `d(x,y) = 1`: `κ = 1 − W₁(m_x,m_y)`.  Given a
    transport plan `π` (upper bound `W₁ ≤ transportCost`) we get the **lower bound**
    `κ ≥ 1 − transportCost`; given a `1`-Lipschitz potential (lower bound `W₁ ≥ dualValue`) we get the
    **upper bound** `κ ≤ 1 − dualValue`.  When a plan and a potential meet, `κ` is pinned. -/
def ollivierLB (cost : Int) : Int := 1 - cost

/-- ★★★★ **Ollivier curvature is squeezed between the dual and primal bounds.**  For any plan `π ≥ 0`
    and `1`-Lipschitz `f`, `1 − transportCost ≤ 1 − dualValue` — i.e. the curvature lower bound (from
    the plan) never exceeds the upper bound (from the potential), with equality pinning `κ` when they
    meet.  Immediate from `kantorovich_weak_duality`. -/
theorem ollivier_bracket (n : Nat) (d : Nat → Nat → Int) (f : Nat → Int) (pi : Nat → Nat → Int)
    (hpi : ∀ x y, x < n → y < n → 0 ≤ pi x y) (hlip : ∀ x y, f x - f y ≤ d x y) :
    1 - transportCost n d pi ≤ 1 - dualValue n f pi := by
  have hdc := kantorovich_weak_duality n d f pi hpi hlip
  apply Order.le_of_sub_nonneg
  rw [show (1 - dualValue n f pi) - (1 - transportCost n d pi)
        = transportCost n d pi - dualValue n f pi from by ring_intZ]
  exact Order.sub_nonneg_of_le hdc

/-- ★★★★ **Optimality certificate for a transport plan.**  `dualValue` depends only on the marginals,
    so if a plan `π` meets a `1`-Lipschitz potential (`dualValue f π = transportCost d π`), then `π` is
    cost-optimal among **all** plans `π'` sharing its marginals: `transportCost d π ≤ transportCost d π'`.
    Hence `W₁ = transportCost d π` exactly, pinning Ollivier `κ = 1 − transportCost d π` — the general
    form of the triangle worked example below.  Proof: same-marginals ⟹ same `dualValue`, then
    `kantorovich_weak_duality` bounds `π'`'s cost below by that common dual value. -/
theorem ollivier_plan_optimal (n : Nat) (d : Nat → Nat → Int) (f : Nat → Int)
    (pi pi' : Nat → Nat → Int)
    (hpi' : ∀ x y, x < n → y < n → 0 ≤ pi' x y)
    (hlip : ∀ x y, f x - f y ≤ d x y)
    (hrow : ∀ x, x < n → rowMarg n pi x = rowMarg n pi' x)
    (hcol : ∀ y, y < n → colMarg n pi y = colMarg n pi' y)
    (hmeet : dualValue n f pi = transportCost n d pi) :
    transportCost n d pi ≤ transportCost n d pi' := by
  have hr : gridSumZ n (fun x => f x * rowMarg n pi x) = gridSumZ n (fun x => f x * rowMarg n pi' x) :=
    gridSumZ_congr n _ _ (fun x hx => by rw [hrow x hx])
  have hc : gridSumZ n (fun y => f y * colMarg n pi y) = gridSumZ n (fun y => f y * colMarg n pi' y) :=
    gridSumZ_congr n _ _ (fun y hy => by rw [hcol y hy])
  have hdv : dualValue n f pi = dualValue n f pi' := by unfold dualValue; rw [hr, hc]
  rw [← hmeet, hdv]
  exact kantorovich_weak_duality n d f pi' hpi' hlip

/-! ## §4 — worked example: the triangle `K₃` has positive Ollivier curvature

The edge `(0,1)` of the triangle `C₃` (index set `{0,1,2}`, all distinct vertices at distance `1`).
The one-step walk measures (uniform on neighbours, integer-scaled to total mass `2`) are
`m₀ = (0,1,1)` (neighbours `{1,2}` of `0`) and `m₁ = (1,0,1)` (neighbours `{0,2}` of `1`).  An
optimal transport plan `triPi` (move the unit at vertex `1` to vertex `0`, keep the unit at `2`) has
cost `1`; the `1`-Lipschitz potential `triF` (`f 1 = 1`, else `0`) has dual value `1`.  They **meet**
(`dualValue = transportCost = 1`), so by `kantorovich_weak_duality` this is optimal: the scaled
`W₁(m₀,m₁) = 1`, i.e. probability `W₁ = ½`, so Ollivier `κ = 1 − ½ = ½ > 0` — the triangle is
positively curved (matching its Forman `+` sign, `DiscreteRicci`). -/

open E213.Tactic.NatHelper (cases_lt_three)

/-- Graph distance on the triangle `C₃`: `0` on the diagonal, `1` off it. -/
def triD : Nat → Nat → Int := fun i j => if i = j then 0 else 1

/-- The optimal transport plan: `1↦0` and `2↦2`. -/
def triPi : Nat → Nat → Int :=
  fun x y => if x = 1 ∧ y = 0 then 1 else if x = 2 ∧ y = 2 then 1 else 0

/-- Walk measure at vertex `0` (uniform on `{1,2}`, scaled): `(0,1,1)`. -/
def triMu0 : Nat → Int := fun i => if i = 1 then 1 else if i = 2 then 1 else 0

/-- Walk measure at vertex `1` (uniform on `{0,2}`, scaled): `(1,0,1)`. -/
def triMu1 : Nat → Int := fun i => if i = 0 then 1 else if i = 2 then 1 else 0

/-- The Kantorovich dual potential: `f 1 = 1`, else `0`. -/
def triF : Nat → Int := fun i => if i = 1 then 1 else 0

/-- `triPi` is a valid coupling of `m₀` and `m₁` (its marginals are `triMu0`, `triMu1`). -/
theorem triangle_coupling :
    (∀ x, x < 3 → rowMarg 3 triPi x = triMu0 x)
    ∧ (∀ y, y < 3 → colMarg 3 triPi y = triMu1 y) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rcases cases_lt_three hx with rfl | rfl | rfl <;> decide
  · rcases cases_lt_three hy with rfl | rfl | rfl <;> decide

/-- `triF` is `1`-Lipschitz w.r.t. the triangle distance: `f i − f j ≤ d i j` for all `i,j`. -/
theorem triF_lipschitz (i j : Nat) : triF i - triF j ≤ triD i j := by
  unfold triF triD
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, Order.sub_self_zero]; exact Order.le_refl 0
  · rw [if_neg hij]
    by_cases hi : i = 1 <;> by_cases hj : j = 1
    · exact absurd (hi.trans hj.symm) hij
    · rw [if_pos hi, if_neg hj]; decide
    · rw [if_neg hi, if_pos hj]; decide
    · rw [if_neg hi, if_neg hj]; decide

/-- ★★★★★ **The triangle's optimal transport meets the dual** (`dualValue = transportCost = 1`).
    With `triangle_coupling` (valid plan) and `triF_lipschitz` (valid potential), this pins the scaled
    `W₁(m₀,m₁) = 1` — Ollivier `κ = 1 − ½ = ½ > 0`, the triangle is positively curved. -/
theorem triangle_ollivier_optimal :
    dualValue 3 triF triPi = transportCost 3 triD triPi
    ∧ transportCost 3 triD triPi = 1 := by
  refine ⟨by decide, by decide⟩

/-- ★★★★★ **`triPi` is the optimal plan** (not merely *a* plan meeting the dual): its cost `1` is
    `≤` the cost of **every** valid coupling `π'` of `m₀`, `m₁`.  Hence `W₁(m₀,m₁) = 1` (scaled), so
    Ollivier `κ = 1 − ½ = ½ > 0` rigorously — a genuine optimum, via `ollivier_plan_optimal` with the
    `triF` certificate.  This is the full concrete Ollivier-curvature computation on the triangle. -/
theorem triangle_plan_optimal (pi' : Nat → Nat → Int)
    (hpi' : ∀ x y, x < 3 → y < 3 → 0 ≤ pi' x y)
    (hrow : ∀ x, x < 3 → rowMarg 3 pi' x = triMu0 x)
    (hcol : ∀ y, y < 3 → colMarg 3 pi' y = triMu1 y) :
    transportCost 3 triD triPi ≤ transportCost 3 triD pi' := by
  refine ollivier_plan_optimal 3 triD triF triPi pi' hpi' triF_lipschitz
    (fun x hx => ?_) (fun y hy => ?_) triangle_ollivier_optimal.1
  · rw [triangle_coupling.1 x hx, hrow x hx]
  · rw [triangle_coupling.2 y hy, hcol y hy]

/-! ## §5 — worked example: the 4-cycle `C₄` is **flat** (`κ = 0`)

The edge `(0,1)` of the square `C₄` (`0–1–2–3–0`, no triangles).  Neighbours of `0` are `{1,3}`, of
`1` are `{0,2}`, so the scaled walk measures are `m₀ = (0,1,0,1)`, `m₁ = (1,0,1,0)`.  The plan `c4Pi`
(`1↦0`, `3↦2`) has cost `2`, and the `1`-Lipschitz potential `c4F` (`f 1 = f 3 = 1`, else `0`) has dual
value `2` — they **meet**, so scaled `W₁ = 2`, probability `W₁ = 1`, Ollivier `κ = 1 − 1 = 0`: the
square is **flat**.  Contrast the triangle (`κ = ½ > 0`): Ollivier curvature tracks local clustering
(triangles ⟹ positive), the optimal-transport analogue of the Forman / Gauss–Bonnet sign↔topology
results (`DiscreteRicci`, `DiscreteGaussBonnet`). -/

open E213.Tactic.NatHelper (cases_lt_four)

/-- Generic Int helper: `a ≤ c` and `0 ≤ b` ⟹ `a − b ≤ c`. -/
theorem sub_le_of_le_of_nonneg {a b c : Int} (ha : a ≤ c) (hb : (0 : Int) ≤ b) : a - b ≤ c :=
  Order.le_trans
    (show a - b ≤ a from by
      apply Order.le_of_sub_nonneg
      rw [show a - (a - b) = b from by ring_intZ]
      exact Order.nonneg_of_le_zero hb)
    ha

/-- Graph distance on the square `C₄`: `0` diagonal, `2` on opposite pairs `{0,2},{1,3}`, else `1`. -/
def c4D : Nat → Nat → Int := fun i j =>
  if i = j then 0
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 2 else 1

/-- The optimal transport plan on `C₄`: `1↦0` and `3↦2`. -/
def c4Pi : Nat → Nat → Int :=
  fun x y => if x = 1 ∧ y = 0 then 1 else if x = 3 ∧ y = 2 then 1 else 0

/-- Walk measure at vertex `0` (uniform on neighbours `{1,3}`, scaled): `(0,1,0,1)`. -/
def c4Mu0 : Nat → Int := fun i => if i = 1 then 1 else if i = 3 then 1 else 0

/-- Walk measure at vertex `1` (uniform on neighbours `{0,2}`, scaled): `(1,0,1,0)`. -/
def c4Mu1 : Nat → Int := fun i => if i = 0 then 1 else if i = 2 then 1 else 0

/-- The Kantorovich dual potential: `f 1 = f 3 = 1`, else `0`. -/
def c4F : Nat → Int := fun i => if i = 1 then 1 else if i = 3 then 1 else 0

/-- `c4F i ≤ 1` for every `i` (it takes values in `{0,1}`). -/
theorem c4F_le_one (i : Nat) : c4F i ≤ 1 := by
  unfold c4F
  by_cases h1 : i = 1
  · rw [if_pos h1]; exact Order.le_refl 1
  · rw [if_neg h1]
    by_cases h3 : i = 3
    · rw [if_pos h3]; exact Order.le_refl 1
    · rw [if_neg h3]; decide

/-- `0 ≤ c4F j` for every `j`. -/
theorem c4F_nonneg (j : Nat) : (0 : Int) ≤ c4F j := by
  unfold c4F
  by_cases h1 : j = 1
  · rw [if_pos h1]; decide
  · rw [if_neg h1]
    by_cases h3 : j = 3
    · rw [if_pos h3]; decide
    · rw [if_neg h3]; exact Order.le_refl 0

/-- `c4F` is `1`-Lipschitz w.r.t. the square distance: off-diagonal `d ≥ 1` while `f i − f j ≤ 1`. -/
theorem c4F_lipschitz (i j : Nat) : c4F i - c4F j ≤ c4D i j := by
  by_cases hij : i = j
  · subst hij; rw [Order.sub_self_zero]
    show (0 : Int) ≤ c4D i i
    unfold c4D; rw [if_pos rfl]; exact Order.le_refl 0
  · have hd : (1 : Int) ≤ c4D i j := by
      unfold c4D; rw [if_neg hij]
      by_cases hopp : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)
      · rw [if_pos hopp]; decide
      · rw [if_neg hopp]; exact Order.le_refl 1
    exact Order.le_trans (sub_le_of_le_of_nonneg (c4F_le_one i) (c4F_nonneg j)) hd

/-- `c4Pi` is a valid coupling of `m₀` and `m₁` (its marginals are `c4Mu0`, `c4Mu1`). -/
theorem c4_coupling :
    (∀ x, x < 4 → rowMarg 4 c4Pi x = c4Mu0 x)
    ∧ (∀ y, y < 4 → colMarg 4 c4Pi y = c4Mu1 y) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rcases cases_lt_four hx with rfl | rfl | rfl | rfl <;> decide
  · rcases cases_lt_four hy with rfl | rfl | rfl | rfl <;> decide

/-- ★★★★★ **The square's transport meets the dual at `2`** (`dualValue = transportCost = 2`).  Scaled
    `W₁ = 2`, probability `W₁ = 1`, Ollivier `κ = 1 − 1 = 0`: the square `C₄` is flat. -/
theorem c4_ollivier_flat :
    dualValue 4 c4F c4Pi = transportCost 4 c4D c4Pi
    ∧ transportCost 4 c4D c4Pi = 2 := by
  refine ⟨by decide, by decide⟩

/-- ★★★★★ **`c4Pi` is the optimal plan**: its cost `2 ≤` cost of **every** valid coupling of `m₀,m₁`,
    so `W₁ = 2` (scaled) is a genuine optimum and Ollivier `κ = 0` rigorously — the square is flat. -/
theorem c4_plan_optimal (pi' : Nat → Nat → Int)
    (hpi' : ∀ x y, x < 4 → y < 4 → 0 ≤ pi' x y)
    (hrow : ∀ x, x < 4 → rowMarg 4 pi' x = c4Mu0 x)
    (hcol : ∀ y, y < 4 → colMarg 4 pi' y = c4Mu1 y) :
    transportCost 4 c4D c4Pi ≤ transportCost 4 c4D pi' := by
  refine ollivier_plan_optimal 4 c4D c4F c4Pi pi' hpi' c4F_lipschitz
    (fun x hx => ?_) (fun y hy => ?_) c4_ollivier_flat.1
  · rw [c4_coupling.1 x hx, hrow x hx]
  · rw [c4_coupling.2 y hy, hcol y hy]

/-! ## §6 — worked example: the double-star is **negatively curved** (`κ < 0`)

The center edge `(0,1)` of the double-star `D` (center vertices `0,1`; leaves `{2,3}` of `0`, leaves
`{4,5}` of `1`).  Each centre has degree `3`, so the scaled walk measures are `m₀ = (·, neighbours of 0
`{1,2,3}`)`, `m₁ = (·, neighbours of 1 `{0,4,5}`)`, each unit mass `1` on three vertices.  No matter the
plan, two of `m₀`'s three units must cross to the far star (`distance 1` and `3`), forcing transport cost
`5`.  The matching `1`-Lipschitz potential `dsF` (`f = 0,−1,1,1,−2,−2` on `0..5`) also reaches dual value
`5`; they **meet**, so scaled `W₁ = 5`, probability `W₁ = 5/3`, Ollivier `κ = 1 − 5/3 = −2/3 < 0`: the
double-star is **negatively curved** (a tree, like hyperbolic space).  Together with the triangle
(`κ = ½ > 0`) and square (`κ = 0`) this is the full Ollivier sign **trichotomy**, matching Forman /
Gauss–Bonnet (`DiscreteRicci`, `DiscreteGaussBonnet`): `+` clustered, `0` flat, `−` tree. -/

open E213.Tactic.NatHelper (cases_lt_six)

/-- Generic Int helper: `a ≤ c` and `d ≤ b` ⟹ `a − b ≤ c − d` (monotone subtraction). -/
theorem sub_le_sub_bounds {a b c d : Int} (ha : a ≤ c) (hb : d ≤ b) : a - b ≤ c - d := by
  apply Order.le_of_sub_nonneg
  rw [show (c - d) - (a - b) = (c - a) + (b - d) from by ring_intZ]
  exact Order.nonneg_of_le_zero
    (add_nonneg (Order.le_zero_of_nonneg (Order.sub_nonneg_of_le ha))
                (Order.le_zero_of_nonneg (Order.sub_nonneg_of_le hb)))

/-- Graph distance on the double-star (centres `0,1`; leaves `{2,3}` of `0`, `{4,5}` of `1`).  `0`
    diagonal; `1` on the `5` edges; `2` on the `2`-paths; `3` on the cross-star leaf pairs.  Guarded by
    `i,j < 6` so out-of-range indices default to `3` (≥ any potential spread). -/
def dsD (i j : Nat) : Int :=
  if i = j then 0
  else if i < 6 ∧ j < 6 then
    (if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)
        ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨ (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1)
        ∨ (i = 1 ∧ j = 5) ∨ (i = 5 ∧ j = 1) then 1
     else if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨ (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0)
        ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)
        ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) then 2
     else 3)
  else 3

/-- The optimal transport plan on the double-star: `1↦4`, `2↦0`, `3↦5` (cost `1+1+3 = 5`). -/
def dsPi : Nat → Nat → Int :=
  fun x y => if x = 1 ∧ y = 4 then 1 else if x = 2 ∧ y = 0 then 1
             else if x = 3 ∧ y = 5 then 1 else 0

/-- Walk measure at centre `0` (uniform on neighbours `{1,2,3}`, scaled). -/
def dsMu0 : Nat → Int := fun i => if i = 1 then 1 else if i = 2 then 1 else if i = 3 then 1 else 0

/-- Walk measure at centre `1` (uniform on neighbours `{0,4,5}`, scaled). -/
def dsMu1 : Nat → Int := fun i => if i = 0 then 1 else if i = 4 then 1 else if i = 5 then 1 else 0

/-- The Kantorovich dual potential: `f = (0,−1,1,1,−2,−2)` on `0..5`, else `0`. -/
def dsF : Nat → Int :=
  fun i => if i = 2 ∨ i = 3 then 1 else if i = 1 then -1 else if i = 4 ∨ i = 5 then -2 else 0

/-- `dsF i ≤ 1` for every `i`. -/
theorem dsF_le_one (i : Nat) : dsF i ≤ 1 := by
  unfold dsF
  by_cases h23 : i = 2 ∨ i = 3
  · rw [if_pos h23]; exact Order.le_refl 1
  · rw [if_neg h23]
    by_cases h1 : i = 1
    · rw [if_pos h1]; decide
    · rw [if_neg h1]
      by_cases h45 : i = 4 ∨ i = 5
      · rw [if_pos h45]; decide
      · rw [if_neg h45]; decide

/-- `-2 ≤ dsF i` for every `i`. -/
theorem dsF_ge_negtwo (i : Nat) : (-2 : Int) ≤ dsF i := by
  unfold dsF
  by_cases h23 : i = 2 ∨ i = 3
  · rw [if_pos h23]; decide
  · rw [if_neg h23]
    by_cases h1 : i = 1
    · rw [if_pos h1]; decide
    · rw [if_neg h1]
      by_cases h45 : i = 4 ∨ i = 5
      · rw [if_pos h45]; exact Order.le_refl (-2)
      · rw [if_neg h45]; decide

/-- `dsF` is `1`-Lipschitz w.r.t. the double-star distance.  On the six graph vertices each of the `36`
    pairs is checked directly; for out-of-range indices the distance defaults to `3 ≥ 1 − (−2)`, the full
    `dsF` spread. -/
theorem dsF_lipschitz (i j : Nat) : dsF i - dsF j ≤ dsD i j := by
  by_cases hij : i = j
  · subst hij; rw [Order.sub_self_zero]
    show (0 : Int) ≤ dsD i i
    unfold dsD; rw [if_pos rfl]; exact Order.le_refl 0
  · by_cases hb : i < 6 ∧ j < 6
    · obtain ⟨hi, hj⟩ := hb
      rcases cases_lt_six hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases cases_lt_six hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl hij | decide
    · have hd : dsD i j = 3 := by unfold dsD; rw [if_neg hij, if_neg hb]
      rw [hd]
      exact Order.le_trans (sub_le_sub_bounds (dsF_le_one i) (dsF_ge_negtwo j)) (by decide)

/-- `dsPi` is a valid coupling of `m₀` and `m₁` (its marginals are `dsMu0`, `dsMu1`). -/
theorem ds_coupling :
    (∀ x, x < 6 → rowMarg 6 dsPi x = dsMu0 x)
    ∧ (∀ y, y < 6 → colMarg 6 dsPi y = dsMu1 y) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rcases cases_lt_six hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases cases_lt_six hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- ★★★★★ **The double-star's transport meets the dual at `5`** (`dualValue = transportCost = 5`).
    Scaled `W₁ = 5`, probability `W₁ = 5/3`, Ollivier `κ = 1 − 5/3 = −2/3 < 0`: negatively curved. -/
theorem ds_ollivier_negative :
    dualValue 6 dsF dsPi = transportCost 6 dsD dsPi
    ∧ transportCost 6 dsD dsPi = 5 := by
  refine ⟨by decide, by decide⟩

/-- ★★★★★ **`dsPi` is the optimal plan**: its cost `5 ≤` cost of **every** valid coupling of `m₀,m₁`,
    so `W₁ = 5` (scaled) is a genuine optimum and Ollivier `κ = −2/3 < 0` rigorously — the double-star is
    negatively curved, completing the Ollivier `+ / 0 / −` trichotomy. -/
theorem ds_plan_optimal (pi' : Nat → Nat → Int)
    (hpi' : ∀ x y, x < 6 → y < 6 → 0 ≤ pi' x y)
    (hrow : ∀ x, x < 6 → rowMarg 6 pi' x = dsMu0 x)
    (hcol : ∀ y, y < 6 → colMarg 6 pi' y = dsMu1 y) :
    transportCost 6 dsD dsPi ≤ transportCost 6 dsD pi' := by
  refine ollivier_plan_optimal 6 dsD dsF dsPi pi' hpi' dsF_lipschitz
    (fun x hx => ?_) (fun y hy => ?_) ds_ollivier_negative.1
  · rw [ds_coupling.1 x hx, hrow x hx]
  · rw [ds_coupling.2 y hy, hcol y hy]

/-! ## §7 — the complete graph `K_m` for general `m`: Ollivier `κ = (m−2)/(m−1) > 0`

The parametric companion of the §4 triangle (`K₃`).  The edge `(0,1)` of `K_m` (vertices `0..m−1`, every
distinct pair at distance `1`).  The one-step walk measures (uniform on the `m−1` neighbours, scaled to
total mass `m−1`) are `m₀ = [i ↦ 1 unless i = 0]` and `m₁ = [i ↦ 1 unless i = 1]`: they agree on the
`m−2` shared neighbours `{2,…,m−1}` and differ only at `0,1` — `m₀` has the unit at `1`, `m₁` the unit at
`0`.  So the optimal plan `kmPi` keeps the `m−2` shared units on the diagonal (cost `0`) and moves the
single unit at vertex `1` to vertex `0` (distance `1`): cost `1`.  The `1`-Lipschitz Kronecker-`δ`
potential `kmF = δ₁` reaches dual value `1`; they **meet**, so (scaled) `W₁(m₀,m₁) = 1`, probability
`W₁ = 1/(m−1)`, Ollivier `κ = 1 − 1/(m−1) = (m−2)/(m−1) > 0` for `m ≥ 3`.  At `m = 3` this is the triangle
`κ = ½`; `κ → 1` as `m → ∞` (the complete graph is increasingly positively curved) — the
optimal-transport reading of all-to-all adjacency, parallel to the Bakry–Émery `CD((m+2)/2,∞)`
(`BakryEmery.lean` §3).  Unlike §4–§6 (`decide` on a fixed graph), every step here is a `gridSumZ`-`δ`
computation parametric in `m`. -/

/-- Graph distance on `K_m`: `0` on the diagonal, `1` off it (all distinct vertices adjacent). -/
def kmD : Nat → Nat → Int := fun i j => if i = j then 0 else 1

/-- Walk measure at vertex `0` (uniform on neighbours `= all except 0`, scaled mass `1` each). -/
def kmMu0 : Nat → Int := fun i => if i = 0 then 0 else 1

/-- Walk measure at vertex `1` (uniform on neighbours `= all except 1`). -/
def kmMu1 : Nat → Int := fun i => if i = 1 then 0 else 1

/-- The optimal transport plan: move the unit at vertex `1` to vertex `0`, keep every shared neighbour
    `≥ 2` on the diagonal. -/
def kmPi : Nat → Nat → Int :=
  fun x y => if x = 1 then (if y = 0 then 1 else 0)
             else if 2 ≤ x then (if y = x then 1 else 0) else 0

/-- The Kantorovich dual potential: the Kronecker-`δ` at vertex `1`. -/
def kmF : Nat → Int := fun i => if i = 1 then 1 else 0

/-- `2 ≤ x` from `x ≠ 0` and `x ≠ 1`. -/
private theorem two_le_of_ne01 {x : Nat} (h0 : ¬ x = 0) (h1 : ¬ x = 1) : 2 ≤ x := by
  match x with
  | 0 => exact absurd rfl h0
  | 1 => exact absurd rfl h1
  | n + 2 => exact Nat.le_add_left 2 n

/-- Row `0` of the plan is empty. -/
theorem kmPi_row0 (y : Nat) : kmPi 0 y = 0 := by
  unfold kmPi; rw [if_neg (by decide : ¬ (0:Nat) = 1), if_neg (by decide : ¬ 2 ≤ (0:Nat))]

/-- Row `1` of the plan is the `δ` at `0`. -/
theorem kmPi_row1 (y : Nat) : kmPi 1 y = if y = 0 then 1 else 0 := by
  unfold kmPi; rw [if_pos rfl]

/-- Row `x ≥ 2` of the plan is the diagonal `δ` at `x`. -/
theorem kmPi_rowGe2 {x : Nat} (hx : 2 ≤ x) (y : Nat) :
    kmPi x y = if y = x then 1 else 0 := by
  unfold kmPi
  rw [if_neg (fun h => by rw [h] at hx; exact absurd hx (by decide)), if_pos hx]

/-- Column `0` of the plan is the `δ` at `1` (only `1 ↦ 0` lands in column `0`). -/
theorem kmPi_col0 (x : Nat) : kmPi x 0 = if x = 1 then 1 else 0 := by
  by_cases hx1 : x = 1
  · subst hx1; decide
  · rw [if_neg hx1]
    by_cases hx0 : x = 0
    · subst hx0; exact kmPi_row0 0
    · rw [kmPi_rowGe2 (two_le_of_ne01 hx0 hx1), if_neg (fun h => hx0 h.symm)]

/-- Column `1` of the plan is empty. -/
theorem kmPi_col1 (x : Nat) : kmPi x 1 = 0 := by
  by_cases hx1 : x = 1
  · subst hx1; decide
  · by_cases hx0 : x = 0
    · subst hx0; exact kmPi_row0 1
    · rw [kmPi_rowGe2 (two_le_of_ne01 hx0 hx1), if_neg (fun h => hx1 h.symm)]

/-- Column `j ≥ 2` of the plan is the diagonal `δ` at `j`. -/
theorem kmPi_colGe2 {j : Nat} (hj : 2 ≤ j) (x : Nat) :
    kmPi x j = if x = j then 1 else 0 := by
  by_cases hx1 : x = 1
  · subst hx1
    rw [kmPi_row1, if_neg (fun h => by rw [h] at hj; exact absurd hj (by decide)),
        if_neg (fun h => by rw [← h] at hj; exact absurd hj (by decide))]
  · by_cases hx0 : x = 0
    · subst hx0
      rw [kmPi_row0, if_neg (fun h => by rw [← h] at hj; exact absurd hj (by decide))]
    · rw [kmPi_rowGe2 (two_le_of_ne01 hx0 hx1)]
      by_cases hxj : x = j
      · rw [if_pos hxj.symm, if_pos hxj]
      · rw [if_neg (fun h => hxj h.symm), if_neg hxj]

/-- ★★★★★ **`kmPi` is a valid coupling of `m₀` and `m₁`** (its marginals are `kmMu0`, `kmMu1`),
    parametric in the vertex count `m ≥ 2`.  The three row/column cases (`0`, `1`, `≥ 2`) are each a
    Kronecker-`δ` grid sum. -/
theorem km_coupling (m : Nat) (hm : 2 ≤ m) :
    (∀ x, x < m → rowMarg m kmPi x = kmMu0 x)
    ∧ (∀ y, y < m → colMarg m kmPi y = kmMu1 y) := by
  have h0m : 0 < m := Nat.lt_of_lt_of_le (by decide) hm
  have h1m : 1 < m := Nat.lt_of_lt_of_le (by decide) hm
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · by_cases hx1 : x = 1
    · subst hx1
      show gridSumZ m (fun b => kmPi 1 b) = (1:Int)
      exact Eq.trans (gridSumZ_congr m (fun b => kmPi 1 b) (fun b => if b = 0 then (1:Int) else 0)
          (fun b _ => kmPi_row1 b)) (gridSumZ_delta m 0 1 h0m)
    · by_cases hx0 : x = 0
      · subst hx0
        show gridSumZ m (fun b => kmPi 0 b) = (0:Int)
        exact Eq.trans (gridSumZ_congr m (fun b => kmPi 0 b) (fun _ => (0:Int))
            (fun b _ => kmPi_row0 b)) (gridSumZ_zero_fn m)
      · show gridSumZ m (fun b => kmPi x b) = kmMu0 x
        have hmu : kmMu0 x = 1 := by unfold kmMu0; rw [if_neg hx0]
        exact (Eq.trans (gridSumZ_congr m (fun b => kmPi x b) (fun b => if b = x then (1:Int) else 0)
            (fun b _ => kmPi_rowGe2 (two_le_of_ne01 hx0 hx1) b))
          (gridSumZ_delta m x 1 hx)).trans hmu.symm
  · by_cases hy1 : y = 1
    · subst hy1
      show gridSumZ m (fun a => kmPi a 1) = (0:Int)
      exact Eq.trans (gridSumZ_congr m (fun a => kmPi a 1) (fun _ => (0:Int))
          (fun a _ => kmPi_col1 a)) (gridSumZ_zero_fn m)
    · by_cases hy0 : y = 0
      · subst hy0
        show gridSumZ m (fun a => kmPi a 0) = (1:Int)
        exact Eq.trans (gridSumZ_congr m (fun a => kmPi a 0) (fun a => if a = 1 then (1:Int) else 0)
            (fun a _ => kmPi_col0 a)) (gridSumZ_delta m 1 1 h1m)
      · show gridSumZ m (fun a => kmPi a y) = kmMu1 y
        have hmu : kmMu1 y = 1 := by unfold kmMu1; rw [if_neg hy1]
        exact (Eq.trans (gridSumZ_congr m (fun a => kmPi a y) (fun a => if a = y then (1:Int) else 0)
            (fun a _ => kmPi_colGe2 (two_le_of_ne01 hy0 hy1) a))
          (gridSumZ_delta m y 1 hy)).trans hmu.symm

/-- ★★★★★ **Transport cost `= 1`** (parametric in `m ≥ 2`).  The only off-diagonal mass is `1 ↦ 0` at
    distance `1`; the `m−2` shared units sit on the diagonal (distance `0`).  `kmD a b · kmPi a b =
    δ₁(a)·δ₀(b)`, so the double `δ`-sum is `1`. -/
theorem km_cost (m : Nat) (hm : 2 ≤ m) : transportCost m kmD kmPi = 1 := by
  have h0m : 0 < m := Nat.lt_of_lt_of_le (by decide) hm
  have h1m : 1 < m := Nat.lt_of_lt_of_le (by decide) hm
  unfold transportCost
  have inner : ∀ a, gridSumZ m (fun b => kmD a b * kmPi a b) = if a = 1 then (1:Int) else 0 := by
    intro a
    by_cases ha1 : a = 1
    · subst ha1
      show gridSumZ m (fun b => kmD 1 b * kmPi 1 b) = 1
      exact Eq.trans (gridSumZ_congr m (fun b => kmD 1 b * kmPi 1 b)
          (fun b => if b = 0 then (1:Int) else 0)
          (fun b _ => by
            dsimp only
            rw [kmPi_row1]
            by_cases hb0 : b = 0
            · subst hb0; decide
            · rw [if_neg hb0, PolyIntM.mul_zeroZ]))
        (gridSumZ_delta m 0 1 h0m)
    · rw [if_neg ha1]
      exact Eq.trans (gridSumZ_congr m (fun b => kmD a b * kmPi a b) (fun _ => (0:Int))
          (fun b _ => by
            dsimp only
            by_cases ha0 : a = 0
            · subst ha0; rw [kmPi_row0, PolyIntM.mul_zeroZ]
            · rw [kmPi_rowGe2 (two_le_of_ne01 ha0 ha1)]
              by_cases hba : b = a
              · rw [if_pos hba]; unfold kmD; rw [if_pos hba.symm, zero_mul]
              · rw [if_neg hba, PolyIntM.mul_zeroZ]))
        (gridSumZ_zero_fn m)
  show gridSumZ m (fun a => gridSumZ m (fun b => kmD a b * kmPi a b)) = 1
  exact Eq.trans (gridSumZ_congr m (fun a => gridSumZ m (fun b => kmD a b * kmPi a b))
      (fun a => if a = 1 then (1:Int) else 0) (fun a _ => inner a))
    (gridSumZ_delta m 1 1 h1m)

/-- ★★★★★ **Dual value `= 1`** (parametric in `m ≥ 2`).  Against the `δ₁` potential, the dual collapses
    to `rowMarg(1) − colMarg(1) = m₀(1) − m₁(1) = 1 − 0 = 1` via the weighted-`δ` sum. -/
theorem km_dual (m : Nat) (hm : 2 ≤ m) : dualValue m kmF kmPi = 1 := by
  have h0m : 0 < m := Nat.lt_of_lt_of_le (by decide) hm
  have h1m : 1 < m := Nat.lt_of_lt_of_le (by decide) hm
  have hrow1 : rowMarg m kmPi 1 = 1 :=
    Eq.trans (gridSumZ_congr m (fun b => kmPi 1 b) (fun b => if b = 0 then (1:Int) else 0)
      (fun b _ => kmPi_row1 b)) (gridSumZ_delta m 0 1 h0m)
  have hcol1 : colMarg m kmPi 1 = 0 :=
    Eq.trans (gridSumZ_congr m (fun a => kmPi a 1) (fun _ => (0:Int))
      (fun a _ => kmPi_col1 a)) (gridSumZ_zero_fn m)
  have hs1 : gridSumZ m (fun x => kmF x * rowMarg m kmPi x) = 1 :=
    (gridSumZ_delta_weight m 1 (rowMarg m kmPi) h1m).trans hrow1
  have hs2 : gridSumZ m (fun y => kmF y * colMarg m kmPi y) = 0 :=
    (gridSumZ_delta_weight m 1 (colMarg m kmPi) h1m).trans hcol1
  show gridSumZ m (fun x => kmF x * rowMarg m kmPi x)
       - gridSumZ m (fun y => kmF y * colMarg m kmPi y) = 1
  rw [hs1, hs2]; decide

/-- ★★★★★ **The plan meets the dual at `1`** (`dualValue = transportCost = 1`), parametric in `m ≥ 2`.
    By `kantorovich_weak_duality` this pins the scaled `W₁(m₀,m₁) = 1`, probability `1/(m−1)` — Ollivier
    `κ = (m−2)/(m−1) > 0` for the complete graph `K_m`, generalizing the triangle (`m = 3`, `κ = ½`). -/
theorem km_ollivier_optimal (m : Nat) (hm : 2 ≤ m) :
    dualValue m kmF kmPi = transportCost m kmD kmPi
    ∧ transportCost m kmD kmPi = 1 :=
  ⟨(km_dual m hm).trans (km_cost m hm).symm, km_cost m hm⟩

/-- `kmF i ≤ 1` (the `δ₁` potential takes values in `{0,1}`). -/
theorem kmF_le_one (i : Nat) : kmF i ≤ 1 := by
  unfold kmF; by_cases h : i = 1
  · rw [if_pos h]; exact Order.le_refl 1
  · rw [if_neg h]; decide

/-- `0 ≤ kmF i`. -/
theorem kmF_nonneg (i : Nat) : (0:Int) ≤ kmF i := by
  unfold kmF; by_cases h : i = 1
  · rw [if_pos h]; decide
  · rw [if_neg h]; exact Order.le_refl 0

/-- `kmF` is `1`-Lipschitz w.r.t. the `K_m` distance: off-diagonal `d = 1 ≥ f i − f j`. -/
theorem kmF_lipschitz (i j : Nat) : kmF i - kmF j ≤ kmD i j := by
  by_cases hij : i = j
  · subst hij; rw [Order.sub_self_zero]
    show (0:Int) ≤ kmD i i; unfold kmD; rw [if_pos rfl]; exact Order.le_refl 0
  · have hd : (1:Int) ≤ kmD i j := by unfold kmD; rw [if_neg hij]; exact Order.le_refl 1
    exact Order.le_trans (sub_le_of_le_of_nonneg (kmF_le_one i) (kmF_nonneg j)) hd

/-- ★★★★★ **`kmPi` is the optimal plan** (not merely *a* plan meeting the dual): its cost `1 ≤` the cost
    of **every** valid coupling `π'` of `m₀, m₁`, so the scaled `W₁(m₀,m₁) = 1` is a genuine optimum and
    Ollivier `κ = (m−2)/(m−1) > 0` rigorously for `K_m`, general `m ≥ 2`.  Via `ollivier_plan_optimal`
    with the `kmF` certificate and `km_coupling`. -/
theorem km_plan_optimal (m : Nat) (hm : 2 ≤ m) (pi' : Nat → Nat → Int)
    (hpi' : ∀ x y, x < m → y < m → 0 ≤ pi' x y)
    (hrow : ∀ x, x < m → rowMarg m pi' x = kmMu0 x)
    (hcol : ∀ y, y < m → colMarg m pi' y = kmMu1 y) :
    transportCost m kmD kmPi ≤ transportCost m kmD pi' := by
  refine ollivier_plan_optimal m kmD kmF kmPi pi' hpi' kmF_lipschitz
    (fun x hx => ?_) (fun y hy => ?_) (km_ollivier_optimal m hm).1
  · rw [(km_coupling m hm).1 x hx, hrow x hx]
  · rw [(km_coupling m hm).2 y hy, hcol y hy]

end E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci
