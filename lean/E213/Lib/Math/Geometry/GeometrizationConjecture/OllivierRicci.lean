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

Ladder: `research-notes/frontiers/a6_ricci_core/discrete_ricci_flow_ladder.md`, rung 5.
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

end E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci
