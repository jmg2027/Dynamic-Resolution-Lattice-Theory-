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

end E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci
