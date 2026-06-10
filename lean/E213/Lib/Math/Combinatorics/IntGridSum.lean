import E213.Meta.Int213
import E213.Meta.Int213.PolyIntMTactic

/-!
# Integer grid sum `gridSumZ n f = Σ_{x<n} f x`

A finite index sum over ℤ with its linearity, monotonicity, Fubini, and Kronecker-`δ`
toolkit — domain-agnostic infrastructure for any finite-contraction computation (optimal
transport, Bakry–Émery curvature, the Riemannian tensor calculus, graph-Laplacian spectra).
All `∅`-axiom (`ring_intZ` + the pure `Int213.Order` API).
-/

namespace E213.Lib.Math.Combinatorics.IntGridSum

open E213.Meta.Int213

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

/-- **Antisymmetric kernel sums to zero**: `A x y = −A y x` ⟹ `Σ_xΣ_y A x y = 0`.
    Fubini reflects the double sum onto its own negation (`S = −S`), and the doubling
    cancellation `2S = 0 ⟹ S = 0` closes without division — the discrete
    integration-by-parts engine (every Green identity is an antisymmetrized kernel). -/
theorem gridSumZ_antisym_zero (n : Nat) (A : Nat → Nat → Int)
    (hA : ∀ x y, A x y = - A y x) :
    gridSumZ n (fun x => gridSumZ n (fun y => A x y)) = 0 := by
  have hswap : gridSumZ n (fun x => gridSumZ n (fun y => A x y))
      = gridSumZ n (fun y => gridSumZ n (fun x => A x y)) := gridSumZ_fubini n n A
  have hneg : gridSumZ n (fun y => gridSumZ n (fun x => A x y))
      = gridSumZ n (fun y => (-1) * gridSumZ n (fun x => A y x)) :=
    gridSumZ_congr n _ _ (fun y _ => by
      rw [← gridSumZ_mul_left n (-1) (fun x => A y x)]
      exact gridSumZ_congr n _ _ (fun x _ => by rw [hA x y]; ring_intZ))
  have hS : gridSumZ n (fun x => gridSumZ n (fun y => A x y))
      = (-1) * gridSumZ n (fun y => gridSumZ n (fun x => A y x)) :=
    Eq.trans hswap (Eq.trans hneg
      (gridSumZ_mul_left n (-1) (fun y => gridSumZ n (fun x => A y x))))
  have h2 : 2 * gridSumZ n (fun x => gridSumZ n (fun y => A x y)) = 0 := by
    rw [show 2 * gridSumZ n (fun x => gridSumZ n (fun y => A x y))
          = gridSumZ n (fun x => gridSumZ n (fun y => A x y))
            - (-1) * gridSumZ n (fun y => gridSumZ n (fun x => A y x)) from by ring_intZ,
        ← hS]
    exact Order.sub_self_zero _
  exact OrderMul.eq_zero_of_two_mul_eq_zero h2

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

end E213.Lib.Math.Combinatorics.IntGridSum
