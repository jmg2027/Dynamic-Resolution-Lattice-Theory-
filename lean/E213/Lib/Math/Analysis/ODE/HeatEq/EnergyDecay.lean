import E213.Lib.Math.Analysis.ODE.HeatEq.Conservation
import E213.Lib.Math.Analysis.ODE.HeatEq.EnergyL2
import E213.Meta.Int213
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Nat.PolyNatMTactic

/-!
# Discrete heat equation — Dirichlet energy decay `E(lazy u) ≤ 16·E(u)` (∅-axiom)

**Marathon P3 capstone**.

The lazy heat step does not increase the Dirichlet energy (averaged): on the length-`n`
periodic grid, `E(lazyStep u) ≤ 16·E(u)` (the `16 = 4²` is the stencil's normalization, so the
*averaged* energy is non-increasing).  Assembled from:

  * the heat step commutes with the gradient — the lazy-step edge difference is the lazy
    stencil on the three edge gradients (`lazy_energy_pointwise`);
  * Jensen / convexity of the square (`lazyHeatStep_l2_jensen`);
  * cyclic-shift invariance of the grid sum (`gridSum_rightNbr`), which turns each shifted
    gradient-energy back into `E(u)`.

The `Nat`↔ℤ bridge is `∅`-axiom (`sqDistNat_cast` + `Int213.Order.le_of_ofNat_le`); the per-edge
square bound is the POSITIVITY archetype over ℤ.  All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.ODE.HeatEq.EnergyDecay

open E213.Lib.Math.Analysis.ODE.HeatEq.Discrete
open E213.Lib.Math.Analysis.ODE.HeatEq.EnergyL2 (lazy_energy_pointwise lazyHeatStep_l2_jensen)
open E213.Meta.Int213

/-! ## §1 — the `Nat`↔ℤ square cast -/

/-- `↑(sqDistNat a b) = (↑a − ↑b)²` over ℤ. -/
theorem sqDistNat_cast (a b : Nat) :
    Int.ofNat (sqDistNat a b) = (Int.ofNat a - Int.ofNat b) * (Int.ofNat a - Int.ofNat b) := by
  rcases Nat.le_total b a with h | h
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have hsd : sqDistNat (b + d) b = d * d := by
      unfold sqDistNat
      have h1 : b + d - b = d := by
        rw [Nat.add_comm b d]; exact E213.Tactic.NatHelper.add_sub_cancel_right d b
      have h2 : b - (b + d) = 0 := by
        have e := E213.Tactic.NatHelper.add_sub_add_left b 0 d
        rw [Nat.add_zero, Nat.zero_sub] at e; exact e
      rw [h1, h2, Nat.zero_mul, Nat.add_zero]
    have hm : Int.ofNat (d * d) = Int.ofNat d * Int.ofNat d := Int.ofNat_mul d d
    have ha : Int.ofNat (b + d) = Int.ofNat b + Int.ofNat d := Int.ofNat_add b d
    rw [hsd, hm, ha]; ring_intZ
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have hsd : sqDistNat a (a + d) = d * d := by
      unfold sqDistNat
      have h1 : a + d - a = d := by
        rw [Nat.add_comm a d]; exact E213.Tactic.NatHelper.add_sub_cancel_right d a
      have h2 : a - (a + d) = 0 := by
        have e := E213.Tactic.NatHelper.add_sub_add_left a 0 d
        rw [Nat.add_zero, Nat.zero_sub] at e; exact e
      rw [h1, h2, Nat.zero_mul, Nat.zero_add]
    have hm : Int.ofNat (d * d) = Int.ofNat d * Int.ofNat d := Int.ofNat_mul d d
    have ha : Int.ofNat (a + d) = Int.ofNat a + Int.ofNat d := Int.ofNat_add a d
    rw [hsd, hm, ha]; ring_intZ

/-! ## §2 — the pointwise energy-dissipation bound, in `Nat` -/

/-- ★★ **Pointwise energy dissipation (`Nat`).**  For four consecutive grid values,

      `sqDistNat (q+2r+s) (p+2q+r) ≤ 4·(sqDistNat q p + 2·sqDistNat r q + sqDistNat s r)`.

    The left side is the squared edge-difference of the lazy-stepped field; the right is `4×` the
    lazy-weighted edge gradient energies.  `Nat`↔ℤ image of `lazy_energy_pointwise`. -/
theorem lazy_energy_pointwise_nat (p q r s : Nat) :
    sqDistNat (q + 2 * r + s) (p + 2 * q + r)
      ≤ 4 * (sqDistNat q p + 2 * sqDistNat r q + sqDistNat s r) := by
  apply Order.le_of_ofNat_le
  have c2 : (Int.ofNat 2 : Int) = 2 := rfl
  have c4 : (Int.ofNat 4 : Int) = 4 := rfl
  -- cast the two compound lazy-step values (term-mode casts, then rw)
  have eq1 : Int.ofNat (q + 2 * r + s)
      = Int.ofNat q + 2 * Int.ofNat r + Int.ofNat s := by
    have t1 : Int.ofNat (q + 2 * r + s) = Int.ofNat (q + 2 * r) + Int.ofNat s :=
      Int.ofNat_add (q + 2 * r) s
    have t2 : Int.ofNat (q + 2 * r) = Int.ofNat q + Int.ofNat (2 * r) := Int.ofNat_add q (2 * r)
    have t3 : Int.ofNat (2 * r) = Int.ofNat 2 * Int.ofNat r := Int.ofNat_mul 2 r
    rw [t1, t2, t3, c2]
  have eq2 : Int.ofNat (p + 2 * q + r)
      = Int.ofNat p + 2 * Int.ofNat q + Int.ofNat r := by
    have t1 : Int.ofNat (p + 2 * q + r) = Int.ofNat (p + 2 * q) + Int.ofNat r :=
      Int.ofNat_add (p + 2 * q) r
    have t2 : Int.ofNat (p + 2 * q) = Int.ofNat p + Int.ofNat (2 * q) := Int.ofNat_add p (2 * q)
    have t3 : Int.ofNat (2 * q) = Int.ofNat 2 * Int.ofNat q := Int.ofNat_mul 2 q
    rw [t1, t2, t3, c2]
  -- LHS image
  have hL : Int.ofNat (sqDistNat (q + 2 * r + s) (p + 2 * q + r))
      = (Int.ofNat s + Int.ofNat r - Int.ofNat q - Int.ofNat p)
        * (Int.ofNat s + Int.ofNat r - Int.ofNat q - Int.ofNat p) := by
    rw [sqDistNat_cast, eq1, eq2]; ring_intZ
  -- RHS image
  have hR : Int.ofNat (4 * (sqDistNat q p + 2 * sqDistNat r q + sqDistNat s r))
      = 4 * ((Int.ofNat q - Int.ofNat p) * (Int.ofNat q - Int.ofNat p)
            + 2 * ((Int.ofNat r - Int.ofNat q) * (Int.ofNat r - Int.ofNat q))
            + (Int.ofNat s - Int.ofNat r) * (Int.ofNat s - Int.ofNat r)) := by
    have u1 : Int.ofNat (4 * (sqDistNat q p + 2 * sqDistNat r q + sqDistNat s r))
        = Int.ofNat 4 * Int.ofNat (sqDistNat q p + 2 * sqDistNat r q + sqDistNat s r) :=
      Int.ofNat_mul 4 _
    have u2 : Int.ofNat (sqDistNat q p + 2 * sqDistNat r q + sqDistNat s r)
        = Int.ofNat (sqDistNat q p + 2 * sqDistNat r q) + Int.ofNat (sqDistNat s r) :=
      Int.ofNat_add (sqDistNat q p + 2 * sqDistNat r q) (sqDistNat s r)
    have u3 : Int.ofNat (sqDistNat q p + 2 * sqDistNat r q)
        = Int.ofNat (sqDistNat q p) + Int.ofNat (2 * sqDistNat r q) :=
      Int.ofNat_add (sqDistNat q p) (2 * sqDistNat r q)
    have u4 : Int.ofNat (2 * sqDistNat r q) = Int.ofNat 2 * Int.ofNat (sqDistNat r q) :=
      Int.ofNat_mul 2 (sqDistNat r q)
    rw [u1, c4, u2, u3, u4, c2, sqDistNat_cast q p, sqDistNat_cast r q, sqDistNat_cast s r]
  rw [hL, hR]
  exact lazy_energy_pointwise (Int.ofNat p) (Int.ofNat q) (Int.ofNat r) (Int.ofNat s)

/-! ## §3 — the energy decay -/

/-- The "left" edge-gradient energy sums to `E(u) = gridSum n (E-integrand)` (shift invariance
    + `leftNbr ∘ rightNbr = id`). -/
private theorem energy_shift_left (n : Nat) (u : Nat → Nat) :
    gridSum n (fun x => sqDistNat (u x) (u (leftNbr n x)))
      = gridSum n (fun x => sqDistNat (u (rightNbr n x)) (u x)) := by
  rw [← gridSum_rightNbr n (fun x => sqDistNat (u x) (u (leftNbr n x)))]
  apply gridSum_congr; intro x hx
  rw [leftNbr_rightNbr n x hx]

/-- The "right" edge-gradient energy sums to `E(u)` (it is the `E-integrand` precomposed with the
    rotation). -/
private theorem energy_shift_right (n : Nat) (u : Nat → Nat) :
    gridSum n (fun x => sqDistNat (u (rightNbr n (rightNbr n x))) (u (rightNbr n x)))
      = gridSum n (fun x => sqDistNat (u (rightNbr n x)) (u x)) :=
  gridSum_rightNbr n (fun x => sqDistNat (u (rightNbr n x)) (u x))

/-- ★★★★ **Dirichlet energy decay.**  `E(lazyStep u) ≤ 16·E(u)` on the periodic grid — the lazy
    heat step does not increase the (averaged) energy.  The L²-method conclusion: the discrete
    heat flow dissipates the Dirichlet energy, the analytic engine behind smoothing / convergence
    to equilibrium.  Assembled from `gridSum_le` + the pointwise dissipation + shift-invariance. -/
theorem lazy_energy_decay (n : Nat) (u : Nat → Nat) :
    dirichletEnergy n (lazyHeatStepNum n u) ≤ 16 * dirichletEnergy n u := by
  unfold dirichletEnergy
  -- step 1: pointwise bound under the grid sum
  have hbound : gridSum n (fun x =>
        sqDistNat (lazyHeatStepNum n u (rightNbr n x)) (lazyHeatStepNum n u x))
      ≤ gridSum n (fun x => 4 * (sqDistNat (u x) (u (leftNbr n x))
            + 2 * sqDistNat (u (rightNbr n x)) (u x)
            + sqDistNat (u (rightNbr n (rightNbr n x))) (u (rightNbr n x)))) := by
    apply gridSum_le
    intro x hx
    have hWr : lazyHeatStepNum n u (rightNbr n x)
        = u x + 2 * u (rightNbr n x) + u (rightNbr n (rightNbr n x)) := by
      show u (leftNbr n (rightNbr n x)) + 2 * u (rightNbr n x)
            + u (rightNbr n (rightNbr n x))
          = u x + 2 * u (rightNbr n x) + u (rightNbr n (rightNbr n x))
      rw [leftNbr_rightNbr n x hx]
    rw [hWr]
    exact lazy_energy_pointwise_nat (u (leftNbr n x)) (u x) (u (rightNbr n x))
      (u (rightNbr n (rightNbr n x)))
  -- step 2: the RHS sum = 16·E(u)
  refine Nat.le_trans hbound (Nat.le_of_eq ?_)
  rw [gridSum_mul_left n 4 (fun x => sqDistNat (u x) (u (leftNbr n x))
        + 2 * sqDistNat (u (rightNbr n x)) (u x)
        + sqDistNat (u (rightNbr n (rightNbr n x))) (u (rightNbr n x))),
      gridSum_add n (fun x => sqDistNat (u x) (u (leftNbr n x))
        + 2 * sqDistNat (u (rightNbr n x)) (u x))
        (fun x => sqDistNat (u (rightNbr n (rightNbr n x))) (u (rightNbr n x))),
      gridSum_add n (fun x => sqDistNat (u x) (u (leftNbr n x)))
        (fun x => 2 * sqDistNat (u (rightNbr n x)) (u x)),
      gridSum_two_mul n (fun x => sqDistNat (u (rightNbr n x)) (u x)),
      energy_shift_left n u, energy_shift_right n u]
  ring_nat

/-! ## §4 — L² norm contraction (companion to energy decay) -/

/-- Pointwise L²-Jensen in `Nat`: `(a+2b+c)² ≤ 4(a²+2b²+c²)` (no subtraction — cast of
    `lazyHeatStep_l2_jensen`). -/
theorem lazy_l2_pointwise_nat (a b c : Nat) :
    (a + 2 * b + c) * (a + 2 * b + c) ≤ 4 * (a * a + 2 * (b * b) + c * c) := by
  have c2 : (Int.ofNat 2 : Int) = 2 := rfl
  have c4 : (Int.ofNat 4 : Int) = 4 := rfl
  have eA : Int.ofNat (a + 2 * b + c) = Int.ofNat a + 2 * Int.ofNat b + Int.ofNat c := by
    have t1 : Int.ofNat (a + 2 * b + c) = Int.ofNat (a + 2 * b) + Int.ofNat c :=
      Int.ofNat_add (a + 2 * b) c
    have t2 : Int.ofNat (a + 2 * b) = Int.ofNat a + Int.ofNat (2 * b) := Int.ofNat_add a (2 * b)
    have t3 : Int.ofNat (2 * b) = Int.ofNat 2 * Int.ofNat b := Int.ofNat_mul 2 b
    rw [t1, t2, t3, c2]
  have hL : Int.ofNat ((a + 2 * b + c) * (a + 2 * b + c))
      = (Int.ofNat a + 2 * Int.ofNat b + Int.ofNat c)
        * (Int.ofNat a + 2 * Int.ofNat b + Int.ofNat c) := by
    have hm : Int.ofNat ((a + 2 * b + c) * (a + 2 * b + c))
        = Int.ofNat (a + 2 * b + c) * Int.ofNat (a + 2 * b + c) :=
      Int.ofNat_mul (a + 2 * b + c) (a + 2 * b + c)
    rw [hm, eA]
  have hR : Int.ofNat (4 * (a * a + 2 * (b * b) + c * c))
      = 4 * (Int.ofNat a * Int.ofNat a + 2 * (Int.ofNat b * Int.ofNat b)
            + Int.ofNat c * Int.ofNat c) := by
    have u1 : Int.ofNat (4 * (a * a + 2 * (b * b) + c * c))
        = Int.ofNat 4 * Int.ofNat (a * a + 2 * (b * b) + c * c) :=
      Int.ofNat_mul 4 _
    have u2 : Int.ofNat (a * a + 2 * (b * b) + c * c)
        = Int.ofNat (a * a + 2 * (b * b)) + Int.ofNat (c * c) :=
      Int.ofNat_add (a * a + 2 * (b * b)) (c * c)
    have u3 : Int.ofNat (a * a + 2 * (b * b))
        = Int.ofNat (a * a) + Int.ofNat (2 * (b * b)) := Int.ofNat_add (a * a) (2 * (b * b))
    have u4 : Int.ofNat (2 * (b * b)) = Int.ofNat 2 * Int.ofNat (b * b) := Int.ofNat_mul 2 (b * b)
    have u5 : Int.ofNat (a * a) = Int.ofNat a * Int.ofNat a := Int.ofNat_mul a a
    have u6 : Int.ofNat (b * b) = Int.ofNat b * Int.ofNat b := Int.ofNat_mul b b
    have u7 : Int.ofNat (c * c) = Int.ofNat c * Int.ofNat c := Int.ofNat_mul c c
    rw [u1, c4, u2, u3, u4, c2, u5, u6, u7]
  have key := lazyHeatStep_l2_jensen (Int.ofNat a) (Int.ofNat b) (Int.ofNat c)
  rw [← hL, ← hR] at key
  exact Order.le_of_ofNat_le key

/-- ★★★★ **L² norm contraction**: `Σ_x (lazyStep u)² ≤ 16·Σ_x u²` — the lazy heat step does not
    increase the (averaged) L² norm of the field (`16 = 4²` is the stencil normalization).  The
    L²-stability companion of the energy decay; pure-product version (no gradient/`Nat`-subtraction). -/
theorem lazy_l2_norm_bound (n : Nat) (u : Nat → Nat) :
    gridSum n (fun x => lazyHeatStepNum n u x * lazyHeatStepNum n u x)
      ≤ 16 * gridSum n (fun x => u x * u x) := by
  have hbound :
      gridSum n (fun x => lazyHeatStepNum n u x * lazyHeatStepNum n u x)
      ≤ gridSum n (fun x => 4 * (u (leftNbr n x) * u (leftNbr n x)
            + 2 * (u x * u x) + u (rightNbr n x) * u (rightNbr n x))) := by
    apply gridSum_le
    intro x _
    exact lazy_l2_pointwise_nat (u (leftNbr n x)) (u x) (u (rightNbr n x))
  refine Nat.le_trans hbound (Nat.le_of_eq ?_)
  rw [gridSum_mul_left n 4 (fun x => u (leftNbr n x) * u (leftNbr n x)
        + 2 * (u x * u x) + u (rightNbr n x) * u (rightNbr n x)),
      gridSum_add n (fun x => u (leftNbr n x) * u (leftNbr n x) + 2 * (u x * u x))
        (fun x => u (rightNbr n x) * u (rightNbr n x)),
      gridSum_add n (fun x => u (leftNbr n x) * u (leftNbr n x)) (fun x => 2 * (u x * u x)),
      gridSum_two_mul n (fun x => u x * u x),
      gridSum_leftNbr n (fun y => u y * u y), gridSum_rightNbr n (fun y => u y * u y)]
  ring_nat

end E213.Lib.Math.Analysis.ODE.HeatEq.EnergyDecay
