import E213.Lib.Math.Analysis.ODE.HeatEq.Discrete
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# Discrete heat equation — mass conservation on the periodic grid (∅-axiom)

**Marathon P3 infrastructure**.

The discrete heat step is a redistribution: it moves heat between neighbours but creates and
destroys none.  On the length-`n` periodic grid the **total mass** `Σ_{x<n} u(x)` is therefore
conserved (up to the stencil's normalization): `Σ heatStepNum = 2·Σ u`, `Σ lazyHeatStepNum =
4·Σ u` — i.e. the *averaged* total is invariant.  This is the discrete conservation law, the
companion of the maximum principle.

The engine is a finite-grid sum `gridSum n f = Σ_{x<n} f x` with **cyclic-shift invariance**:
the neighbour maps `leftNbr`/`rightNbr` are the two full-cycle rotations of `{0,…,n−1}`, so
re-summing `u` along them returns the same total (`gridSum_rightNbr`, `gridSum_leftNbr`).
`gridSum` is generic finite-sum infrastructure — reusable for the Dirichlet energy `Σ(u_{i+1}−u_i)²`
(P3 proper) — kept here with its first consumer.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.ODE.HeatEq.Discrete

/-! ## §1 — the finite-grid sum -/

/-- `gridSum n f = Σ_{x<n} f x` (peels the top index). -/
def gridSum : Nat → (Nat → Nat) → Nat
  | 0,     _ => 0
  | n + 1, f => gridSum n f + f n

theorem gridSum_succ (n : Nat) (f : Nat → Nat) :
    gridSum (n + 1) f = gridSum n f + f n := rfl

/-- **Congruence**: `gridSum` depends only on the values at `x < n`. -/
theorem gridSum_congr (n : Nat) (f g : Nat → Nat) (h : ∀ x, x < n → f x = g x) :
    gridSum n f = gridSum n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [gridSum_succ, gridSum_succ, h m (Nat.lt_succ_self m),
        ih (fun x hx => h x (Nat.lt_succ_of_lt hx))]

/-- **Additivity**: `Σ (f + g) = Σ f + Σ g`. -/
theorem gridSum_add (n : Nat) (f g : Nat → Nat) :
    gridSum n (fun x => f x + g x) = gridSum n f + gridSum n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show gridSum m (fun x => f x + g x) + (f m + g m)
        = (gridSum m f + f m) + (gridSum m g + g m)
    rw [ih]; ring_nat

/-- **Monotonicity**: pointwise `f ≤ g` on the grid ⟹ `Σ f ≤ Σ g`. -/
theorem gridSum_le (n : Nat) (f g : Nat → Nat) (h : ∀ x, x < n → f x ≤ g x) :
    gridSum n f ≤ gridSum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    rw [gridSum_succ, gridSum_succ]
    exact Nat.add_le_add (ih (fun x hx => h x (Nat.lt_succ_of_lt hx)))
      (h m (Nat.lt_succ_self m))

/-- **Scalar (left)**: `Σ (c·f) = c·Σ f`. -/
theorem gridSum_mul_left (n c : Nat) (f : Nat → Nat) :
    gridSum n (fun x => c * f x) = c * gridSum n f := by
  induction n with
  | zero => exact (Nat.mul_zero c).symm
  | succ m ih => rw [gridSum_succ, gridSum_succ, ih, Nat.mul_add]

/-- **Scalar**: `Σ (2·f) = 2·Σ f`. -/
theorem gridSum_two_mul (n : Nat) (f : Nat → Nat) :
    gridSum n (fun x => 2 * f x) = 2 * gridSum n f := gridSum_mul_left n 2 f

/-- **Constant sum**: `Σ_{x<m} c = m·c`. -/
theorem gridSum_const (m c : Nat) : gridSum m (fun _ => c) = m * c := by
  induction m with
  | zero => exact (Nat.zero_mul c).symm
  | succ k ih =>
    show gridSum k (fun _ => c) + c = (k + 1) * c
    rw [ih]
    ring_nat

/-- **Term ≤ sum**: a single value is at most the whole (`Nat`) grid sum. -/
theorem gridSum_term_le (m : Nat) (f : Nat → Nat) :
    ∀ k, k < m → f k ≤ gridSum m f := by
  induction m with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ p ih =>
    intro k hk
    rw [gridSum_succ]
    rcases Nat.lt_or_ge k p with h | h
    · exact Nat.le_trans (ih k h) (Nat.le_add_right _ _)
    · have hkp : k = p := Nat.le_antisymm (Nat.le_of_lt_succ hk) h
      rw [hkp]
      exact Nat.le_add_left (f p) (gridSum p f)

/-! ## §2 — cyclic-shift invariance -/

/-- Head-shift: `Σ_{x<m} f(x+1) + f 0 = Σ_{x<m+1} f x`.  Moving the head term `f 0` to the
    front of the shifted tail recovers the full sum. -/
theorem gridSum_head_shift (m : Nat) (f : Nat → Nat) :
    gridSum m (fun x => f (x + 1)) + f 0 = gridSum (m + 1) f := by
  induction m with
  | zero => rfl
  | succ k ih =>
    show (gridSum k (fun x => f (x + 1)) + f (k + 1)) + f 0
        = gridSum (k + 1) f + f (k + 1)
    rw [Nat.add_right_comm, ih]

/-- ★★ **Right-shift invariance**: `Σ_{x<n} f(rightNbr n x) = Σ_{x<n} f x`.  `rightNbr`
    rotates `{0,…,n−1}` by `+1`; the wrap `n−1 ↦ 0` is absorbed by `gridSum_head_shift`. -/
theorem gridSum_rightNbr (n : Nat) (f : Nat → Nat) :
    gridSum n (fun x => f (rightNbr n x)) = gridSum n f := by
  cases n with
  | zero => rfl
  | succ m =>
    have hlast : rightNbr (m + 1) m = 0 := by
      show (m + 1) % (m + 1) = 0; exact E213.Meta.Nat.AddMod213.mod_self (m + 1)
    have hcongr : gridSum m (fun x => f (rightNbr (m + 1) x))
                = gridSum m (fun x => f (x + 1)) := by
      apply gridSum_congr
      intro x hx
      have hr : rightNbr (m + 1) x = x + 1 := by
        show (x + 1) % (m + 1) = x + 1; exact Nat.mod_eq_of_lt (Nat.succ_lt_succ hx)
      rw [hr]
    show gridSum m (fun x => f (rightNbr (m + 1) x)) + f (rightNbr (m + 1) m)
        = gridSum (m + 1) f
    rw [hlast, hcongr]; exact gridSum_head_shift m f

/-- `leftNbr` is the inverse of `rightNbr` on the grid: `leftNbr n (rightNbr n x) = x`
    for `x < n`. -/
theorem leftNbr_rightNbr (n x : Nat) (hx : x < n) : leftNbr n (rightNbr n x) = x := by
  cases Nat.lt_or_ge (x + 1) n with
  | inl hlt =>
    have hr : rightNbr n x = x + 1 := by
      show (x + 1) % n = x + 1; exact Nat.mod_eq_of_lt hlt
    have hsub : x + 1 + n - 1 = x + n := by
      rw [Nat.add_right_comm x 1 n, E213.Tactic.NatHelper.add_sub_cancel_right]
    rw [hr]
    show (x + 1 + n - 1) % n = x
    rw [hsub, E213.Tactic.NatHelper.add_self_mod_pure x n, Nat.mod_eq_of_lt hx]
  | inr hge =>
    have heq : x + 1 = n := Nat.le_antisymm hx hge
    have hr : rightNbr n x = 0 := by
      show (x + 1) % n = 0; rw [heq]; exact E213.Meta.Nat.AddMod213.mod_self n
    rw [hr]
    show (0 + n - 1) % n = x
    rw [Nat.zero_add, ← heq, E213.Tactic.NatHelper.add_sub_cancel_right]
    exact Nat.mod_eq_of_lt (Nat.lt_succ_self x)

/-- ★★ **Left-shift invariance**: `Σ_{x<n} f(leftNbr n x) = Σ_{x<n} f x`.  Derived from
    right-shift invariance and `leftNbr ∘ rightNbr = id`. -/
theorem gridSum_leftNbr (n : Nat) (f : Nat → Nat) :
    gridSum n (fun x => f (leftNbr n x)) = gridSum n f := by
  have key := gridSum_rightNbr n (fun y => f (leftNbr n y))
  have hid : gridSum n (fun x => f (leftNbr n (rightNbr n x))) = gridSum n f := by
    apply gridSum_congr; intro x hx; rw [leftNbr_rightNbr n x hx]
  rw [hid] at key; exact key.symm

/-! ## §3 — mass conservation -/

/-- ★★★ **Mass conservation (non-lazy).**  `Σ heatStepNum = 2·Σ u`: the heat step
    redistributes mass without creating or destroying it (the averaged total is invariant). -/
theorem heatStep_mass_conservation (n : Nat) (u : Nat → Nat) :
    gridSum n (heatStepNum n u) = 2 * gridSum n u := by
  have e : (heatStepNum n u) = (fun x => u (leftNbr n x) + u (rightNbr n x)) := rfl
  rw [e, gridSum_add n (fun x => u (leftNbr n x)) (fun x => u (rightNbr n x)),
      gridSum_leftNbr n u, gridSum_rightNbr n u, Nat.two_mul]

/-- ★★★ **Mass conservation (lazy).**  `Σ lazyHeatStepNum = 4·Σ u`. -/
theorem lazyHeatStep_mass_conservation (n : Nat) (u : Nat → Nat) :
    gridSum n (lazyHeatStepNum n u) = 4 * gridSum n u := by
  have e : (lazyHeatStepNum n u)
         = (fun x => u (leftNbr n x) + 2 * u x + u (rightNbr n x)) := rfl
  rw [e, gridSum_add n (fun x => u (leftNbr n x) + 2 * u x) (fun x => u (rightNbr n x)),
      gridSum_add n (fun x => u (leftNbr n x)) (fun x => 2 * u x),
      gridSum_leftNbr n u, gridSum_rightNbr n u, gridSum_two_mul n u]
  ring_nat

/-! ## §4 — discrete summation by parts (the Dirichlet pairing)

The pairing `⟨u, A u⟩ = Σ_x u(x)·(A u)(x)` for the heat operator `A`, computed via cyclic-shift
invariance — the discrete integration-by-parts / Green identity that underlies all energy
estimates.  Pure products, so no `Nat`-subtraction (the obstacle to writing `Σ(u_{x+1}−u_x)²`
directly; the signed Dirichlet energy proper needs the Int213 difference-Lens, P3's next step). -/

/-- The edge correlation is shift-symmetric: `Σ u(x)·u(leftNbr n x) = Σ u(x)·u(rightNbr n x)`.
    Reindex by the rotation (`gridSum_rightNbr`) using `leftNbr ∘ rightNbr = id`. -/
theorem gridSum_mul_shift_symm (n : Nat) (u : Nat → Nat) :
    gridSum n (fun x => u x * u (leftNbr n x))
      = gridSum n (fun x => u x * u (rightNbr n x)) := by
  have h := gridSum_rightNbr n (fun y => u y * u (leftNbr n y))
  have h2 : gridSum n (fun x => u (rightNbr n x) * u (leftNbr n (rightNbr n x)))
          = gridSum n (fun x => u x * u (rightNbr n x)) := by
    apply gridSum_congr; intro x hx
    rw [leftNbr_rightNbr n x hx, Nat.mul_comm]
  exact (h.symm).trans h2

/-- ★★★ **Dirichlet pairing (non-lazy).**  `Σ u·heatStepNum u = 2·Σ u(x)·u(rightNbr x)` — the
    pairing `⟨u, A u⟩` of the field with its heat image equals twice the edge correlation, the
    discrete summation-by-parts identity. -/
theorem heatStep_dirichlet_pairing (n : Nat) (u : Nat → Nat) :
    gridSum n (fun x => u x * heatStepNum n u x)
      = 2 * gridSum n (fun x => u x * u (rightNbr n x)) := by
  rw [gridSum_congr n (fun x => u x * heatStepNum n u x)
        (fun x => u x * u (leftNbr n x) + u x * u (rightNbr n x))
        (fun x _ => Nat.mul_add (u x) (u (leftNbr n x)) (u (rightNbr n x))),
      gridSum_add n (fun x => u x * u (leftNbr n x)) (fun x => u x * u (rightNbr n x)),
      gridSum_mul_shift_symm n u, Nat.two_mul]

/-- ★★★ **Dirichlet pairing (lazy).**  `Σ u·lazyHeatStepNum u = 2·Σ u² + 2·Σ u(x)·u(rightNbr x)`.
    Since (over ℤ) the Dirichlet energy is `E(u) = 2Σu² − 2·corr`, this reads
    `⟨u, lazy u⟩ = 4Σu² − E(u)` — the energy identity in `Nat`-clean additive form. -/
theorem lazyHeatStep_dirichlet_pairing (n : Nat) (u : Nat → Nat) :
    gridSum n (fun x => u x * lazyHeatStepNum n u x)
      = 2 * gridSum n (fun x => u x * u x)
        + 2 * gridSum n (fun x => u x * u (rightNbr n x)) := by
  rw [gridSum_congr n (fun x => u x * lazyHeatStepNum n u x)
        (fun x => u x * u (leftNbr n x) + 2 * (u x * u x) + u x * u (rightNbr n x))
        (fun x _ => by
          show u x * (u (leftNbr n x) + 2 * u x + u (rightNbr n x))
              = u x * u (leftNbr n x) + 2 * (u x * u x) + u x * u (rightNbr n x)
          rw [Nat.mul_add, Nat.mul_add, E213.Tactic.NatHelper.mul_left_comm (u x) 2 (u x)]),
      gridSum_add n (fun x => u x * u (leftNbr n x) + 2 * (u x * u x))
        (fun x => u x * u (rightNbr n x)),
      gridSum_add n (fun x => u x * u (leftNbr n x)) (fun x => 2 * (u x * u x)),
      gridSum_mul_shift_symm n u, gridSum_two_mul n (fun x => u x * u x)]
  ring_nat

/-! ## §5 — the signed Dirichlet energy and the discrete Green identity

`E(u) = Σ_x |u(rightNbr x) − u(x)|²` is sign-aware: `sqDistNat a b` is the true `(a−b)²`
(exactly one of `a−b`, `b−a` is nonzero, so the sum of their squares is `|a−b|²`, dodging the
`Nat`-subtraction truncation of a bare `(a−b)*(a−b)`).  The **Green identity** `E(u) + 2·corr =
2·Σu²` — `E(u) = ⟨u, −Δu⟩` over ℤ — is the foundational energy identity: the Dirichlet form *is*
the energy.  (The `sqDistNat` binomial is a genuine `Nat`-truncation fact, proven by case split;
`ring_nat` closes each sub-free case once the `0*0` term is pruned.) -/

/-- Sign-correct squared difference `|a−b|²` in `Nat`. -/
def sqDistNat (a b : Nat) : Nat := (a - b) * (a - b) + (b - a) * (b - a)

/-- ★★ **Binomial expansion (sign-correct)**: `|a−b|² + 2ab = a² + b²`. -/
theorem sqDistNat_add_two_mul (a b : Nat) :
    sqDistNat a b + 2 * (a * b) = a * a + b * b := by
  unfold sqDistNat
  rcases Nat.le_total b a with h | h
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have h1 : b + d - b = d := by
      rw [Nat.add_comm b d]; exact E213.Tactic.NatHelper.add_sub_cancel_right d b
    have h2 : b - (b + d) = 0 := by
      have e := E213.Tactic.NatHelper.add_sub_add_left b 0 d
      rw [Nat.add_zero, Nat.zero_sub] at e; exact e
    rw [h1, h2, Nat.zero_mul, Nat.add_zero]; ring_nat
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have h1 : a + d - a = d := by
      rw [Nat.add_comm a d]; exact E213.Tactic.NatHelper.add_sub_cancel_right d a
    have h2 : a - (a + d) = 0 := by
      have e := E213.Tactic.NatHelper.add_sub_add_left a 0 d
      rw [Nat.add_zero, Nat.zero_sub] at e; exact e
    rw [h1, h2, Nat.zero_mul, Nat.zero_add]; ring_nat

/-- The discrete Dirichlet energy `E(u) = Σ_x |u(rightNbr x) − u(x)|²`. -/
def dirichletEnergy (n : Nat) (u : Nat → Nat) : Nat :=
  gridSum n (fun x => sqDistNat (u (rightNbr n x)) (u x))

/-- ★★★ **Discrete Green identity** (additive, `Nat`-clean): `E(u) + 2·corr = 2·Σu²`, where
    `corr = Σ u(x)·u(rightNbr x)`.  Over ℤ this reads `E(u) = 2Σu² − 2·corr = ⟨u, −Δu⟩` — the
    Dirichlet form *is* the energy.  The foundational identity behind energy decay. -/
theorem dirichletEnergy_green (n : Nat) (u : Nat → Nat) :
    dirichletEnergy n u + 2 * gridSum n (fun x => u x * u (rightNbr n x))
      = 2 * gridSum n (fun x => u x * u x) := by
  have key : dirichletEnergy n u + gridSum n (fun x => 2 * (u (rightNbr n x) * u x))
      = gridSum n (fun x => u (rightNbr n x) * u (rightNbr n x))
        + gridSum n (fun x => u x * u x) := by
    unfold dirichletEnergy
    rw [← gridSum_add n (fun x => sqDistNat (u (rightNbr n x)) (u x))
            (fun x => 2 * (u (rightNbr n x) * u x)),
        ← gridSum_add n (fun x => u (rightNbr n x) * u (rightNbr n x)) (fun x => u x * u x)]
    apply gridSum_congr; intro x _
    exact sqDistNat_add_two_mul (u (rightNbr n x)) (u x)
  rw [gridSum_two_mul n (fun x => u (rightNbr n x) * u x),
      gridSum_rightNbr n (fun y => u y * u y)] at key
  have hcomm : gridSum n (fun x => u (rightNbr n x) * u x)
             = gridSum n (fun x => u x * u (rightNbr n x)) := by
    apply gridSum_congr; intro x _; exact Nat.mul_comm _ _
  rw [hcomm] at key
  rw [key, ← Nat.two_mul]

end E213.Lib.Math.Analysis.ODE.HeatEq.Discrete
