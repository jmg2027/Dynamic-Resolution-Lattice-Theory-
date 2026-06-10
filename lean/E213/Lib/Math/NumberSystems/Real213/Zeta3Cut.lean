import E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic
import E213.Lib.Math.NumberSystems.Real213.AbCutSeq
import E213.Lib.Math.NumberSystems.Real213.RateStratification
import E213.Meta.Nat.PolyNat

/-!
# Zeta3Cut — ζ(3) as a constructed fold (an `AbCutSeq` from the Apéry recurrence)

The Apéry zeta tower (`Cauchy/DepthAperyCubic`) pinned the ζ(3) recurrence's
coefficient *degrees*; this file makes the recurrence actually **generate the
convergents** and folds them into a `Real213` cut.  ζ(3) is thereby a cut pointed
at by its own holonomic approximant sequence — a constructed fold, not an
irreducible residue: the genuine residue is outside every view's image
(`FlatOntologyClosure.object1_not_surjective`); a holonomic real is reached by
its own fold.

**The presentation.**  The Apéry recurrence `n³·uₙ = (34n³−51n²+27n−5)·uₙ₋₁ −
(n−1)³·uₙ₋₂` has rational solutions; clearing by `(n!)³` (set `Pₙ = uₙ·(n!)³`)
gives the all-`ℕ` two-term form at `n = m+2`

    P_{m+2} = aperyLead m · P_{m+1} − (aperyBot m)² · P_m

(`aperyLead`/`aperyBot` are *the* `DepthAperyCubic` coefficients, reused).  The
generic orbit is `aperyOrbit x0 x1`; numerator `zeta3Num = aperyOrbit 0 6` and
denominator `zeta3Den = aperyOrbit 1 5` give the genuine Apéry convergents
`zeta3Num n / zeta3Den n = aₙ/bₙ → ζ(3)` (the `(n!)³` cancels in the ratio).

  * **Engine** (`aperyOrbit_inv`/`aperyOrbit_exact`): a growth invariant
    `(m+1)³·xₘ ≤ xₘ₊₁` shows the `ℕ` subtraction never truncates — the recurrence
    is exact, from the single seed condition `x0 + 8·x1 ≤ 117·x1`.
  * **Casoratian in closed form** (`zeta3_cross_det`): consecutive convergents
    differ by exactly `aperyCasDet m` (`= 6·(m!)⁶`) in cross-product — the
    sign-definite ζ(3) Casoratian of `CasoratianStep`, here as an exact `ℕ`
    identity.  Monotonicity is its corollary.
  * **Fold** (`zeta3Ab : AbCutSeq`): the convergents are a monotone
    positive-denominator ab-sequence, so the whole cut interface (each layer a
    `ValidCut`, nesting, eventual constancy, completion to a `ValidCut` limit)
    applies, and the limit inherits the localization
    **ζ(3) ∈ (601/500, 1203/1000]** — `1.2020 < ζ(3) ≤ 1.2030` (true value
    `1.20205690…`), via the linear-combination engine `aperyOrbit_linear`
    (upper bounds are themselves orbits of the same recurrence).

**Honest modulus posture.**  This factorial-cleared presentation is
**rate-free**: its cross-determinant `aperyCasDet m = 6·(m!)⁶` overtakes the
denominator's growth quantum (`zeta3_presentation_overtakes`, via
`RateStratification.overtake_breaks_layer` at layer 9), so the
`holonomic_modulus.md` generator does not apply *to this presentation* and the
completion modulus stays a hypothesis, as for π/Wallis.  Holonomicity-with-rate
is a property of the **pointing**, not the real
(`PresentationDependence.crossDetSmall_is_presentation_dependent`).  The
rate-carrying presentation is the *reduced* one (denominators `2·lcm(1..n)³·bₙ`),
whose ∅-axiom construction needs exactly the two classical Apéry arithmetic
inputs — integrality of the reduced numerators and `lcm(1..n) < 3ⁿ` — recorded on
the frontier board.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Zeta3Cut

open E213.Theory (Raw)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.Analysis.Cauchy.Archimedean (orderProj)
open E213.Lib.Math.Analysis.Cauchy.PellSeq (abLens_witness)
open E213.Lib.Math.Analysis.Cauchy.MonotonicBounded (IsAbMonotonic IsAbPositiveB)
open E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic (aperyLead aperyTop aperyBot apery_cubic_rung)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.NumberSystems.Real213 (AbCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)
open E213.Lib.Math.NumberSystems.Real213.RateStratification (Dominates overtake_breaks_layer)
open E213.Meta.Nat.PolyNat (poly_id)
open E213.Tactic.NatHelper (add_mul mul_assoc mul_left_comm sub_add_cancel
  le_sub_of_add_le add_right_cancel)

/-! ## §1 — the factorial-cleared Apéry orbit -/

/-- **The factorial-cleared Apéry orbit**: `x_{m+2} = aperyLead m · x_{m+1} −
    (aperyBot m)² · x_m`, the ζ(3) recurrence `n³uₙ = c(n)uₙ₋₁ − (n−1)³uₙ₋₂`
    cleared by `(n!)³` at `n = m+2`.  All-`ℕ`; exactness of the truncating
    subtraction is *proved* (`aperyOrbit_exact`), not assumed. -/
def aperyOrbit (x0 x1 : Nat) : Nat → Nat
  | 0 => x0
  | 1 => x1
  | m+2 => aperyLead m * aperyOrbit x0 x1 (m+1) - aperyBot m * aperyBot m * aperyOrbit x0 x1 m

/-- The trailing coefficient is below the leading-quotient coefficient:
    `(m+1)³ ≤ 34m³+153m²+231m+117`. -/
theorem aperyBot_le_lead (m : Nat) : aperyBot m ≤ aperyLead m := by
  have h : aperyLead m = aperyBot m + (33*m*m*m + 150*m*m + 228*m + 116) :=
    poly_id
      (.add (.add (.add (.mul (.mul (.mul (.C 34) .X) .X) .X) (.mul (.mul (.C 153) .X) .X))
                  (.mul (.C 231) .X)) (.C 117))
      (.add (.mul (.mul (.add .X (.C 1)) (.add .X (.C 1))) (.add .X (.C 1)))
            (.add (.add (.add (.mul (.mul (.mul (.C 33) .X) .X) .X) (.mul (.mul (.C 150) .X) .X))
                        (.mul (.C 228) .X)) (.C 116)))
      rfl m
  rw [h]; exact Nat.le_add_right _ _

/-- Two consecutive trailing cubes still fit below the leading-quotient
    coefficient: `(m+2)³ + (m+1)³ ≤ 34m³+153m²+231m+117`.  The growth-invariant
    step inequality. -/
theorem aperyBots_le_lead (m : Nat) : aperyBot (m+1) + aperyBot m ≤ aperyLead m := by
  have h : aperyLead m
      = (aperyBot (m+1) + aperyBot m) + (32*m*m*m + 144*m*m + 216*m + 108) :=
    poly_id
      (.add (.add (.add (.mul (.mul (.mul (.C 34) .X) .X) .X) (.mul (.mul (.C 153) .X) .X))
                  (.mul (.C 231) .X)) (.C 117))
      (.add (.add (.mul (.mul (.add (.add .X (.C 1)) (.C 1)) (.add (.add .X (.C 1)) (.C 1)))
                        (.add (.add .X (.C 1)) (.C 1)))
                  (.mul (.mul (.add .X (.C 1)) (.add .X (.C 1))) (.add .X (.C 1))))
            (.add (.add (.add (.mul (.mul (.mul (.C 32) .X) .X) .X) (.mul (.mul (.C 144) .X) .X))
                        (.mul (.C 216) .X)) (.C 108)))
      rfl m
  rw [h]; exact Nat.le_add_right _ _

/-- `1 ≤ (m+1)³`. -/
theorem aperyBot_pos (m : Nat) : 1 ≤ aperyBot m := by
  have h1 : 1 ≤ m+1 := Nat.succ_le_succ (Nat.zero_le m)
  calc (1:Nat) = 1*1*1 := rfl
    _ ≤ (m+1)*(m+1)*(m+1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h1

/-! ## §2 — the engine: growth invariant ⟹ exact (non-truncating) recurrence

Seed condition `x0 + 8·x1 ≤ 117·x1`: the first step `x₂ = 117·x1 − x0` already
clears the next cube `8·x1`.  From there the invariant `(m+1)³·xₘ ≤ xₘ₊₁`
self-propagates, because the leading coefficient absorbs two consecutive cubes
(`aperyBots_le_lead`). -/

/-- ★ **Growth invariant**: from layer 1 on, each Apéry-orbit step multiplies by
    at least the trailing cube — `aperyBot (t+1) · x_{t+1} ≤ x_{t+2}`. -/
theorem aperyOrbit_inv (x0 x1 : Nat) (hseed : x0 + 8 * x1 ≤ 117 * x1) :
    ∀ t, aperyBot (t+1) * aperyOrbit x0 x1 (t+1) ≤ aperyOrbit x0 x1 (t+2)
  | 0 => by
      show 8 * x1 ≤ 117 * x1 - 1 * x0
      apply le_sub_of_add_le
      rw [Nat.one_mul, Nat.add_comm]
      exact hseed
  | t+1 => by
      have ih := aperyOrbit_inv x0 x1 hseed t
      show aperyBot (t+2) * aperyOrbit x0 x1 (t+2)
        ≤ aperyLead (t+1) * aperyOrbit x0 x1 (t+2)
            - aperyBot (t+1) * aperyBot (t+1) * aperyOrbit x0 x1 (t+1)
      apply le_sub_of_add_le
      have h1 : aperyBot (t+1) * aperyBot (t+1) * aperyOrbit x0 x1 (t+1)
          ≤ aperyBot (t+1) * aperyOrbit x0 x1 (t+2) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ ih
      calc aperyBot (t+2) * aperyOrbit x0 x1 (t+2)
              + aperyBot (t+1) * aperyBot (t+1) * aperyOrbit x0 x1 (t+1)
          ≤ aperyBot (t+2) * aperyOrbit x0 x1 (t+2)
              + aperyBot (t+1) * aperyOrbit x0 x1 (t+2) := Nat.add_le_add_left h1 _
        _ = (aperyBot (t+2) + aperyBot (t+1)) * aperyOrbit x0 x1 (t+2) :=
            (add_mul _ _ _).symm
        _ ≤ aperyLead (t+1) * aperyOrbit x0 x1 (t+2) :=
            Nat.mul_le_mul_right _ (aperyBots_le_lead (t+1))

/-- ★★ **Exactness**: the `ℕ` subtraction in the orbit never truncates — the
    recurrence holds as the additive identity
    `x_{m+2} + (aperyBot m)²·x_m = aperyLead m · x_{m+1}`. -/
theorem aperyOrbit_exact (x0 x1 : Nat) (hseed : x0 + 8 * x1 ≤ 117 * x1) :
    ∀ m, aperyOrbit x0 x1 (m+2) + aperyBot m * aperyBot m * aperyOrbit x0 x1 m
       = aperyLead m * aperyOrbit x0 x1 (m+1)
  | 0 => by
      show 117 * x1 - 1 * x0 + 1 * x0 = 117 * x1
      apply sub_add_cancel
      rw [Nat.one_mul]
      exact Nat.le_trans (Nat.le_add_right x0 (8 * x1)) hseed
  | m+1 => by
      show aperyLead (m+1) * aperyOrbit x0 x1 (m+2)
            - aperyBot (m+1) * aperyBot (m+1) * aperyOrbit x0 x1 (m+1)
            + aperyBot (m+1) * aperyBot (m+1) * aperyOrbit x0 x1 (m+1)
          = aperyLead (m+1) * aperyOrbit x0 x1 (m+2)
      apply sub_add_cancel
      calc aperyBot (m+1) * aperyBot (m+1) * aperyOrbit x0 x1 (m+1)
          = aperyBot (m+1) * (aperyBot (m+1) * aperyOrbit x0 x1 (m+1)) := mul_assoc _ _ _
        _ ≤ aperyBot (m+1) * aperyOrbit x0 x1 (m+2) :=
            Nat.mul_le_mul_left _ (aperyOrbit_inv x0 x1 hseed m)
        _ ≤ aperyLead (m+1) * aperyOrbit x0 x1 (m+2) :=
            Nat.mul_le_mul_right _ (aperyBot_le_lead (m+1))

/-- Positivity from layer 1 on (layer 0 may seed `0`, as the numerator does). -/
theorem aperyOrbit_pos (x0 x1 : Nat) (hx1 : 1 ≤ x1) (hseed : x0 + 8 * x1 ≤ 117 * x1) :
    ∀ m, 1 ≤ aperyOrbit x0 x1 (m+1)
  | 0 => hx1
  | t+1 =>
      Nat.le_trans
        (calc (1:Nat) = 1*1 := rfl
          _ ≤ aperyBot (t+1) * aperyOrbit x0 x1 (t+1) :=
              Nat.mul_le_mul (aperyBot_pos (t+1)) (aperyOrbit_pos x0 x1 hx1 hseed t))
        (aperyOrbit_inv x0 x1 hseed t)

/-! ## §3 — the ζ(3) convergents and their closed-form Casoratian -/

/-- ζ(3) convergent **numerators**, factorial-cleared: `zeta3Num n = aₙ·(n!)³`
    (`a₀ = 0`, `a₁ = 6`).  `zeta3Num n / zeta3Den n = aₙ/bₙ → ζ(3)`. -/
def zeta3Num : Nat → Nat := aperyOrbit 0 6

/-- ζ(3) convergent **denominators**, factorial-cleared: `zeta3Den n = bₙ·(n!)³`
    where `bₙ` are the Apéry numbers `1, 5, 73, 1445, …`. -/
def zeta3Den : Nat → Nat := aperyOrbit 1 5

private theorem seedNum : (0:Nat) + 8 * 6 ≤ 117 * 6 := by decide
private theorem seedDen : (1:Nat) + 8 * 5 ≤ 117 * 5 := by decide

theorem zeta3Num_pos (n : Nat) : 1 ≤ zeta3Num (n+1) :=
  aperyOrbit_pos 0 6 (by decide) seedNum n

theorem zeta3Den_pos (n : Nat) : 1 ≤ zeta3Den (n+1) :=
  aperyOrbit_pos 1 5 (by decide) seedDen n

/-- **The ζ(3) Casoratian, closed form**: `aperyCasDet m = 6·(m!)⁶`, by the
    recursion `C_{m+1} = (aperyBot m)²·C_m` from `C₀ = 6` — the sign-definite
    cube-product telescoping of `CasoratianStep` §2, here as a value. -/
def aperyCasDet : Nat → Nat
  | 0 => 6
  | m+1 => aperyBot m * aperyBot m * aperyCasDet m

/-- ★★★ **The cross-determinant of the ζ(3) convergents is exactly the
    Casoratian**: `zeta3Num (m+1)·zeta3Den m = zeta3Num m·zeta3Den (m+1) +
    aperyCasDet m`, an exact `ℕ` identity for every `m`.  Strict monotonicity of
    the convergents (and the divergence-ladder `W`-object of this presentation)
    in one stroke.  The signed classical statement `Cₙ = 6/n³` (after the `(n!)³`
    un-clearing) is its shadow. -/
theorem zeta3_cross_det :
    ∀ m, zeta3Num (m+1) * zeta3Den m = zeta3Num m * zeta3Den (m+1) + aperyCasDet m
  | 0 => by decide
  | m+1 => by
      have hP : zeta3Num (m+2) + aperyBot m * aperyBot m * zeta3Num m
              = aperyLead m * zeta3Num (m+1) := aperyOrbit_exact 0 6 seedNum m
      have hQ : zeta3Den (m+2) + aperyBot m * aperyBot m * zeta3Den m
              = aperyLead m * zeta3Den (m+1) := aperyOrbit_exact 1 5 seedDen m
      have ih := zeta3_cross_det m
      show zeta3Num (m+2) * zeta3Den (m+1)
         = zeta3Num (m+1) * zeta3Den (m+2)
             + aperyBot m * aperyBot m * aperyCasDet m
      -- multiply the two exactness identities into the cross products
      have e1 : (zeta3Num (m+2) + aperyBot m * aperyBot m * zeta3Num m) * zeta3Den (m+1)
              = (aperyLead m * zeta3Num (m+1)) * zeta3Den (m+1) := by rw [hP]
      have e2 : zeta3Num (m+1) * (zeta3Den (m+2) + aperyBot m * aperyBot m * zeta3Den m)
              = zeta3Num (m+1) * (aperyLead m * zeta3Den (m+1)) := by rw [hQ]
      have e3 : (aperyLead m * zeta3Num (m+1)) * zeta3Den (m+1)
              = zeta3Num (m+1) * (aperyLead m * zeta3Den (m+1)) :=
        (mul_assoc _ _ _).trans (mul_left_comm _ _ _).symm
      have e4 : (zeta3Num (m+2) + aperyBot m * aperyBot m * zeta3Num m) * zeta3Den (m+1)
              = zeta3Num (m+1) * (zeta3Den (m+2) + aperyBot m * aperyBot m * zeta3Den m) :=
        e1.trans (e3.trans e2.symm)
      have eL : (zeta3Num (m+2) + aperyBot m * aperyBot m * zeta3Num m) * zeta3Den (m+1)
              = zeta3Num (m+2) * zeta3Den (m+1)
                  + aperyBot m * aperyBot m * (zeta3Num m * zeta3Den (m+1)) := by
        rw [add_mul, mul_assoc (aperyBot m * aperyBot m) (zeta3Num m) (zeta3Den (m+1))]
      have eR : zeta3Num (m+1) * (zeta3Den (m+2) + aperyBot m * aperyBot m * zeta3Den m)
              = zeta3Num (m+1) * zeta3Den (m+2)
                  + aperyBot m * aperyBot m * (zeta3Num (m+1) * zeta3Den m) := by
        rw [Nat.mul_add, mul_left_comm (zeta3Num (m+1)) (aperyBot m * aperyBot m) (zeta3Den m)]
      have e5 : zeta3Num (m+2) * zeta3Den (m+1)
                  + aperyBot m * aperyBot m * (zeta3Num m * zeta3Den (m+1))
              = zeta3Num (m+1) * zeta3Den (m+2)
                  + aperyBot m * aperyBot m
                      * (zeta3Num m * zeta3Den (m+1) + aperyCasDet m) := by
        rw [← ih]
        exact eL.symm.trans (e4.trans eR)
      have e6 : zeta3Num (m+2) * zeta3Den (m+1)
                  + aperyBot m * aperyBot m * (zeta3Num m * zeta3Den (m+1))
              = (zeta3Num (m+1) * zeta3Den (m+2)
                    + aperyBot m * aperyBot m * aperyCasDet m)
                  + aperyBot m * aperyBot m * (zeta3Num m * zeta3Den (m+1)) := by
        rw [e5, Nat.mul_add (aperyBot m * aperyBot m) (zeta3Num m * zeta3Den (m+1)) (aperyCasDet m),
            ← Nat.add_assoc,
            Nat.add_assoc (zeta3Num (m+1) * zeta3Den (m+2))
              (aperyBot m * aperyBot m * (zeta3Num m * zeta3Den (m+1)))
              (aperyBot m * aperyBot m * aperyCasDet m),
            Nat.add_comm (aperyBot m * aperyBot m * (zeta3Num m * zeta3Den (m+1)))
              (aperyBot m * aperyBot m * aperyCasDet m),
            ← Nat.add_assoc]
      exact add_right_cancel e6

/-! ## §4 — linear combinations of orbits: the upper-bracket engine

The recurrence is linear, so any `ℕ`-linear relation among seeds propagates to
the whole orbits.  An upper bound `ζ(3) ≤ u/v` is the statement that the slack
`u·bₙ − v·aₙ` is itself a (nonnegative) orbit — Nat-typing *is* the proof. -/

/-- ★★ **Orbit linearity**: if `v·x + t = u·y` holds at both seeds, it holds at
    every layer.  (All three orbits exact via their seed conditions.) -/
theorem aperyOrbit_linear (u v x0 x1 y0 y1 t0 t1 : Nat)
    (hx : x0 + 8 * x1 ≤ 117 * x1) (hy : y0 + 8 * y1 ≤ 117 * y1)
    (ht : t0 + 8 * t1 ≤ 117 * t1)
    (h0 : v * x0 + t0 = u * y0) (h1 : v * x1 + t1 = u * y1) :
    ∀ m, v * aperyOrbit x0 x1 m + aperyOrbit t0 t1 m = u * aperyOrbit y0 y1 m := by
  have key : ∀ m,
      (v * aperyOrbit x0 x1 m + aperyOrbit t0 t1 m = u * aperyOrbit y0 y1 m)
      ∧ (v * aperyOrbit x0 x1 (m+1) + aperyOrbit t0 t1 (m+1)
          = u * aperyOrbit y0 y1 (m+1)) := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hxe := aperyOrbit_exact x0 x1 hx k
      have hye := aperyOrbit_exact y0 y1 hy k
      have hte := aperyOrbit_exact t0 t1 ht k
      have hbig : (v * aperyOrbit x0 x1 (k+2) + aperyOrbit t0 t1 (k+2))
            + (aperyBot k * aperyBot k * (v * aperyOrbit x0 x1 k)
                + aperyBot k * aperyBot k * aperyOrbit t0 t1 k)
          = (u * aperyOrbit y0 y1 (k+2))
            + (aperyBot k * aperyBot k * (v * aperyOrbit x0 x1 k)
                + aperyBot k * aperyBot k * aperyOrbit t0 t1 k) := by
        calc (v * aperyOrbit x0 x1 (k+2) + aperyOrbit t0 t1 (k+2))
              + (aperyBot k * aperyBot k * (v * aperyOrbit x0 x1 k)
                  + aperyBot k * aperyBot k * aperyOrbit t0 t1 k)
            = (v * aperyOrbit x0 x1 (k+2)
                  + aperyBot k * aperyBot k * (v * aperyOrbit x0 x1 k))
              + (aperyOrbit t0 t1 (k+2)
                  + aperyBot k * aperyBot k * aperyOrbit t0 t1 k) :=
              Nat.add_add_add_comm _ _ _ _
          _ = (v * aperyOrbit x0 x1 (k+2)
                  + v * (aperyBot k * aperyBot k * aperyOrbit x0 x1 k))
              + (aperyOrbit t0 t1 (k+2)
                  + aperyBot k * aperyBot k * aperyOrbit t0 t1 k) := by
              rw [mul_left_comm (aperyBot k * aperyBot k) v (aperyOrbit x0 x1 k)]
          _ = v * (aperyOrbit x0 x1 (k+2)
                  + aperyBot k * aperyBot k * aperyOrbit x0 x1 k)
              + (aperyOrbit t0 t1 (k+2)
                  + aperyBot k * aperyBot k * aperyOrbit t0 t1 k) := by
              rw [Nat.mul_add v (aperyOrbit x0 x1 (k+2))
                    (aperyBot k * aperyBot k * aperyOrbit x0 x1 k)]
          _ = v * (aperyLead k * aperyOrbit x0 x1 (k+1))
              + aperyLead k * aperyOrbit t0 t1 (k+1) := by rw [hxe, hte]
          _ = aperyLead k * (v * aperyOrbit x0 x1 (k+1))
              + aperyLead k * aperyOrbit t0 t1 (k+1) := by
              rw [mul_left_comm v (aperyLead k) (aperyOrbit x0 x1 (k+1))]
          _ = aperyLead k * (v * aperyOrbit x0 x1 (k+1) + aperyOrbit t0 t1 (k+1)) :=
              (Nat.mul_add _ _ _).symm
          _ = aperyLead k * (u * aperyOrbit y0 y1 (k+1)) := by rw [ih.2]
          _ = u * (aperyLead k * aperyOrbit y0 y1 (k+1)) := mul_left_comm _ _ _
          _ = u * (aperyOrbit y0 y1 (k+2)
                  + aperyBot k * aperyBot k * aperyOrbit y0 y1 k) := by rw [hye]
          _ = u * aperyOrbit y0 y1 (k+2)
              + u * (aperyBot k * aperyBot k * aperyOrbit y0 y1 k) :=
              Nat.mul_add _ _ _
          _ = u * aperyOrbit y0 y1 (k+2)
              + aperyBot k * aperyBot k * (u * aperyOrbit y0 y1 k) := by
              rw [mul_left_comm u (aperyBot k * aperyBot k) (aperyOrbit y0 y1 k)]
          _ = u * aperyOrbit y0 y1 (k+2)
              + aperyBot k * aperyBot k
                  * (v * aperyOrbit x0 x1 k + aperyOrbit t0 t1 k) := by
              rw [← ih.1]
          _ = u * aperyOrbit y0 y1 (k+2)
              + (aperyBot k * aperyBot k * (v * aperyOrbit x0 x1 k)
                  + aperyBot k * aperyBot k * aperyOrbit t0 t1 k) := by
              rw [Nat.mul_add (aperyBot k * aperyBot k) (v * aperyOrbit x0 x1 k)
                    (aperyOrbit t0 t1 k)]
      exact add_right_cancel hbig
  intro m; exact (key m).1

private theorem seed54 : (5:Nat) + 8 * 1 ≤ 117 * 1 := by decide
private theorem seed1203 : (1203:Nat) + 8 * 15 ≤ 117 * 15 := by decide

/-- ★★ **All convergents below `5/4`**: the slack `5·zeta3Den − 4·zeta3Num` is the
    orbit seeded `(5, 1)`, so it is a `ℕ` — `4·zeta3Num m + (slack) = 5·zeta3Den m`. -/
theorem zeta3_below_5_4 (m : Nat) :
    4 * zeta3Num m + aperyOrbit 5 1 m = 5 * zeta3Den m :=
  aperyOrbit_linear 5 4 0 6 1 5 5 1 seedNum seedDen seed54 (by decide) (by decide) m

/-- ★★ **All convergents below `1203/1000`** (sharp: `ζ(3) = 1.20205…`): the slack
    `1203·zeta3Den − 1000·zeta3Num` is the orbit seeded `(1203, 15)`. -/
theorem zeta3_below_1203_1000 (m : Nat) :
    1000 * zeta3Num m + aperyOrbit 1203 15 m = 1203 * zeta3Den m :=
  aperyOrbit_linear 1203 1000 0 6 1 5 1203 15 seedNum seedDen seed1203
    (by decide) (by decide) m

/-! ## §5 — ζ(3) as an `AbCutSeq` (the fold's carrier) -/

/-- The ζ(3) convergent Raw at layer `n` reads `(zeta3Num (n+1), zeta3Den (n+1))`
    (shifted past the seed layer `0/1`, so the numerator is positive). -/
def zeta3Raw (n : Nat) :
    {r : Raw // abLens.view r = (zeta3Num (n+1), zeta3Den (n+1))} :=
  abLens_witness (zeta3Num (n+1) + zeta3Den (n+1)) (zeta3Num (n+1)) (zeta3Den (n+1)) rfl
    (zeta3Num_pos n) (zeta3Den_pos n)

theorem zeta3Raw_view (n : Nat) :
    abLens.view (zeta3Raw n).val = (zeta3Num (n+1), zeta3Den (n+1)) :=
  (zeta3Raw n).property

/-- The ζ(3) convergent Raw sequence. -/
def zeta3RawSeq : Nat → Raw := fun n => (zeta3Raw n).val

/-- The convergents climb: ab-monotone, from the closed-form Casoratian. -/
theorem zeta3_isAbMonotonic : IsAbMonotonic zeta3RawSeq := by
  intro n
  show (abLens.view (zeta3Raw n).val).1 * (abLens.view (zeta3Raw (n+1)).val).2
     ≤ (abLens.view (zeta3Raw (n+1)).val).1 * (abLens.view (zeta3Raw n).val).2
  rw [zeta3Raw_view, zeta3Raw_view]
  show zeta3Num (n+1) * zeta3Den (n+2) ≤ zeta3Num (n+2) * zeta3Den (n+1)
  exact Nat.le.intro (zeta3_cross_det (n+1)).symm

/-- Positive denominators. -/
theorem zeta3_isAbPositiveB : IsAbPositiveB zeta3RawSeq := by
  intro n
  show 1 ≤ (abLens.view (zeta3Raw n).val).2
  rw [zeta3Raw_view]
  exact zeta3Den_pos n

/-- ★★★ **ζ(3)'s Apéry convergents as an `AbCutSeq`** — the fold's carrier.  The
    whole cut interface (layer `ValidCut`s, nesting, eventual constancy,
    completion to a `ValidCut` limit) applies generically. -/
def zeta3Ab : AbCutSeq := ⟨zeta3RawSeq, zeta3_isAbMonotonic, zeta3_isAbPositiveB⟩

/-- **ζ(3)'s cut at layer `n`**: `decide (zeta3Num (n+1)·k ≤ zeta3Den (n+1)·m)`. -/
def zeta3Cut (n : Nat) : Nat → Nat → Bool := zeta3Ab.cut n

/-- Each layer cut is a `ValidCut`. -/
theorem zeta3Cut_valid (n : Nat) : ValidCut (zeta3Cut n) := zeta3Ab.cut_valid n

/-- The `constCut` view of `zeta3Cut`. -/
theorem zeta3Cut_eq (n m k : Nat) :
    zeta3Cut n m k = decide (zeta3Num (n+1) * k ≤ zeta3Den (n+1) * m) := by
  show orderProj m k (abLens.view (zeta3Raw n).val) = _
  rw [zeta3Raw_view]; rfl

/-- **Nesting** for ζ(3), from the generic `AbCutSeq.cut_false_fwd`. -/
theorem zeta3Cut_false_fwd (m k N : Nat) (hN : zeta3Cut N m k = false)
    (i : Nat) (hi : i ≥ N) : zeta3Cut i m k = false :=
  zeta3Ab.cut_false_fwd m k N hN i hi

/-! ## §6 — localization: `601/500 < ζ(3) ≤ 1203/1000` (and the clean `(6/5, 5/4)`) -/

/-- ★★ **ζ(3) ≤ 5/4**: the cut at `5/4` is `true` at every layer. -/
theorem zeta3Cut_at_5_4 (n : Nat) : zeta3Cut n 5 4 = true := by
  rw [zeta3Cut_eq]
  apply decide_eq_true
  show zeta3Num (n+1) * 4 ≤ zeta3Den (n+1) * 5
  rw [Nat.mul_comm (zeta3Num (n+1)) 4, Nat.mul_comm (zeta3Den (n+1)) 5]
  exact Nat.le.intro (zeta3_below_5_4 (n+1))

/-- ★★ **ζ(3) ≤ 1203/1000**: the sharp upper cut is `true` at every layer. -/
theorem zeta3Cut_at_1203_1000 (n : Nat) : zeta3Cut n 1203 1000 = true := by
  rw [zeta3Cut_eq]
  apply decide_eq_true
  show zeta3Num (n+1) * 1000 ≤ zeta3Den (n+1) * 1203
  rw [Nat.mul_comm (zeta3Num (n+1)) 1000, Nat.mul_comm (zeta3Den (n+1)) 1203]
  exact Nat.le.intro (zeta3_below_1203_1000 (n+1))

/-- ★★ **ζ(3) > 6/5**: `false` from layer 1 on (`a₂/b₂ = 351/292 > 6/5` exactly,
    by `decide` — `702·5 = 3510 > 3504 = 584·6` — and nesting). -/
theorem zeta3Cut_below_6_5 (n : Nat) (hn : n ≥ 1) : zeta3Cut n 6 5 = false :=
  zeta3Cut_false_fwd 6 5 1 (by rw [zeta3Cut_eq]; decide) n hn

/-- ★★★ **ζ(3) > 601/500**: `false` from layer 2 on (`a₃/b₃` exceeds `1.2020`
    exactly, by `decide` at layer 2 + nesting). -/
theorem zeta3Cut_below_601_500 (n : Nat) (hn : n ≥ 2) : zeta3Cut n 601 500 = false :=
  zeta3Cut_false_fwd 601 500 2 (by rw [zeta3Cut_eq]; decide) n hn

/-- ★★★ **ζ(3) is strictly inside `(601/500, 1203/1000]`, ∀ tail layer (n ≥ 2)** —
    `1.2020 < ζ(3) ≤ 1.2030` (true value `1.20205690…`). -/
theorem zeta3Cut_in_bracket (n : Nat) (hn : n ≥ 2) :
    zeta3Cut n 601 500 = false ∧ zeta3Cut n 1203 1000 = true :=
  ⟨zeta3Cut_below_601_500 n hn, zeta3Cut_at_1203_1000 n⟩

/-! ## §7 — completion (the `toCauchy` fold; modulus supplied)

Like π (`PiCut` §4) and unlike e (`EulerModulus`): in **this presentation** the
completion modulus is a hypothesis, because the presentation is rate-free
(§8).  The moment a modulus is given, the limit is a `ValidCut` carrying the
bracket. -/

/-- ★★★ **ζ(3)'s completed limit is a real (`ValidCut`)** — for any supplied
    modulus, from `AbCutSeq.toCauchy_limit_valid`. -/
theorem zeta3Limit_valid (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → zeta3Ab.cut i m k = zeta3Ab.cut j m k) :
    ValidCut (zeta3Ab.toCauchy N hc).limit :=
  zeta3Ab.toCauchy_limit_valid N hc

/-- ★★★ **The completed limit inherits the localization** — `false` at `601/500`,
    `true` at `1203/1000`, provided the modulus reached the `n ≥ 2` regime at
    `601/500`. -/
theorem zeta3Limit_in_bracket (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → zeta3Ab.cut i m k = zeta3Ab.cut j m k)
    (h601 : N 601 500 ≥ 2) :
    (zeta3Ab.toCauchy N hc).limit 601 500 = false
    ∧ (zeta3Ab.toCauchy N hc).limit 1203 1000 = true :=
  zeta3Ab.limit_brackets N hc 601 500 1203 1000 2
    (fun n hn => zeta3Cut_below_601_500 n hn) (fun n => zeta3Cut_at_1203_1000 n) h601

/-! ## §8 — the holonomic signature, and the honest rate stratum -/

/-- ★★★ **The fold is the Apéry recurrence** — the cut-sequence's convergent data
    satisfies, exactly over `ℕ`, the order-2 recurrence whose three coefficients
    are the `DepthAperyCubic` degree-3 polynomials (`apery_cubic_rung`:
    `polyDepth 3` for `aperyTop`, `aperyLead`, `aperyBot`).  ζ(3)'s holonomic
    recurrence actually *generates* `zeta3Cut`, completing the
    `Cauchy/DepthAperyCubic` arc from coefficient statistics to a working fold. -/
theorem zeta3_fold_is_apery :
    (∀ m, zeta3Num (m+2) + aperyBot m * aperyBot m * zeta3Num m
        = aperyLead m * zeta3Num (m+1))
    ∧ (∀ m, zeta3Den (m+2) + aperyBot m * aperyBot m * zeta3Den m
        = aperyLead m * zeta3Den (m+1))
    ∧ (polyDepth 3 aperyTop ∧ polyDepth 3 aperyLead ∧ polyDepth 3 aperyBot) :=
  ⟨aperyOrbit_exact 0 6 seedNum, aperyOrbit_exact 1 5 seedDen, apery_cubic_rung⟩

/-- ★★ **This presentation is rate-free** (`RateStratification` overtake): at
    layer 9 the cross-determinant `aperyCasDet 9 = 6·(9!)⁶` already exceeds the
    denominator quantum `10·zeta3Den 10`, so layer 9 is **not** dominated and the
    free-modulus generator (`holonomic_modulus.md`) does not apply to the
    factorial-cleared pair.  Rate is a property of the presentation
    (`PresentationDependence`): the rate-carrying ζ(3) presentation is the
    *reduced* one (`2·lcm(1..n)³·bₙ` denominators), whose ∅-axiom construction =
    the classical Apéry arithmetic (numerator integrality + `lcm < 3ⁿ`) —
    the recorded open frontier. -/
theorem zeta3_presentation_overtakes : ¬ Dominates aperyCasDet zeta3Den 9 :=
  overtake_breaks_layer aperyCasDet 9 (by decide) (by decide)

end E213.Lib.Math.NumberSystems.Real213.Zeta3Cut
