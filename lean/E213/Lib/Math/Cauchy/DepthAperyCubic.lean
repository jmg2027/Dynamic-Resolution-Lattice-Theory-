import E213.Meta.Nat.PolyNat
import E213.Lib.Math.Cauchy.DepthPRecursiveInstances

/-!
# DepthAperyCubic — the Apéry zeta tower: ζ(2) degree 2, ζ(3) degree 3

`DivergenceDepth`/`DepthPRecursiveInstances` pinned the divergence-depth coefficient
degree of e (degree **1**, linear: ratio `n+1`).  This file adds the two Apéry rungs
above it, the constants whose irrationality Apéry proved by P-recursive (holonomic)
recurrences of **order 2**:

  * **ζ(2) = π²/6**, recurrence `(n+1)²·uₙ₊₁ = (11n²+11n+3)·uₙ + n²·uₙ₋₁` — order 2,
    **degree-2 (quadratic)** coefficients;
  * **ζ(3)**, recurrence `n³·aₙ = (34n³−51n²+27n−5)·aₙ₋₁ − (n−1)³·aₙ₋₂` — order 2,
    **degree-3 (cubic)** coefficients.

Each recurrence coefficient is a discrete polynomial, so its finite-difference depth is
its degree (`newton_polyDepth`'s "degree d ⟹ depth d", pinned concretely here with the
reflection prover `Meta.Nat.PolyNat`).  For ζ(3) the cubic coefficients are reindexed to
the recurrence's actual domain `n = m + 2` (`m ≥ 0`), clearing every truncating
subtraction into all-positive cubics: leading `34n³−51n²+27n−5 ↦ 34m³+153m²+231m+117`,
top `n³ ↦ (m+2)³`, trailing `(n−1)³ ↦ (m+1)³`.

The constant floors are the leading coefficient times the factorial of the degree:
`204 = 34·3!` for the cubic leading-quotient, `6 = 1·3!` for the two cubes, `2 = 1·2!`
and `22 = 11·2!` for the ζ(2) quadratics.

## The coefficient-degree tower

    e : degree 1 (linear)  →  ζ(2) : degree 2 (quadratic)  →  ζ(3) : degree 3 (cubic).

This is the **Apéry zeta tower** as a strict ∅-axiom arithmetic statement: the minimal
holonomic recurrence coefficient degree of `ζ(k)`'s convergents rises by one with `k`.
The degree is the invariant that controls the Casoratian (discrete Wronskian) of the
order-2 recurrence: `Cₙ = aₙbₙ₋₁ − aₙ₋₁bₙ` satisfies `c₂(n)·Cₙ = −c₀(n)·Cₙ₋₁`, whose
closed forms are `±5/n²` (ζ(2), the `n²` from `c₂=(n+1)²`, `c₀=n²`) and `±6/n³` (ζ(3),
the `n³` from `c₂=n³`, `c₀=(n−1)³`) — the denominators `n²`, `n³` are exactly `aperyBot`
/ `aperyTop` here, of finite-difference depth 2 and 3.  The middle coefficient
(`34n³−51n²+27n−5`, `11n²+11n+3`) cancels out of the Casoratian, so although it is the
same degree it is not what the Wronskian sees.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthAperyCubic

open E213.Meta.Nat.PolyNat (poly_id)
open E213.Lib.Math.Cauchy.DivergenceLadder (diff liftK)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth liftK_diff_comm liftK_congr)
open E213.Tactic.NatHelper (add_sub_cancel_right)

/-! ## §1 — ζ(3), the Apéry leading-quotient coefficient `34n³−51n²+27n−5` at `n = m+2`

`34(m+2)³ − 51(m+2)² + 27(m+2) − 5 = 34m³ + 153m² + 231m + 117` (all positive). -/

/-- The ζ(3) Apéry recurrence's leading-quotient coefficient `34n³−51n²+27n−5`, evaluated
    at `n = m+2` (first valid index `n=2` is `m=0`): the all-positive cubic
    `34m³+153m²+231m+117`.  This is the `aₙ₋₁` coefficient `c₁`; degree 3. -/
def aperyLead (m : Nat) : Nat := 34*m*m*m + 153*m*m + 231*m + 117

/-- Successive forward differences of `aperyLead` (quadratic, linear). -/
private def aL1 (m : Nat) : Nat := 102*m*m + 408*m + 418
private def aL2 (m : Nat) : Nat := 204*m + 510

private theorem RL1 (m : Nat) : aperyLead (m+1) = aperyLead m + aL1 m :=
  poly_id
    (.add (.add (.add (.mul (.mul (.mul (.C 34) (.add .X (.C 1))) (.add .X (.C 1))) (.add .X (.C 1)))
                    (.mul (.mul (.C 153) (.add .X (.C 1))) (.add .X (.C 1))))
               (.mul (.C 231) (.add .X (.C 1)))) (.C 117))
    (.add (.add (.add (.add (.mul (.mul (.mul (.C 34) .X) .X) .X) (.mul (.mul (.C 153) .X) .X))
                    (.mul (.C 231) .X)) (.C 117))
          (.add (.add (.mul (.mul (.C 102) .X) .X) (.mul (.C 408) .X)) (.C 418)))
    rfl m

private theorem RL2 (m : Nat) : aL1 (m+1) = aL1 m + aL2 m :=
  poly_id
    (.add (.add (.mul (.mul (.C 102) (.add .X (.C 1))) (.add .X (.C 1))) (.mul (.C 408) (.add .X (.C 1)))) (.C 418))
    (.add (.add (.add (.mul (.mul (.C 102) .X) .X) (.mul (.C 408) .X)) (.C 418))
          (.add (.mul (.C 204) .X) (.C 510)))
    rfl m

private theorem RL3 (m : Nat) : aL2 (m+1) = aL2 m + 204 :=
  poly_id
    (.add (.mul (.C 204) (.add .X (.C 1))) (.C 510))
    (.add (.add (.mul (.C 204) .X) (.C 510)) (.C 204))
    rfl m

private theorem diff_aperyLead (m : Nat) : diff aperyLead m = aL1 m := by
  show aperyLead (m+1) - aperyLead m = aL1 m
  rw [RL1 m, Nat.add_comm (aperyLead m) (aL1 m)]; exact add_sub_cancel_right (aL1 m) (aperyLead m)

private theorem diff_aL1 (m : Nat) : diff aL1 m = aL2 m := by
  show aL1 (m+1) - aL1 m = aL2 m
  rw [RL2 m, Nat.add_comm (aL1 m) (aL2 m)]; exact add_sub_cancel_right (aL2 m) (aL1 m)

private theorem diff_aL2 (m : Nat) : diff aL2 m = 204 := by
  show aL2 (m+1) - aL2 m = 204
  rw [RL3 m, Nat.add_comm (aL2 m) 204]; exact add_sub_cancel_right 204 (aL2 m)

/-- The 3rd finite difference of `aperyLead` is the constant `204 = 34·3!` (leading
    coefficient times `3!`) — three differences take the cubic to its floor. -/
theorem liftK3_aperyLead (m : Nat) : liftK 3 aperyLead m = 204 := by
  rw [liftK_diff_comm 2 aperyLead, liftK_congr 2 (diff aperyLead) aL1 diff_aperyLead m,
      liftK_diff_comm 1 aL1, liftK_congr 1 (diff aL1) aL2 diff_aL1 m]
  show diff aL2 m = 204
  exact diff_aL2 m

/-- ★★★ **The ζ(3) Apéry leading-quotient coefficient has divergence-depth 3.**
    `polyDepth 3 aperyLead` — the degree-3 polynomial `34n³−51n²+27n−5` (the `aₙ₋₁`
    coefficient `c₁`) reaches its constant floor `204 = 34·3!` after exactly three
    finite differences.  ∅-axiom via the reflection prover. -/
theorem aperyLead_polyDepth : polyDepth 3 aperyLead :=
  fun m => by rw [liftK3_aperyLead m, liftK3_aperyLead 0]

/-! ## §2 — ζ(3), the top coefficient `n³` at `n = m+2`: `(m+2)³`, depth 3

`aperyTop = n³ = c₂` is one of the two factors controlling the Casoratian `±6/n³`. -/

/-- The ζ(3) recurrence's leading coefficient `n³` at `n = m+2`: `(m+2)³` (= `c₂`, the
    Casoratian denominator factor). -/
def aperyTop (m : Nat) : Nat := (m+2)*(m+2)*(m+2)

private def aT1 (m : Nat) : Nat := 3*m*m + 15*m + 19
private def aT2 (m : Nat) : Nat := 6*m + 18

private theorem RT1 (m : Nat) : aperyTop (m+1) = aperyTop m + aT1 m :=
  poly_id
    (.mul (.mul (.add (.add .X (.C 1)) (.C 2)) (.add (.add .X (.C 1)) (.C 2))) (.add (.add .X (.C 1)) (.C 2)))
    (.add (.mul (.mul (.add .X (.C 2)) (.add .X (.C 2))) (.add .X (.C 2)))
          (.add (.add (.mul (.mul (.C 3) .X) .X) (.mul (.C 15) .X)) (.C 19)))
    rfl m

private theorem RT2 (m : Nat) : aT1 (m+1) = aT1 m + aT2 m :=
  poly_id
    (.add (.add (.mul (.mul (.C 3) (.add .X (.C 1))) (.add .X (.C 1))) (.mul (.C 15) (.add .X (.C 1)))) (.C 19))
    (.add (.add (.add (.mul (.mul (.C 3) .X) .X) (.mul (.C 15) .X)) (.C 19))
          (.add (.mul (.C 6) .X) (.C 18)))
    rfl m

private theorem RT3 (m : Nat) : aT2 (m+1) = aT2 m + 6 :=
  poly_id
    (.add (.mul (.C 6) (.add .X (.C 1))) (.C 18))
    (.add (.add (.mul (.C 6) .X) (.C 18)) (.C 6))
    rfl m

private theorem diff_aperyTop (m : Nat) : diff aperyTop m = aT1 m := by
  show aperyTop (m+1) - aperyTop m = aT1 m
  rw [RT1 m, Nat.add_comm (aperyTop m) (aT1 m)]; exact add_sub_cancel_right (aT1 m) (aperyTop m)

private theorem diff_aT1 (m : Nat) : diff aT1 m = aT2 m := by
  show aT1 (m+1) - aT1 m = aT2 m
  rw [RT2 m, Nat.add_comm (aT1 m) (aT2 m)]; exact add_sub_cancel_right (aT2 m) (aT1 m)

private theorem diff_aT2 (m : Nat) : diff aT2 m = 6 := by
  show aT2 (m+1) - aT2 m = 6
  rw [RT3 m, Nat.add_comm (aT2 m) 6]; exact add_sub_cancel_right 6 (aT2 m)

theorem liftK3_aperyTop (m : Nat) : liftK 3 aperyTop m = 6 := by
  rw [liftK_diff_comm 2 aperyTop, liftK_congr 2 (diff aperyTop) aT1 diff_aperyTop m,
      liftK_diff_comm 1 aT1, liftK_congr 1 (diff aT1) aT2 diff_aT1 m]
  show diff aT2 m = 6
  exact diff_aT2 m

/-- ★★★ **The ζ(3) Casoratian-controlling coefficient `n³` has divergence-depth 3.**
    `polyDepth 3 aperyTop` — the pure cube `(m+2)³ = c₂` floors at `6 = 1·3!` after three
    differences.  This is the polynomial whose degree is the principled ζ(3) divergence
    depth (the Casoratian `Cₙ = aₙbₙ₋₁−aₙ₋₁bₙ = ±6/n³` has denominator `n³`). -/
theorem aperyTop_polyDepth : polyDepth 3 aperyTop :=
  fun m => by rw [liftK3_aperyTop m, liftK3_aperyTop 0]

/-! ## §3 — ζ(3), the trailing coefficient `(n−1)³` at `n = m+2`: `(m+1)³`, depth 3

`aperyBot = (n−1)³ = c₀`, the other Casoratian factor. -/

/-- The ζ(3) recurrence's trailing coefficient `(n−1)³` at `n = m+2`: `(m+1)³` (= `c₀`). -/
def aperyBot (m : Nat) : Nat := (m+1)*(m+1)*(m+1)

private def aB1 (m : Nat) : Nat := 3*m*m + 9*m + 7
private def aB2 (m : Nat) : Nat := 6*m + 12

private theorem RB1 (m : Nat) : aperyBot (m+1) = aperyBot m + aB1 m :=
  poly_id
    (.mul (.mul (.add (.add .X (.C 1)) (.C 1)) (.add (.add .X (.C 1)) (.C 1))) (.add (.add .X (.C 1)) (.C 1)))
    (.add (.mul (.mul (.add .X (.C 1)) (.add .X (.C 1))) (.add .X (.C 1)))
          (.add (.add (.mul (.mul (.C 3) .X) .X) (.mul (.C 9) .X)) (.C 7)))
    rfl m

private theorem RB2 (m : Nat) : aB1 (m+1) = aB1 m + aB2 m :=
  poly_id
    (.add (.add (.mul (.mul (.C 3) (.add .X (.C 1))) (.add .X (.C 1))) (.mul (.C 9) (.add .X (.C 1)))) (.C 7))
    (.add (.add (.add (.mul (.mul (.C 3) .X) .X) (.mul (.C 9) .X)) (.C 7))
          (.add (.mul (.C 6) .X) (.C 12)))
    rfl m

private theorem RB3 (m : Nat) : aB2 (m+1) = aB2 m + 6 :=
  poly_id
    (.add (.mul (.C 6) (.add .X (.C 1))) (.C 12))
    (.add (.add (.mul (.C 6) .X) (.C 12)) (.C 6))
    rfl m

private theorem diff_aperyBot (m : Nat) : diff aperyBot m = aB1 m := by
  show aperyBot (m+1) - aperyBot m = aB1 m
  rw [RB1 m, Nat.add_comm (aperyBot m) (aB1 m)]; exact add_sub_cancel_right (aB1 m) (aperyBot m)

private theorem diff_aB1 (m : Nat) : diff aB1 m = aB2 m := by
  show aB1 (m+1) - aB1 m = aB2 m
  rw [RB2 m, Nat.add_comm (aB1 m) (aB2 m)]; exact add_sub_cancel_right (aB2 m) (aB1 m)

private theorem diff_aB2 (m : Nat) : diff aB2 m = 6 := by
  show aB2 (m+1) - aB2 m = 6
  rw [RB3 m, Nat.add_comm (aB2 m) 6]; exact add_sub_cancel_right 6 (aB2 m)

theorem liftK3_aperyBot (m : Nat) : liftK 3 aperyBot m = 6 := by
  rw [liftK_diff_comm 2 aperyBot, liftK_congr 2 (diff aperyBot) aB1 diff_aperyBot m,
      liftK_diff_comm 1 aB1, liftK_congr 1 (diff aB1) aB2 diff_aB1 m]
  show diff aB2 m = 6
  exact diff_aB2 m

/-- ★★ **The ζ(3) trailing coefficient `(n−1)³` has divergence-depth 3.**  `polyDepth 3
    aperyBot` — the cube `(m+1)³ = c₀` floors at `6 = 1·3!` after three differences. -/
theorem aperyBot_polyDepth : polyDepth 3 aperyBot :=
  fun m => by rw [liftK3_aperyBot m, liftK3_aperyBot 0]

/-! ## §4 — ζ(2), the order-2 quadratic rung `(n+1)²·uₙ₊₁ = (11n²+11n+3)·uₙ + n²·uₙ₋₁`

All three coefficients are degree-2 (already positive for `n ≥ 0`, no reindex needed). -/

/-- The ζ(2) recurrence's leading coefficient `(n+1)²` (= `c₂`, the Casoratian
    denominator factor). -/
def zeta2Top (n : Nat) : Nat := (n+1)*(n+1)
/-- The ζ(2) recurrence's middle coefficient `11n²+11n+3` (= `c₁`). -/
def zeta2Mid (n : Nat) : Nat := 11*n*n + 11*n + 3
/-- The ζ(2) recurrence's trailing coefficient `n²` (= `c₀`). -/
def zeta2Bot (n : Nat) : Nat := n*n

private def z2T1 (n : Nat) : Nat := 2*n + 3
private def z2M1 (n : Nat) : Nat := 22*n + 22
private def z2B1 (n : Nat) : Nat := 2*n + 1

private theorem RZT1 (n : Nat) : zeta2Top (n+1) = zeta2Top n + z2T1 n :=
  poly_id
    (.mul (.add (.add .X (.C 1)) (.C 1)) (.add (.add .X (.C 1)) (.C 1)))
    (.add (.mul (.add .X (.C 1)) (.add .X (.C 1))) (.add (.mul (.C 2) .X) (.C 3)))
    rfl n

private theorem RZT2 (n : Nat) : z2T1 (n+1) = z2T1 n + 2 :=
  poly_id (.add (.mul (.C 2) (.add .X (.C 1))) (.C 3)) (.add (.add (.mul (.C 2) .X) (.C 3)) (.C 2)) rfl n

private theorem RZM1 (n : Nat) : zeta2Mid (n+1) = zeta2Mid n + z2M1 n :=
  poly_id
    (.add (.add (.mul (.mul (.C 11) (.add .X (.C 1))) (.add .X (.C 1))) (.mul (.C 11) (.add .X (.C 1)))) (.C 3))
    (.add (.add (.add (.mul (.mul (.C 11) .X) .X) (.mul (.C 11) .X)) (.C 3))
          (.add (.mul (.C 22) .X) (.C 22)))
    rfl n

private theorem RZM2 (n : Nat) : z2M1 (n+1) = z2M1 n + 22 :=
  poly_id (.add (.mul (.C 22) (.add .X (.C 1))) (.C 22)) (.add (.add (.mul (.C 22) .X) (.C 22)) (.C 22)) rfl n

private theorem RZB1 (n : Nat) : zeta2Bot (n+1) = zeta2Bot n + z2B1 n :=
  poly_id
    (.mul (.add .X (.C 1)) (.add .X (.C 1)))
    (.add (.mul .X .X) (.add (.mul (.C 2) .X) (.C 1)))
    rfl n

private theorem RZB2 (n : Nat) : z2B1 (n+1) = z2B1 n + 2 :=
  poly_id (.add (.mul (.C 2) (.add .X (.C 1))) (.C 1)) (.add (.add (.mul (.C 2) .X) (.C 1)) (.C 2)) rfl n

private theorem diff_zeta2Top (n : Nat) : diff zeta2Top n = z2T1 n := by
  show zeta2Top (n+1) - zeta2Top n = z2T1 n
  rw [RZT1 n, Nat.add_comm (zeta2Top n) (z2T1 n)]; exact add_sub_cancel_right (z2T1 n) (zeta2Top n)

private theorem diff_z2T1 (n : Nat) : diff z2T1 n = 2 := by
  show z2T1 (n+1) - z2T1 n = 2
  rw [RZT2 n, Nat.add_comm (z2T1 n) 2]; exact add_sub_cancel_right 2 (z2T1 n)

private theorem diff_zeta2Mid (n : Nat) : diff zeta2Mid n = z2M1 n := by
  show zeta2Mid (n+1) - zeta2Mid n = z2M1 n
  rw [RZM1 n, Nat.add_comm (zeta2Mid n) (z2M1 n)]; exact add_sub_cancel_right (z2M1 n) (zeta2Mid n)

private theorem diff_z2M1 (n : Nat) : diff z2M1 n = 22 := by
  show z2M1 (n+1) - z2M1 n = 22
  rw [RZM2 n, Nat.add_comm (z2M1 n) 22]; exact add_sub_cancel_right 22 (z2M1 n)

private theorem diff_zeta2Bot (n : Nat) : diff zeta2Bot n = z2B1 n := by
  show zeta2Bot (n+1) - zeta2Bot n = z2B1 n
  rw [RZB1 n, Nat.add_comm (zeta2Bot n) (z2B1 n)]; exact add_sub_cancel_right (z2B1 n) (zeta2Bot n)

private theorem diff_z2B1 (n : Nat) : diff z2B1 n = 2 := by
  show z2B1 (n+1) - z2B1 n = 2
  rw [RZB2 n, Nat.add_comm (z2B1 n) 2]; exact add_sub_cancel_right 2 (z2B1 n)

theorem liftK2_zeta2Top (n : Nat) : liftK 2 zeta2Top n = 2 := by
  rw [liftK_diff_comm 1 zeta2Top, liftK_congr 1 (diff zeta2Top) z2T1 diff_zeta2Top n]
  show diff z2T1 n = 2
  exact diff_z2T1 n

theorem liftK2_zeta2Mid (n : Nat) : liftK 2 zeta2Mid n = 22 := by
  rw [liftK_diff_comm 1 zeta2Mid, liftK_congr 1 (diff zeta2Mid) z2M1 diff_zeta2Mid n]
  show diff z2M1 n = 22
  exact diff_z2M1 n

theorem liftK2_zeta2Bot (n : Nat) : liftK 2 zeta2Bot n = 2 := by
  rw [liftK_diff_comm 1 zeta2Bot, liftK_congr 1 (diff zeta2Bot) z2B1 diff_zeta2Bot n]
  show diff z2B1 n = 2
  exact diff_z2B1 n

/-- ★★ **The ζ(2) recurrence coefficients have divergence-depth 2.**  `(n+1)²` and `n²`
    floor at `2 = 1·2!`, `11n²+11n+3` floors at `22 = 11·2!`, each after two
    differences — degree-2 discrete polynomials.  `zeta2Top = (n+1)²` and `zeta2Bot =
    n²` control the ζ(2) Casoratian `±5/n²` (denominator `n²`). -/
theorem zeta2_quadratic_rung :
    polyDepth 2 zeta2Top ∧ polyDepth 2 zeta2Mid ∧ polyDepth 2 zeta2Bot :=
  ⟨fun n => by rw [liftK2_zeta2Top n, liftK2_zeta2Top 0],
   fun n => by rw [liftK2_zeta2Mid n, liftK2_zeta2Mid 0],
   fun n => by rw [liftK2_zeta2Bot n, liftK2_zeta2Bot 0]⟩

/-! ## §5 — the Apéry zeta tower: coefficient degree 1 → 2 → 3 -/

/-- ★★★ **ζ(3) is P-recursive of order 2 with degree-3 (cubic) coefficients, each of
    divergence-depth 3.**  The three coefficients of the Apéry recurrence — leading `n³`
    (`aperyTop` = `c₂`), leading-quotient `34n³−51n²+27n−5` (`aperyLead` = `c₁`),
    trailing `(n−1)³` (`aperyBot` = `c₀`) — are all degree-3 discrete polynomials
    (`polyDepth 3`). -/
theorem apery_cubic_rung :
    polyDepth 3 aperyTop ∧ polyDepth 3 aperyLead ∧ polyDepth 3 aperyBot :=
  ⟨aperyTop_polyDepth, aperyLead_polyDepth, aperyBot_polyDepth⟩

/-- ★★★ **The Apéry zeta tower, ∅-axiom.**  The Casoratian-controlling coefficients of
    the minimal holonomic recurrences climb by exactly one degree from ζ(2) to ζ(3):
    `zeta2Top = (n+1)²` has depth **2** (Casoratian `±5/n²`), `aperyTop = n³` has depth
    **3** (Casoratian `±6/n³`).  Together with e's degree-1 ratio (`DivergenceDepth`),
    the coefficient-degree tower is `e : 1 → ζ(2) : 2 → ζ(3) : 3` — the minimal
    holonomic recurrence coefficient degree of `ζ(k)`'s convergents rises by one with
    `k`, the structural invariant behind the Apéry irrationality proofs. -/
theorem apery_zeta_tower :
    polyDepth 2 zeta2Top ∧ polyDepth 3 aperyTop :=
  ⟨zeta2_quadratic_rung.1, aperyTop_polyDepth⟩

end E213.Lib.Math.Cauchy.DepthAperyCubic
