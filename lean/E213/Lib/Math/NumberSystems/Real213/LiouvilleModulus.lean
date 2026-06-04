import E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake
import E213.Lib.Math.Analysis.Cauchy.DepthLiouvilleCoord
import E213.Meta.Nat.PureNat

/-!
# LiouvilleModulus — on the cross-determinant axis the Liouville constant is as tame as e

`DepthLiouvilleCoord` places the Liouville exponent `k!` *outside* every finite value
coordinate `(h,d)` on the difference axis (`diff fact = k·k!`, super-polynomial): on
the value axis a Liouville number looks maximally pathological.  The tower-native
question is the opposite one — present the Liouville constant `Σ_j c^{-j!}` as a
num/den convergent sequence and ask whether its **cross-determinant** stays below its
**denominator** (the completability comparison `CrossDetSmall`).

It does, decisively.  With the convergents defined by the recurrence (growth factor
`g_k = c^{k·k!}`)

> `liouDen c 0 = c`,            `liouDen c (k+1) = g_k · liouDen c k`   (`= c^{k!}`),
> `liouNum c 0 = 1`,            `liouNum c (k+1) = g_k · liouNum c k + 1`,

the **cross-determinant collapses to the denominator** — `liou_cross_det`:
`liouNum_{k+1}·liouDen_k = liouNum_k·liouDen_{k+1} + liouDen_k`, i.e. `W_k = liouDen_k`
— *exactly* the e pattern (`euler_cross_det`).  The factorial denominator then grows
so fast (`g_k = c^{k·k!} ≥ k+1`) that the smallness condition `CrossDetSmall` holds, so
`CrossDetOvertake.crossdet_small_total_modulus` gives a **free total ∅-axiom modulus**.

  * ★★★ `liouville_total_modulus` — the Liouville constant carries a total constructed
    modulus `N(m,k) = k+2`, no irrationality measure, no LEM.
  * ★★★ `liouville_W_eq_denom_coordinate` — the adjudication: the cross-determinant
    equals the denominator (`W_k = liouDen_k`), the denominator's exponent **is** the
    factorial (`liouDen_k = c^{k!}`), and the factorial sits at recursion-coordinate
    (ratio-depth 1) one tier down (`DepthLiouvilleCoord.ratioLift_fact`).  So `W` and
    `d` share the factorial-tier coordinate and `d`'s growth dominates `W` — the
    recursion-coordinate of `W` sits at/below that of `d`, hence Liouville completes.

The value-axis depth-∞ is irrelevant to completability; on the cross-determinant /
denominator axis a Liouville number is no worse than e.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.LiouvilleModulus

open E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake
  (CrossDetSmall crossdet_small_total_modulus two_pow_ge_succ)
open E213.Lib.Math.NumberSystems.Real213.RateModulus (rcut)
open E213.Lib.Math.Analysis.Cauchy.DepthLiouvilleCoord (fact fact_pos fact_succ ratioLift_fact)
open E213.Lib.Math.Analysis.Cauchy.DepthTower (ratioLift)
open E213.Tactic.NatHelper (mul_assoc add_mul add_sub_of_le)
open E213.Meta.Nat.PureNat (pow_add)

/-! ## §1 — the Liouville-constant convergents (recurrence form) -/

/-- The denominator growth factor `g_k = liouDen_{k+1}/liouDen_k = c^{k·k!}`. -/
def g (c k : Nat) : Nat := c ^ (k * fact k)

/-- Convergent denominators `liouDen c k = c^{k!}` (in recurrence form). -/
def liouDen (c : Nat) : Nat → Nat
  | 0   => c
  | k+1 => g c k * liouDen c k

/-- Convergent numerators of `Σ_{j} c^{-j!}` (in recurrence form). -/
def liouNum (c : Nat) : Nat → Nat
  | 0   => 1
  | k+1 => g c k * liouNum c k + 1

/-- `g c k` is positive when `c ≥ 1`. -/
theorem g_pos (c k : Nat) (hc : 1 ≤ c) : 0 < g c k := Nat.pos_pow_of_pos _ hc

/-! ## §2 — the cross-determinant equals the denominator (the e pattern) -/

/-- ★★ **`W_k = liouDen_k`.**  The Liouville-constant convergents' cross-determinant
    is exactly the denominator: `liouNum_{k+1}·liouDen_k = liouNum_k·liouDen_{k+1} +
    liouDen_k`.  Identical in form to e's `euler_cross_det`. -/
theorem liou_cross_det (c k : Nat) :
    liouNum c (k+1) * liouDen c k = liouNum c k * liouDen c (k+1) + liouDen c k := by
  show (g c k * liouNum c k + 1) * liouDen c k
     = liouNum c k * (g c k * liouDen c k) + liouDen c k
  rw [add_mul, Nat.one_mul]
  congr 1
  rw [Nat.mul_comm (g c k) (liouNum c k), mul_assoc]

/-! ## §3 — the generator hypotheses -/

/-- Positive denominators. -/
theorem liou_hd (c : Nat) (hc : 1 ≤ c) : ∀ k, 1 ≤ liouDen c k
  | 0   => hc
  | k+1 => Nat.mul_pos (g_pos c k hc) (liou_hd c hc k)

/-- Convergents strictly increasing — the difference is exactly `liouDen c k`. -/
theorem liou_hmonoS (c : Nat) (hc : 1 ≤ c) :
    ∀ i, liouNum c i * liouDen c (i+1) < liouNum c (i+1) * liouDen c i := by
  intro i
  show liouNum c i * (g c i * liouDen c i) < (g c i * liouNum c i + 1) * liouDen c i
  have hL : liouNum c i * (g c i * liouDen c i) = g c i * liouNum c i * liouDen c i := by
    rw [← mul_assoc, Nat.mul_comm (liouNum c i) (g c i)]
  have hR : (g c i * liouNum c i + 1) * liouDen c i
      = g c i * liouNum c i * liouDen c i + liouDen c i := by
    rw [add_mul, Nat.one_mul]
  rw [hL, hR]; exact Nat.lt_add_of_pos_right (liou_hd c hc i)

/-- Convergents increasing across any gap. -/
theorem liou_hmono (c : Nat) (hc : 1 ≤ c) :
    ∀ N i, N ≤ i → liouNum c N * liouDen c i ≤ liouNum c i * liouDen c N := by
  intro N
  have aux : ∀ t, liouNum c N * liouDen c (N+t) ≤ liouNum c (N+t) * liouDen c N := by
    intro t
    induction t with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      show liouNum c N * (g c (N+t) * liouDen c (N+t))
         ≤ (g c (N+t) * liouNum c (N+t) + 1) * liouDen c N
      have h1 : liouNum c N * (g c (N+t) * liouDen c (N+t))
          = g c (N+t) * (liouNum c N * liouDen c (N+t)) := by
        rw [← mul_assoc, Nat.mul_comm (liouNum c N) (g c (N+t)), mul_assoc]
      have h3 : g c (N+t) * (liouNum c (N+t) * liouDen c N)
          ≤ (g c (N+t) * liouNum c (N+t) + 1) * liouDen c N := by
        have hLr : g c (N+t) * (liouNum c (N+t) * liouDen c N)
            = g c (N+t) * liouNum c (N+t) * liouDen c N := (mul_assoc _ _ _).symm
        have hRr : (g c (N+t) * liouNum c (N+t) + 1) * liouDen c N
            = g c (N+t) * liouNum c (N+t) * liouDen c N + liouDen c N := by
          rw [add_mul, Nat.one_mul]
        rw [hLr, hRr]; exact Nat.le_add_right _ _
      rw [h1]
      exact Nat.le_trans (Nat.mul_le_mul_left (g c (N+t)) ih) h3
  intro i hi; rw [← add_sub_of_le hi]; exact aux (i - N)

/-! ## §4 — the cross-determinant is small (factorial growth dominates) -/

/-- `i + 1 ≤ g c i` for `c ≥ 2`: the growth factor `c^{i·i!}` already exceeds the
    linear axis (`i+1 ≤ 2^i ≤ 2^{i·i!} ≤ c^{i·i!}`). -/
theorem succ_le_g (c i : Nat) (hc : 2 ≤ c) : i + 1 ≤ g c i := by
  have hi_le : i ≤ i * fact i := Nat.le_mul_of_pos_right i (fact_pos i)
  show i + 1 ≤ c ^ (i * fact i)
  exact Nat.le_trans (two_pow_ge_succ i)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) hi_le)
      (Nat.pow_le_pow_left hc (i * fact i)))

/-- ★★ **The Liouville cross-determinant is small.**  With `W = d = liouDen`, the
    smallness condition `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}` reduces to
    `i(i+1)+i ≤ (i+1)·g_i`, which holds because `g_i ≥ i+1` (factorial growth). -/
theorem liou_crossDetSmall (c : Nat) (hc : 2 ≤ c) :
    CrossDetSmall (liouDen c) (liouDen c) := by
  intro i _
  have hbound : i * (i+1) + i ≤ (i+1) * g c i := by
    calc i * (i+1) + i
        ≤ i * (i+1) + (i+1) := Nat.add_le_add_left (Nat.le_succ i) _
      _ = (i+1) * (i+1) := by rw [Nat.succ_mul]
      _ ≤ (i+1) * g c i := Nat.mul_le_mul_left (i+1) (succ_le_g c i hc)
  show i * (i+1) * liouDen c i + i * liouDen c i ≤ (i+1) * (g c i * liouDen c i)
  calc i * (i+1) * liouDen c i + i * liouDen c i
      = (i * (i+1) + i) * liouDen c i := by rw [add_mul]
    _ ≤ ((i+1) * g c i) * liouDen c i := Nat.mul_le_mul_right _ hbound
    _ = (i+1) * (g c i * liouDen c i) := by rw [mul_assoc]

/-! ## §5 — the free modulus, and the coordinate adjudication -/

/-- ★★★ **The Liouville constant carries a free total ∅-axiom modulus.**  Its
    convergents satisfy the rate certificate (`CrossDetSmall`, since `W = d` and the
    factorial denominator dominates), so `crossdet_small_total_modulus` produces the
    constructed modulus `N(m,k) = k+2` — no irrationality measure, no LEM.  On the
    cross-determinant / denominator axis a Liouville number completes exactly like e. -/
theorem liouville_total_modulus (c : Nat) (hc : 2 ≤ c) (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (liouNum c) (liouDen c) i m k = rcut (liouNum c) (liouDen c) j m k :=
  have hc1 : 1 ≤ c := Nat.le_trans (by decide) hc
  crossdet_small_total_modulus (liouDen c) (liou_hd c hc1) (liou_cross_det c)
    (liou_crossDetSmall c hc) (liou_hmono c hc1) (liou_hmonoS c hc1) m k hk

/-- The denominator's closed form: `liouDen c k = c^{k!}` — its exponent is the
    factorial. -/
theorem liouDen_closed (c : Nat) : ∀ k, liouDen c k = c ^ (fact k)
  | 0   => by show c = c ^ (fact 0); rw [show fact 0 = 1 from rfl, Nat.pow_one]
  | k+1 => by
    show g c k * liouDen c k = c ^ (fact (k+1))
    rw [liouDen_closed c k]
    show c ^ (k * fact k) * c ^ (fact k) = c ^ (fact (k+1))
    rw [← pow_add]
    congr 1
    rw [← Nat.succ_mul]
    exact (fact_succ k).symm

/-- ★★★ **The T2 adjudication: `W` and `d` share the factorial coordinate, `d`
    dominates.**  The cross-determinant equals the denominator (`liou_cross_det`,
    `W_k = liouDen_k`); the denominator's exponent is the factorial (`liouDen_closed`,
    `liouDen_k = c^{k!}`); and the factorial sits at recursion-coordinate ratio-depth 1
    one tier down (`ratioLift_fact`, `k! ↦ k+1`).  These three identities are what the
    bundle returns; from them the smallness comparison `W ≤ d` follows and the free
    modulus is delivered separately by `liouville_total_modulus` — the tower adjudicates
    completability by a coordinate comparison, with no irrationality measure. -/
theorem liouville_W_eq_denom_coordinate (c : Nat) :
    (∀ k, liouNum c (k+1) * liouDen c k
            = liouNum c k * liouDen c (k+1) + liouDen c k)
    ∧ (∀ k, liouDen c k = c ^ (fact k))
    ∧ (∀ n, ratioLift fact n = n + 1) :=
  ⟨liou_cross_det c, liouDen_closed c, ratioLift_fact⟩

end E213.Lib.Math.NumberSystems.Real213.LiouvilleModulus
