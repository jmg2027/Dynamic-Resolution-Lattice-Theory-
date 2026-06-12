import E213.Lib.Math.NumberSystems.Real213.RateModulus
import E213.Meta.Nat.PolyNatMTactic

/-!
# BracketModulus — bracket exclusion depth ⟹ total modulus (the conversion-law engine)

The modulus-degree ladder's conversion law — a total cut modulus is
`rate⁻¹ ∘ distance` — in engine form, for **two-sided bracket presentations**:
a strictly increasing lower fold `a/d` (the pointing) with a non-increasing
upper companion `A/D` sandwiching it per layer (`a_n/d_n < A_n/D_n`).  The one
hypothesis an instance must supply is the **exclusion depth** `B`: any probe
`m/k` still strictly `Inside` the layer-`n` bracket forces `n ≤ B k`.  Then the
side of every probe is decided past `B k + 1` and the total ∅-axiom modulus is
`N(m,k) = B k + 2` (`bracket_total_modulus`):

  * probe at-or-below the lower endpoint at the exit layer ⟹ the strictly
    increasing fold passes it ⟹ cut `false` forward (`below_fwd`);
  * probe at-or-above the upper companion ⟹ the companion (and with it every
    later lower endpoint) stays below the probe ⟹ cut `true` forward
    (`above_fwd`).

The exclusion depth is where an **effective irrationality measure** enters: a
distance certificate `|x − m/k| ≥ 1/(C·k^s)` against a width rate `≲ 1/n`
yields `B k = C·k^s` — the conditional measure-modulus schema (ladder rung 2).
Instance: `ExpLog/PiMeasureModulus` (Wallis-π/2, conditional degree `s`).

No measure is assumed here; the engine itself is unconditional.  All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.BracketModulus

open E213.Lib.Math.NumberSystems.Real213.RateModulus (rcut)
open E213.Tactic.NatHelper (le_of_mul_le_mul_right add_sub_of_le)

variable {a d A D : Nat → Nat}

/-- The probe `m/k` lies **strictly inside** the layer-`n` bracket:
    `a_n/d_n < m/k < A_n/D_n`, cross-multiplied to `Nat`. -/
def Inside (a d A D : Nat → Nat) (m k n : Nat) : Prop :=
  a n * k < d n * m ∧ m * D n < A n * k

/-! ## §1 — the two stable exits -/

private theorem below_step (hWmono : ∀ n, a n * d (n+1) < a (n+1) * d n)
    (m k j : Nat) (hk : 1 ≤ k) (hbase : d j * m ≤ a j * k) :
    d (j+1) * m < a (j+1) * k := by
  have c1 : (d j * m) * d (j+1) ≤ (a j * k) * d (j+1) :=
    Nat.mul_le_mul_right _ hbase
  have c2 : (a j * k) * d (j+1) = (a j * d (j+1)) * k := by ring_nat
  have c3 : (a j * d (j+1)) * k < (a (j+1) * d j) * k :=
    Nat.mul_lt_mul_of_pos_right (hWmono j) hk
  have c4 : (a (j+1) * d j) * k = (a (j+1) * k) * d j := by ring_nat
  have hchain : (d (j+1) * m) * d j < (a (j+1) * k) * d j := by
    rw [show (d (j+1) * m) * d j = (d j * m) * d (j+1) from by ring_nat]
    exact Nat.lt_of_le_of_lt (Nat.le_trans c1 (Nat.le_of_eq c2)) (c4 ▸ c3)
  rcases Nat.lt_or_ge (d (j+1) * m) (a (j+1) * k) with h | h
  · exact h
  · exact absurd (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h) hchain)
      (Nat.lt_irrefl _)

/-- Probe at-or-below the lower endpoint at layer `n₀` ⟹ the strictly
    increasing fold passes it ⟹ cut `false` for every `j ≥ n₀+1`. -/
private theorem below_fwd (hWmono : ∀ n, a n * d (n+1) < a (n+1) * d n)
    (m k n₀ : Nat) (hk : 1 ≤ k) (hbase : d n₀ * m ≤ a n₀ * k) :
    ∀ j, n₀+1 ≤ j → rcut a d j m k = false := by
  have aux : ∀ t, d (n₀+1+t) * m < a (n₀+1+t) * k := by
    intro t
    induction t with
    | zero => exact below_step hWmono m k n₀ hk hbase
    | succ t ih => exact below_step hWmono m k (n₀+1+t) hk (Nat.le_of_lt ih)
  intro j hj
  apply decide_eq_false
  intro hle
  have h := aux (j - (n₀+1))
  rw [add_sub_of_le hj] at h
  exact absurd hle (Nat.not_le.mpr h)

private theorem above_step (hUmono : ∀ n, A (n+1) * D n ≤ A n * D (n+1))
    (hD : ∀ n, 1 ≤ D n) (m k j : Nat) (hbase : A j * k ≤ m * D j) :
    A (j+1) * k ≤ m * D (j+1) := by
  have c2 : (A (j+1) * D j) * k ≤ (A j * D (j+1)) * k :=
    Nat.mul_le_mul_right _ (hUmono j)
  have c3 : (A j * D (j+1)) * k = (A j * k) * D (j+1) := by ring_nat
  have c4 : (A j * k) * D (j+1) ≤ (m * D j) * D (j+1) :=
    Nat.mul_le_mul_right _ hbase
  have c5 : (m * D j) * D (j+1) = (m * D (j+1)) * D j := by ring_nat
  have hchain : (A (j+1) * k) * D j ≤ (m * D (j+1)) * D j := by
    rw [show (A (j+1) * k) * D j = (A (j+1) * D j) * k from by ring_nat]
    exact Nat.le_trans c2 (Nat.le_trans (Nat.le_of_eq c3)
      (Nat.le_trans c4 (Nat.le_of_eq c5)))
  exact le_of_mul_le_mul_right (hD j) hchain

/-- Below the upper companion ⟹ below the probe: the per-layer sandwich turns
    `A_j/D_j ≤ m/k` into a `true` cut at layer `j`. -/
private theorem cut_true_of_above (hD : ∀ n, 1 ≤ D n)
    (hsand : ∀ n, a n * D n < A n * d n)
    (m k j : Nat) (habove : A j * k ≤ m * D j) :
    rcut a d j m k = true := by
  apply decide_eq_true
  have c2 : (a j * D j) * k ≤ (A j * d j) * k :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt (hsand j))
  have c3 : (A j * d j) * k = (A j * k) * d j := by ring_nat
  have c4 : (A j * k) * d j ≤ (m * D j) * d j := Nat.mul_le_mul_right _ habove
  have c5 : (m * D j) * d j = (d j * m) * D j := by ring_nat
  have hchain : (a j * k) * D j ≤ (d j * m) * D j := by
    rw [show (a j * k) * D j = (a j * D j) * k from by ring_nat]
    exact Nat.le_trans c2 (Nat.le_trans (Nat.le_of_eq c3)
      (Nat.le_trans c4 (Nat.le_of_eq c5)))
  exact le_of_mul_le_mul_right (hD j) hchain

/-- Probe at-or-above the upper companion at layer `n₀` ⟹ cut `true` for every
    `j ≥ n₀` (the companion is non-increasing, the sandwich finishes). -/
private theorem above_fwd (hUmono : ∀ n, A (n+1) * D n ≤ A n * D (n+1))
    (hD : ∀ n, 1 ≤ D n) (hsand : ∀ n, a n * D n < A n * d n)
    (m k n₀ : Nat) (hbase : A n₀ * k ≤ m * D n₀) :
    ∀ j, n₀ ≤ j → rcut a d j m k = true := by
  have aux : ∀ t, A (n₀+t) * k ≤ m * D (n₀+t) := by
    intro t
    induction t with
    | zero => exact hbase
    | succ t ih => exact above_step hUmono hD m k (n₀+t) ih
  intro j hj
  have h := aux (j - n₀)
  rw [add_sub_of_le hj] at h
  exact cut_true_of_above hD hsand m k j h

/-! ## §2 — the engine -/

/-- ★★★ **Bracket exit ⟹ cut constant.**  If the probe is *not* strictly inside
    the layer-`n₀` bracket, the cut is constant past `n₀+1`: the exit is one of
    the two stable sides (`below_fwd` / `above_fwd`).  No rate certificate, no
    measure — the bracket pair's monotonicity alone. -/
theorem bracket_cut_const (hD : ∀ n, 1 ≤ D n)
    (hWmono : ∀ n, a n * d (n+1) < a (n+1) * d n)
    (hUmono : ∀ n, A (n+1) * D n ≤ A n * D (n+1))
    (hsand : ∀ n, a n * D n < A n * d n)
    (m k : Nat) (hk : 1 ≤ k)
    (n₀ : Nat) (hout : ¬ Inside a d A D m k n₀)
    (i j : Nat) (hi : n₀+1 ≤ i) (hj : n₀+1 ≤ j) :
    rcut a d i m k = rcut a d j m k := by
  rcases Nat.lt_or_ge (a n₀ * k) (d n₀ * m) with hin1 | hlow
  · have habove : A n₀ * k ≤ m * D n₀ := by
      rcases Nat.lt_or_ge (m * D n₀) (A n₀ * k) with hin2 | h
      · exact absurd ⟨hin1, hin2⟩ hout
      · exact h
    have hi' : n₀ ≤ i := Nat.le_trans (Nat.le_succ n₀) hi
    have hj' : n₀ ≤ j := Nat.le_trans (Nat.le_succ n₀) hj
    rw [above_fwd hUmono hD hsand m k n₀ habove i hi',
        above_fwd hUmono hD hsand m k n₀ habove j hj']
  · rw [below_fwd hWmono m k n₀ hk hlow i hi,
        below_fwd hWmono m k n₀ hk hlow j hj]

/-- ★★★ **Exclusion depth ⟹ total modulus.**  If every probe still inside the
    layer-`n` bracket forces `n ≤ B k`, the cut has the total ∅-axiom modulus
    `N(m,k) = B k + 2` — the conversion law `N = rate⁻¹ ∘ distance` with the
    composite packaged as the depth function `B`. -/
theorem bracket_total_modulus (hD : ∀ n, 1 ≤ D n)
    (hWmono : ∀ n, a n * d (n+1) < a (n+1) * d n)
    (hUmono : ∀ n, A (n+1) * D n ≤ A n * D (n+1))
    (hsand : ∀ n, a n * D n < A n * d n)
    (B : Nat → Nat)
    (hexcl : ∀ m k n, 1 ≤ k → Inside a d A D m k n → n ≤ B k)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  ⟨B k + 2, fun i j hi hj =>
    bracket_cut_const hD hWmono hUmono hsand m k hk (B k + 1)
      (fun hin => absurd (hexcl m k (B k + 1) hk hin) (Nat.not_succ_le_self (B k)))
      i j hi hj⟩

/-! ## §3 — the bracket engine IS a separation schedule (weld/exp unification) -/

/-- ★★★★ **Exclusion depth ⟹ separation schedule.**  The two-sided exclusion-depth
    hypotheses yield exactly the *one-sided* separation property that drives
    `AbCutSeq.sep_cauchy` (the `coth`/`exp` completion engine): any `false` reading
    of the lower fold anywhere already shows at the single layer `B k + 2`.  Hence
    the modulus-degree ladder's rung-2 bracket schema and the weld's separation
    schedule are **one device** — the bracket's exclusion depth `B` *is* the
    separation schedule `I k = B k + 2`, the lower fold supplying it two-sided
    (shrinking bracket) where `exp(p/q)` supplies it one-sided (linear-pq growth).

    Two regimes meet: `false` at a layer `≤ B k + 1` propagates **forward** to
    `B k + 2` (`below_fwd`); `false` at a layer `≥ B k + 2` reflects **back** to
    `B k + 2` by post-exit constancy (`bracket_cut_const`).  Mirrors the shape of
    `AbCutSeq.sep_cauchy`'s `hsep` for `rcut a d`. -/
theorem bracket_is_sep_schedule (hD : ∀ n, 1 ≤ D n)
    (hWmono : ∀ n, a n * d (n+1) < a (n+1) * d n)
    (hUmono : ∀ n, A (n+1) * D n ≤ A n * D (n+1))
    (hsand : ∀ n, a n * D n < A n * d n)
    (B : Nat → Nat)
    (hexcl : ∀ m k n, 1 ≤ k → Inside a d A D m k n → n ≤ B k)
    (m k : Nat) (hk : 1 ≤ k) (i : Nat) (hf : rcut a d i m k = false) :
    rcut a d (B k + 2) m k = false := by
  -- a `false` reading means the strictly-increasing lower endpoint has passed `m/k`
  have hbase : d i * m ≤ a i * k := Nat.le_of_lt (Nat.not_le.mp (of_decide_eq_false hf))
  rcases Nat.lt_or_ge i (B k + 2) with hlt | hge
  · -- forward: `below_fwd` from layer `i` reaches `B k + 2` (`i + 1 ≤ B k + 2` is `hlt`)
    exact below_fwd hWmono m k i hk hbase (B k + 2) hlt
  · -- backward: past the exit layer `B k + 1` the cut is constant, so it equals `cut i`
    have hconst := bracket_cut_const hD hWmono hUmono hsand m k hk (B k + 1)
      (fun hin => absurd (hexcl m k (B k + 1) hk hin) (Nat.not_succ_le_self (B k)))
      (B k + 2) i (Nat.le_refl _) hge
    rw [hconst]; exact hf

end E213.Lib.Math.NumberSystems.Real213.BracketModulus
