import E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus

/-!
# PointingLimit — the conceived limit is a pointing: reached by no value, decided in finite

The originator's thesis (2026-06-13), made computational: to *conceive* an infinity
(a limit, a real) is to point at it, and a pointing is a discrete, finite act — a
monotone convergent cut-sequence with a recurrence.  "Is the limit discrete or
continuous, finite or attained?" is a malformed question: the limit-*value* is reached
by no term, while every finite-resolution question about it is settled at a finite,
discretely-determined layer.  What is real, and what is computed, is the **pointing**
and the **shape of its residue** (the cross-determinant against the denominator — the
modulus degree, `DegreeCriterion`), never a limit-value entering a calculation.

This file pins the two halves of that dissolution for any rate-carrying pointing:

  * ★★★ `conv_strict_increase` — the convergent **values strictly advance** across
    every gap (`i < j ⟹ a_i·d_j < a_j·d_i`): the pointing never stalls, no two stages
    coincide, the limit-value is approached by none of them.  (Lifts the one-step
    `hmonoS` to all gaps by fraction-`<` transitivity.)
  * ★★★ `limit_unreached_but_decided` — the dissolution as one statement: the values
    strictly advance forever, **and** every cut `x ⋚ m/k` is constant past a finite,
    constructed layer (`rate_total_modulus`).  The limit enters computation only as
    the discrete modulus — the residue's shape — never as a value.

Cf. `Theory/Raw/CoResidue.object1_not_surjective` (the residue is outside every view's
image — reached by none); `DegreeCriterion` (the residue's shape *is* the modulus);
`theory/essays/foundations/imagining_infinity.md` (the thesis in full).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.PointingLimit

open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (Htel rcut rate_total_modulus)
open E213.Tactic.NatHelper (mul_assoc)

variable {a d : Nat → Nat}

/-- Transitivity of the convergent strict order, cross-multiplied to ℕ: from
    `a_i/d_i < a_m/d_m` and `a_m/d_m < a_n/d_n` (positive denominators) conclude
    `a_i/d_i < a_n/d_n`.  The fraction order is genuinely an order — the pointing's
    stages are linearly arranged. -/
private theorem cross_trans {ai am an di dm dn : Nat}
    (hdn : 1 ≤ dn) (hdi : 1 ≤ di)
    (h1 : ai * dm < am * di) (h2 : am * dn < an * dm) : ai * dn < an * di := by
  have e1 : ai * dm * dn < am * di * dn := by
    have hle : ai * dm * dn + dn ≤ am * di * dn := by
      have h := Nat.mul_le_mul_right dn h1
      rwa [Nat.succ_mul] at h
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hdn) hle
  have e2 : am * dn * di < an * dm * di := by
    have hle : am * dn * di + di ≤ an * dm * di := by
      have h := Nat.mul_le_mul_right di h2
      rwa [Nat.succ_mul] at h
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hdi) hle
  have e3 : am * di * dn = am * dn * di := by
    rw [mul_assoc, Nat.mul_comm di dn, ← mul_assoc]
  have chain : ai * dm * dn < an * dm * di := Nat.lt_trans (e3 ▸ e1) e2
  have eL : ai * dm * dn = (ai * dn) * dm := by
    rw [mul_assoc, Nat.mul_comm dm dn, ← mul_assoc]
  have eR : an * dm * di = (an * di) * dm := by
    rw [mul_assoc, Nat.mul_comm dm di, ← mul_assoc]
  rw [eL, eR] at chain
  rcases Nat.lt_or_ge (ai * dn) (an * di) with h | h
  · exact h
  · exact absurd (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right dm h) chain) (Nat.lt_irrefl _)

/-- The convergents strictly advance across every gap (`i+1+t` form). -/
theorem conv_strict (hd : ∀ i, 1 ≤ d i) (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i) :
    ∀ i t, a i * d (i+1+t) < a (i+1+t) * d i := by
  intro i t
  induction t with
  | zero => exact hmonoS i
  | succ t ih =>
    exact cross_trans (hd ((i+1+t)+1)) (hd i) ih (hmonoS (i+1+t))

/-- ★★★ **The pointing's values strictly advance** — for `i < j`, `a_i·d_j < a_j·d_i`.
    No two stages coincide; the sequence never stalls.  The limit-value is approached
    by none of the convergents — it is the *name of the pointing*, not a term in it. -/
theorem conv_strict_increase (hd : ∀ i, 1 ≤ d i)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i) {i j : Nat} (hij : i < j) :
    a i * d j < a j * d i := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hij
  exact conv_strict hd hmonoS i t

/-- ★★★ **Reached by no value, decided in finite.**  For any rate-carrying pointing:
    (1) the convergent values strictly advance across every gap — the limit is reached
    by none of them; (2) every cut `x ⋚ m/k` is constant past a finite, constructed
    layer (`N = k+2`).  The infinity enters computation *only* as the discrete modulus
    — the shape of the residue — never as a limit-value.  This is the thesis
    "conceiving ∞ is a discrete act" as a theorem: the value-infinity is computationally
    inert; the pointing and its residue-shape carry everything. -/
theorem limit_unreached_but_decided
    (hd : ∀ i, 1 ≤ d i) (htel : Htel a d)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i) :
    (∀ i j, i < j → a i * d j < a j * d i)
    ∧ (∀ m k, 1 ≤ k → ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k) :=
  ⟨fun _ _ hij => conv_strict_increase hd hmonoS hij,
   fun m k hk => rate_total_modulus hd htel hmono hmonoS m k hk⟩

end E213.Lib.Math.NumberSystems.Real213.Modulus.PointingLimit
