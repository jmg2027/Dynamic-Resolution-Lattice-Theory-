import E213.Meta.Nat.PolyNatMTactic

/-!
# Product-of-consecutive-integers divisibility `k! ∣ ∏ k consecutive` (∅-axiom)

The integrality of binomial coefficients in disguise (`C(n,k) = ∏/k!` ∈ ℕ):

  * `two_dvd_consec2`  : `2 ∣ n(n+1)`            (one of two consecutive is even).
  * `six_dvd_consec3`  : `6 ∣ n(n+1)(n+2)`       (3! divides 3 consecutive).
  * `twentyfour_dvd_consec4` : `24 ∣ n(n+1)(n+2)(n+3)` (4! divides 4 consecutive).

Induction with explicit divisibility witnesses + `ring_nat`: the cross-step
identity `(k+1)…(k+j) = k…(k+j−1) + j·(k+1)…(k+j−1)` reduces each case to the IH
plus the shifted lower fact (`6∣3·(k+1)(k+2)` from `2∣(k+1)(k+2)`, etc.).
Genuinely absent (`6 ∣ …` had zero corpus matches).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ConsecutiveProduct

/-- `a ∣ x → a ∣ y → a ∣ (x + y)`, via explicit witnesses + `ring_nat`. -/
theorem dvd_add213 {a x y : Nat} (hx : a ∣ x) (hy : a ∣ y) : a ∣ (x + y) := by
  obtain ⟨wx, hwx⟩ := hx
  obtain ⟨wy, hwy⟩ := hy
  refine ⟨wx + wy, ?_⟩
  rw [hwx, hwy]; ring_nat

/-- ★ **Two consecutive: one is even** — `2 ∣ n(n+1)`. -/
theorem two_dvd_consec2 (n : Nat) : 2 ∣ n * (n + 1) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w + (k + 1), ?_⟩
    have hstep : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring_nat
    rw [hstep, hw]; ring_nat

/-- ★ **3! divides 3 consecutive** — `6 ∣ n(n+1)(n+2)`. -/
theorem six_dvd_consec3 (n : Nat) : 6 ∣ n * (n + 1) * (n + 2) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := two_dvd_consec2 (k + 1)
    have h3 : (6 : Nat) ∣ 3 * ((k + 1) * (k + 1 + 1)) := by
      refine ⟨v, ?_⟩; rw [hv]; ring_nat
    obtain ⟨t, ht⟩ := dvd_add213 ih h3
    refine ⟨t, ?_⟩
    have hstep : (k + 1) * (k + 1 + 1) * (k + 1 + 2)
        = k * (k + 1) * (k + 2) + 3 * ((k + 1) * (k + 1 + 1)) := by ring_nat
    rw [hstep, ht]

/-- ★ **4! divides 4 consecutive** — `24 ∣ n(n+1)(n+2)(n+3)`. -/
theorem twentyfour_dvd_consec4 (n : Nat) :
    24 ∣ n * (n + 1) * (n + 2) * (n + 3) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := six_dvd_consec3 (k + 1)
    have h4 : (24 : Nat) ∣ 4 * ((k + 1) * (k + 1 + 1) * (k + 1 + 2)) := by
      refine ⟨v, ?_⟩; rw [hv]; ring_nat
    obtain ⟨t, ht⟩ := dvd_add213 ih h4
    refine ⟨t, ?_⟩
    have hstep : (k + 1) * (k + 1 + 1) * (k + 1 + 2) * (k + 1 + 3)
        = k * (k + 1) * (k + 2) * (k + 3)
          + 4 * ((k + 1) * (k + 1 + 1) * (k + 1 + 2)) := by ring_nat
    rw [hstep, ht]

/-- Concrete smoke: `2∣20`, `6∣120`, `24∣840`. -/
theorem consec_smoke :
    2 ∣ 4 * 5 ∧ 6 ∣ 4 * 5 * 6 ∧ 24 ∣ 4 * 5 * 6 * 7 :=
  ⟨⟨10, rfl⟩, ⟨20, rfl⟩, ⟨35, rfl⟩⟩

end E213.Lib.Math.NumberTheory.ConsecutiveProduct
