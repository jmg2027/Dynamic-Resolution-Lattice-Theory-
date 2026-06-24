import E213.Meta.Nat.VpSub213
import E213.Lib.Math.NumberTheory.EuclidLemmaGrounded

/-!
# Grounded `vₚ` multiplicativity — `vpSub(a·b) = vpSub a + vpSub b` (∅-axiom)

The capstone of the FTA-uniqueness chain: the prime-power valuation is additive over products.
`PrimeValuation.vp_mul` already proves this, but on the `Nat.mod`-based `Valuation.vp` and through the
`Nat.mod`-routed `prime_dvd_mul` (both `Nat.lt_wfRel`-dirty).  This regrounds it on the structural
`VpSub213.vpSub` (`subMod`-based) and the grounded `EuclidLemmaGrounded.prime_dvd_mul` (`subMod`
Bézout).  The bookkeeping is unchanged: extract unit parts `a = pᵅ·u`, `b = pᵝ·v` with `p ∤ u,v`
(`vpSub_not_dvd_succ`), so `a·b = p^{α+β}·(u·v)` with `p ∤ u·v` (grounded Euclid), pinning
`vpSub(a·b) = α+β`.

`vpSub_mul` carries **no `Nat.div`/`Nat.mod`/`Nat.lt_wfRel`** — the prime-power valuation is now a
fully grounded group homomorphism `ℕ_{>0} → ℕ` at primes.  ∅-axiom.  This closes the conceptual chain
to FTA *uniqueness* (`vₚ` determines the exponent of each prime in a factorisation).
-/

namespace E213.Lib.Math.NumberTheory.VpMulGrounded

open E213.Meta.Nat.VpSub213 (vpSub pow_vpSub_dvd vpSub_not_dvd_succ le_vpSub_iff)
open E213.Lib.Math.NumberTheory.EuclidLemmaGrounded (prime_dvd_mul)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Tactic.NatHelper (mul_assoc mul_left_comm)

/-! ## §0 — pure arithmetic helpers (core analogues carry `propext`) -/

/-- Pure `p^(m+n) = p^m · p^n` (`Nat.pow_add` carries `propext`). -/
private theorem pow_add_pure (p m : Nat) : ∀ n, p ^ (m + n) = p ^ m * p ^ n
  | 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
    rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, pow_add_pure p m n, mul_assoc]

/-- Pure 4-factor swap `a·b·(c·d) = a·c·(b·d)` (`Nat.mul_mul_mul_comm` carries `propext`). -/
private theorem mul4_swap (a b c d : Nat) : a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc, mul_left_comm b c d, ← mul_assoc]

/-- Left-cancellation of a positive factor in a divisibility. -/
private theorem dvd_of_mul_dvd_mul_left {c x y : Nat} (hc : 0 < c) (h : c * x ∣ c * y) : x ∣ y := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, Nat.eq_of_mul_eq_mul_left hc (by rw [hw]; exact mul_assoc c x w)⟩

/-- The unit part `a / pᵛ` is not divisible by `p` (else `p^{v+1} ∣ a`). -/
private theorem unit_not_dvd {p a u : Nat} (hp2 : 2 ≤ p) (ha : 0 < a)
    (hu : a = p ^ (vpSub p a) * u) : ¬ p ∣ u := by
  intro hdu
  obtain ⟨w, hw⟩ := hdu
  refine vpSub_not_dvd_succ p a hp2 ha ⟨w, ?_⟩
  calc a = p ^ (vpSub p a) * u := hu
    _ = p ^ (vpSub p a) * (p * w) := by rw [hw]
    _ = p ^ (vpSub p a + 1) * w := by rw [Nat.pow_succ]; exact (mul_assoc _ _ _).symm

/-! ## §1 — multiplicativity -/

/-- ★★★ **`vₚ` is additive over products** at a prime: `vpSub(a·b) = vpSub a + vpSub b` (`a, b > 0`),
    fully grounded.  Lower bound `p^{α}·p^{β} = p^{α+β} ∣ a·b`; upper bound from
    `a·b = p^{α+β}·(u·v)` with `p ∤ u·v` (grounded Euclid), so `p^{α+β+1} ∤ a·b`.  No `Nat.mod`/
    `Nat.div`/`Nat.lt_wfRel`, no `Int`. ∅-axiom. -/
theorem vpSub_mul {p a b : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b) :
    vpSub p (a * b) = vpSub p a + vpSub p b := by
  have hq : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hq
  have hab : 0 < a * b := Nat.mul_pos ha hb
  obtain ⟨u, hu⟩ := pow_vpSub_dvd p a hp0
  obtain ⟨v, hv⟩ := pow_vpSub_dvd p b hp0
  have hpu : ¬ p ∣ u := unit_not_dvd hq ha hu
  have hpv : ¬ p ∣ v := unit_not_dvd hq hb hv
  have hlow : p ^ (vpSub p a + vpSub p b) ∣ a * b := by
    refine ⟨u * v, ?_⟩
    calc a * b = (p ^ (vpSub p a) * u) * (p ^ (vpSub p b) * v) := by rw [← hu, ← hv]
      _ = p ^ (vpSub p a + vpSub p b) * (u * v) := by rw [pow_add_pure]; exact mul4_swap _ _ _ _
  have hhigh : ¬ p ^ (vpSub p a + vpSub p b + 1) ∣ a * b := by
    intro hdv
    have hab_eq : a * b = p ^ (vpSub p a + vpSub p b) * (u * v) := by
      calc a * b = (p ^ (vpSub p a) * u) * (p ^ (vpSub p b) * v) := by rw [← hu, ← hv]
        _ = p ^ (vpSub p a + vpSub p b) * (u * v) := by rw [pow_add_pure]; exact mul4_swap _ _ _ _
    rw [hab_eq, show p ^ (vpSub p a + vpSub p b + 1) = p ^ (vpSub p a + vpSub p b) * p from by
      rw [Nat.pow_succ]] at hdv
    have hpuv : p ∣ u * v := dvd_of_mul_dvd_mul_left (Nat.pos_pow_of_pos _ hp0) hdv
    rcases prime_dvd_mul hp hpuv with h | h
    · exact hpu h
    · exact hpv h
  refine Nat.le_antisymm ?_ ((le_vpSub_iff p (a * b) _ hq hab).mp hlow)
  exact Nat.le_of_lt_succ (Nat.lt_of_not_le
    (mt (le_vpSub_iff p (a * b) (vpSub p a + vpSub p b + 1) hq hab).mpr hhigh))

end E213.Lib.Math.NumberTheory.VpMulGrounded
