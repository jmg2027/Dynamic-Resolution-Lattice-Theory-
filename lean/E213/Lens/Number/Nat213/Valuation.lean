import E213.Lens.Number.Nat213.WellOrder

/-!
# Lens.Number.Nat213.Valuation — prime-power valuation over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, leg-2 — the `p`-adic structure on `Nat213`.  A valuation counts *how many
times* a prime divides, and that count can be **zero** — but `Nat213` has no zero
(`Peano.no_absorbing_element`).  Two complementary forms, per the design decision:

- **A. Readout into ℕ** (`vp : Nat213 → Nat213 → Nat`): the multiplicity is a *count*, so it reads
  *out* into ℕ (the legitimate Lens direction, like `toNat`/`Raw.depth`), where `0` lives naturally.
  Uses `Peano.powNat` (the `Nat`-exponent power, `powNat p 0 = one`).  `pow_vp_dvd`:
  `p^(vp p n) ∣ n` — the valuation's power genuinely divides.
- **B. `p`-adic factorization** (`padic_factorization`): fully `Nat213`-native, no readout — for a
  prime `p` that *divides* `n` (so the exponent is ≥ 1, expressible in `Nat213`), `n = p^k · m` with
  `¬ p ∣ m`.  This is the FTA-exponent form on the generated carrier.

∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.Valuation

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul one succ pow pow_one pow_succ pow_add mul_assoc one_mul powNat powNat_zero powNat_succ)
open E213.Lens.Number.Nat213.Order (lt le lt_add_right mul_right_cancel mul_left_cancel le_total)
open E213.Lens.Number.Nat213.Divisibility
  (Dvd one_dvd dvd_mul_left dvd_imp_eq_or_lt dvd_mul_of_dvd_left self_dvd_pow)
open E213.Lens.Number.Nat213.Irreducible (Irreducible)
open E213.Lens.Number.Nat213.WellOrder (strong_induction)

/-! ## B — the `p`-adic factorization (fully `Nat213`-native, for `p ∣ n`) -/

/-- A divisor's multiple strictly exceeds it — `p ≠ one → c < p·c`.  (`c ∣ p·c`, and equality would
    cancel to `p = one`.)  The descent bound for the `p`-adic recursion. -/
private theorem lt_mul_of_ne_one {p : Nat213} (hp : p ≠ one) (c : Nat213) : lt c (mul p c) := by
  rcases dvd_imp_eq_or_lt (dvd_mul_left p c) with heq | hlt
  · have h1 : mul one c = mul p c := by rw [one_mul]; exact heq
    exact absurd (mul_right_cancel h1).symm hp
  · exact hlt

/-- ★★★ **`p`-adic factorization over the Raw-generated ℕ₊** — for an irreducible `p` that divides
    `n`, `n = p^k · m` with `¬ p ∣ m` (the maximal `p`-power split, `k ≥ 1` since `p ∣ n`).  Strong
    induction on `n`: write `n = p·c`; if `p ∤ c` take `k=1, m=c`; else recurse on `c < n` and
    prepend one `p` (`k ↦ k+1`).  Fully `Nat213`-native — no readout into ℕ.  ∅-axiom. -/
theorem padic_factorization {p : Nat213} (hp : Irreducible p) :
    ∀ n : Nat213, Dvd p n → ∃ k m : Nat213, n = mul (pow p k) m ∧ ¬ Dvd p m := by
  refine strong_induction
    (C := fun n => Dvd p n → ∃ k m : Nat213, n = mul (pow p k) m ∧ ¬ Dvd p m) ?_
  intro n ih hpn
  obtain ⟨c, hc⟩ := hpn
  by_cases hpc : Dvd p c
  · have hcn : lt c n := by rw [hc]; exact lt_mul_of_ne_one hp.1 c
    obtain ⟨k, m, hkm, hm⟩ := ih c hcn hpc
    exact ⟨succ k, m, by rw [hc, hkm, pow_succ, mul_assoc], hm⟩
  · exact ⟨one, c, by rw [hc, pow_one], hpc⟩

/-- The exponent of a `p`-adic factorization is determined under `le` — if `p^k₁·m₁ = p^k₂·m₂` with
    `¬ p ∣ m₁` and `k₁ ≤ k₂`, then `k₁ = k₂`.  A strict `k₁ < k₂` would put a `p` into `m₁`
    (`p ∣ p^d`, `d ≥ 1`) after cancelling `p^k₁`, contradicting `¬ p ∣ m₁`. -/
private theorem padic_exp_eq_of_le {p k₁ k₂ m₁ m₂ : Nat213}
    (h : mul (pow p k₁) m₁ = mul (pow p k₂) m₂) (hm₁ : ¬ Dvd p m₁) (hle : le k₁ k₂) : k₁ = k₂ := by
  rcases hle with rfl | hlt
  · rfl
  · exfalso
    obtain ⟨d, hd⟩ := hlt
    rw [← hd, pow_add, mul_assoc] at h
    have hm : m₁ = mul (pow p d) m₂ := mul_left_cancel h
    apply hm₁
    rw [hm]
    exact dvd_mul_of_dvd_left (self_dvd_pow p d) m₂

/-- ★★★ **Uniqueness of the `p`-adic factorization** — the `(k, m)` of `padic_factorization` is
    unique: if `p^k₁·m₁ = p^k₂·m₂` with both `m` coprime to `p` (`¬ p ∣ mᵢ`), then `k₁ = k₂` and
    `m₁ = m₂`.  By `le_total` on the exponents + `padic_exp_eq_of_le`, then `mul_left_cancel`.  This
    welds the two valuation forms: B's exponent `k` is well-defined, the native counterpart of A's
    `vp`.  ∅-axiom. -/
theorem padic_factorization_unique {p k₁ k₂ m₁ m₂ : Nat213}
    (h : mul (pow p k₁) m₁ = mul (pow p k₂) m₂) (hm₁ : ¬ Dvd p m₁) (hm₂ : ¬ Dvd p m₂) :
    k₁ = k₂ ∧ m₁ = m₂ := by
  rcases le_total k₁ k₂ with hle | hle
  · have hk : k₁ = k₂ := padic_exp_eq_of_le h hm₁ hle
    subst hk; exact ⟨rfl, mul_left_cancel h⟩
  · have hk : k₂ = k₁ := padic_exp_eq_of_le h.symm hm₂ hle
    subst hk; exact ⟨rfl, mul_left_cancel h⟩

/-! ## A — the `p`-adic valuation, read out into ℕ -/

/-- Downward search for the largest `k ≤ b` with `p^k ∣ n` (`powNat` for the `Nat` exponent, so
    the empty case `k=0` is available).  Decides on the constructive `Dvd` (`Factorization.decDvd`),
    no `Classical`. -/
def vpSearch (p n : Nat213) : Nat → Nat
  | 0     => 0
  | k + 1 => if Dvd (powNat p (k + 1)) n then k + 1 else vpSearch p n k

/-- ★ **The `p`-adic valuation of `n`, read out into ℕ** — the multiplicity of `p` in `n`, a
    *count* (so it lands in ℕ, where `0` lives, not in `Nat213`).  Searches down from the bound
    `toNat n`. -/
def vp (p n : Nat213) : Nat := vpSearch p n n.toNat

/-- The searched power divides `n`, at every bound. -/
theorem vpSearch_dvd (p n : Nat213) : ∀ b : Nat, Dvd (powNat p (vpSearch p n b)) n
  | 0     => by show Dvd (powNat p 0) n; rw [powNat_zero]; exact one_dvd n
  | b + 1 => by
      show Dvd (powNat p (if Dvd (powNat p (b + 1)) n then b + 1 else vpSearch p n b)) n
      by_cases h : Dvd (powNat p (b + 1)) n
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact vpSearch_dvd p n b

/-- The search result never exceeds its bound. -/
theorem vpSearch_le (p n : Nat213) : ∀ b : Nat, vpSearch p n b ≤ b
  | 0     => Nat.le_refl 0
  | b + 1 => by
      show (if Dvd (powNat p (b + 1)) n then b + 1 else vpSearch p n b) ≤ b + 1
      by_cases h : Dvd (powNat p (b + 1)) n
      · rw [if_pos h]; exact Nat.le_refl _
      · rw [if_neg h]; exact Nat.le_succ_of_le (vpSearch_le p n b)

/-- ★★★ **The valuation's power divides** — `p^(vp p n) ∣ n`.  So `vp` is a genuine exponent: the
    `p`-power it names is an actual divisor of `n`.  ∅-axiom (the count reads out into ℕ; the
    divisor stays in `Nat213`). -/
theorem pow_vp_dvd (p n : Nat213) : Dvd (powNat p (vp p n)) n := vpSearch_dvd p n n.toNat

end E213.Lens.Number.Nat213.Valuation
