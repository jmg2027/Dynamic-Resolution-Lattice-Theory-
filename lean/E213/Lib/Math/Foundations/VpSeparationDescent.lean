import E213.Lib.Math.Foundations.MonovariantFlow
import E213.Meta.Nat.VpSeparation

/-!
# UFD separation as a universal-descent-schema instance (∅-axiom)

`VpSeparation.vp_separation` (faithfulness of the prime-exponent coordinate —
unique factorization) is an instance of the universal descent schema
`descent_reaches` (`Lib/Math/Foundations/MonovariantFlow`).

  * carrier `VEPair` — a pair `(m,n)` of positives bundling its valuation-equality
    `∀ p prime, vp p m = vp p n` (carried in the *carrier*, not as a
    `descent_invariant` `Prop`-invariant `I`, which would need `propext`);
  * step `Peel` — divide both coordinates by a shared prime;
  * monovariant `μ = m + n` — strictly descends (`peel_step`);
  * normal form `m = 1 ∨ n = 1` — reads off `m = n` (`nf_eq`).

The start's equality `m = n` is recovered by lifting `t.m = t.n` back up the
`Reaches` chain (`reaches_eq_back`): each peel multiplied both coordinates by the
*same* prime, so equality is preserved across every step.  This is the third
number-theory instance of the descent schema (with GCD and Markov), ∅-axiom —
`research-notes/frontiers/descent_schema_universal.md`.
-/

namespace E213.Lib.Math.Foundations.VpSeparationDescent

open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpSeparation
  (exists_prime_factor dvd_iff_one_le_vp vp_div_prime vp_div_prime_other
   vp_eq_zero_of_not_dvd)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)
open E213.Tactic.NatHelper (add_right_cancel_pure)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.Foundations.MonovariantFlow (Reaches descent_reaches)

/-- A pair `(m,n)` of positives with equal prime valuations everywhere. -/
structure VEPair where
  m : Nat
  n : Nat
  hm : 0 < m
  hn : 0 < n
  hvp : ∀ p, IsPrime213 p → vp p m = vp p n

/-- The peel step: divide both coordinates by a shared prime. -/
def Peel (s t : VEPair) : Prop :=
  ∃ p, IsPrime213 p ∧ p ∣ s.m ∧ p ∣ s.n ∧ t.m = s.m / p ∧ t.n = s.n / p

/-- **The schema's descent obligation**: an ordered valuation-equal pair is either
    a normal form (`m = 1 ∨ n = 1`) or peels a shared prime to a strictly smaller
    sum, still valuation-equal.  This is `vp_separation`'s induction step with the
    strong-recursion removed (the schema supplies it). -/
theorem peel_step (s : VEPair) :
    (s.m = 1 ∨ s.n = 1) ∨ ∃ t, Peel s t ∧ t.m + t.n < s.m + s.n := by
  have hsm := s.hm
  have hsn := s.hn
  rcases Nat.lt_or_ge s.m 2 with hm2 | hm2
  · exact Or.inl (Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hm2) hsm))
  · rcases Nat.lt_or_ge s.n 2 with hn2 | hn2
    · exact Or.inl (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hn2) hsn))
    · obtain ⟨p, hp, hpm⟩ := exists_prime_factor s.m s.m (Nat.le_refl s.m) hm2
      have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
      have hpvm : 1 ≤ vp p s.m := (dvd_iff_one_le_vp hp hsm).mp hpm
      have hpvn : 1 ≤ vp p s.n := by rw [← s.hvp p hp]; exact hpvm
      have hpn : p ∣ s.n := (dvd_iff_one_le_vp hp hsn).mpr hpvn
      obtain ⟨cm, hcm⟩ := hpm
      obtain ⟨cn, hcn⟩ := hpn
      have hmdiv : s.m / p = cm := by rw [hcm]; exact mul_div_cancel_left_pure p cm hppos
      have hndiv : s.n / p = cn := by rw [hcn]; exact mul_div_cancel_left_pure p cn hppos
      have hcm_pos : 0 < cm := by
        rcases Nat.eq_zero_or_pos cm with h0 | hpos
        · exfalso; rw [h0, Nat.mul_zero] at hcm; rw [hcm] at hsm; exact Nat.lt_irrefl 0 hsm
        · exact hpos
      have hcn_pos : 0 < cn := by
        rcases Nat.eq_zero_or_pos cn with h0 | hpos
        · exfalso; rw [h0, Nat.mul_zero] at hcn; rw [hcn] at hsn; exact Nat.lt_irrefl 0 hsn
        · exact hpos
      have hvp' : ∀ q, IsPrime213 q → vp q (s.m / p) = vp q (s.n / p) := by
        intro q hq
        by_cases hqp : q = p
        · subst hqp
          have em : vp q (s.m / q) + 1 = vp q s.m := vp_div_prime hq hsm ⟨cm, hcm⟩
          have en : vp q (s.n / q) + 1 = vp q s.n := vp_div_prime hq hsn ⟨cn, hcn⟩
          have hcancel : vp q (s.m / q) + 1 = vp q (s.n / q) + 1 := by
            rw [em, en]; exact s.hvp q hq
          exact add_right_cancel_pure hcancel
        · have em : vp q (s.m / p) = vp q s.m := vp_div_prime_other hp hq hqp hsm ⟨cm, hcm⟩
          have en : vp q (s.n / p) = vp q s.n := vp_div_prime_other hp hq hqp hsn ⟨cn, hcn⟩
          rw [em, en]; exact s.hvp q hq
      have hsum_lt : s.m / p + s.n / p < s.m + s.n := by
        rw [hmdiv, hndiv, hcm, hcn]
        have h1 : cm < p * cm := by
          have hp2cm : 2 * cm ≤ p * cm := Nat.mul_le_mul_right cm hp.two_le
          have hlt2 : cm < 2 * cm := by rw [Nat.two_mul]; exact Nat.lt_add_of_pos_left hcm_pos
          exact Nat.lt_of_lt_of_le hlt2 hp2cm
        have h2 : cn ≤ p * cn := by
          calc cn = 1 * cn := (Nat.one_mul cn).symm
            _ ≤ p * cn := Nat.mul_le_mul_right cn (Nat.le_trans (by decide) hp.two_le)
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le h1 h2) (Nat.le_refl _)
      exact Or.inr
        ⟨⟨s.m / p, s.n / p, by rw [hmdiv]; exact hcm_pos, by rw [hndiv]; exact hcn_pos, hvp'⟩,
         ⟨p, hp, ⟨cm, hcm⟩, ⟨cn, hcn⟩, rfl, rfl⟩, hsum_lt⟩

/-- A normal form (`m = 1 ∨ n = 1`) with valuation-equality has `m = n`: a value
    `≥ 2` has a prime factor of positive valuation, which `1` lacks. -/
theorem nf_eq (t : VEPair) (h : t.m = 1 ∨ t.n = 1) : t.m = t.n := by
  rcases h with hm1 | hn1
  · rcases Nat.lt_or_ge t.n 2 with hn2 | hn2
    · have hn1 : t.n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hn2) t.hn
      rw [hm1, hn1]
    · exfalso
      obtain ⟨q, hq, hqn⟩ := exists_prime_factor t.n t.n (Nat.le_refl t.n) hn2
      have hqvn : 1 ≤ vp q t.n := (dvd_iff_one_le_vp hq t.hn).mp hqn
      have hqvm : vp q t.m = 0 := by
        rw [hm1]
        refine vp_eq_zero_of_not_dvd hq (by decide) ?_
        intro hd
        have hle1 := le_of_dvd_pos q 1 (by decide) hd
        exact absurd (Nat.le_trans hq.two_le hle1) (by decide)
      rw [← t.hvp q hq, hqvm] at hqvn
      exact absurd hqvn (by decide)
  · rcases Nat.lt_or_ge t.m 2 with hm2 | hm2
    · have hm1 : t.m = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hm2) t.hm
      rw [hm1, hn1]
    · exfalso
      obtain ⟨q, hq, hqm⟩ := exists_prime_factor t.m t.m (Nat.le_refl t.m) hm2
      have hqvm : 1 ≤ vp q t.m := (dvd_iff_one_le_vp hq t.hm).mp hqm
      have hqvn : vp q t.n = 0 := by
        rw [hn1]
        refine vp_eq_zero_of_not_dvd hq (by decide) ?_
        intro hd
        have hle1 := le_of_dvd_pos q 1 (by decide) hd
        exact absurd (Nat.le_trans hq.two_le hle1) (by decide)
      rw [t.hvp q hq, hqvn] at hqvm
      exact absurd hqvm (by decide)

/-- A single peel preserves coordinate equality both ways: `s.m = p·t.m`,
    `s.n = p·t.n`, so `t.m = t.n ⟹ s.m = s.n`. -/
theorem peel_eq_back {s t : VEPair} (h : Peel s t) (heq : t.m = t.n) : s.m = s.n := by
  obtain ⟨p, hp, hpm, hpn, htm, htn⟩ := h
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  obtain ⟨cm, hcm⟩ := hpm
  obtain ⟨cn, hcn⟩ := hpn
  have hmdiv : s.m / p = cm := by rw [hcm]; exact mul_div_cancel_left_pure p cm hppos
  have hndiv : s.n / p = cn := by rw [hcn]; exact mul_div_cancel_left_pure p cn hppos
  have hceq : cm = cn := by rw [← hmdiv, ← hndiv, ← htm, ← htn]; exact heq
  rw [hcm, hcn, hceq]

/-- Coordinate equality lifts the whole `Reaches` chain back to the start. -/
theorem reaches_eq_back : ∀ {s t : VEPair}, Reaches Peel s t → t.m = t.n → s.m = s.n := by
  intro s t h
  induction h with
  | refl => intro heq; exact heq
  | head hxy _ ih => intro heq; exact peel_eq_back hxy (ih heq)

/-- ★★★★★ **UFD separation IS a `descent_reaches` instance.**  `vp_separation`
    reproved through the universal descent schema: the valuation-equal pair
    `(m,n)` peels shared primes (`descent_reaches` supplies the recursion) to a
    normal form `(1,1)`, and the equality lifts back to the start, `m = n`.  The
    third number-theory instance of the descent schema (GCD, Markov, UFD). -/
theorem vp_separation_via_schema {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : ∀ p, IsPrime213 p → vp p m = vp p n) : m = n := by
  obtain ⟨t, hnf, hr⟩ := descent_reaches Peel (fun s => s.m + s.n)
    (fun s => s.m = 1 ∨ s.n = 1) peel_step ⟨m, n, hm, hn, h⟩
  exact reaches_eq_back hr (nf_eq t hnf)

end E213.Lib.Math.Foundations.VpSeparationDescent
