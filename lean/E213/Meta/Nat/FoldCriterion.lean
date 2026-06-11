import E213.Meta.Nat.VpSeparation

/-!
# FoldCriterion — when two powers are equal (∅-axiom)

A power `aᵏ` just multiplies `k` copies of `a`, so its prime-exponent
reading is `k` times `a`'s reading: `vp p (aᵏ) = k · vp p a` (that is
`vp_pow`).  Two positive numbers are equal exactly when their readings
match at every prime (that is `vp_separation`).  Put the two together
and you get the whole story of when one power equals another.

  * ★★ `pow_eq_pow_iff_vp` — `a^r = b^q  ↔  ∀ prime p, r·vp p a = q·vp p b`.
  * ★ `prime_pow_unique` — for distinct primes `p ≠ q`,
    `p^a = q^b → a = 0 ∧ b = 0`.  At the prime `p`, `p`'s exponent is `1`
    and `q`'s is `0`, so `a·1 = b·0` forces `a = 0`; symmetric for `b`.
  * `two_three_unique` — the concrete instance `2^a = 3^b → a = 0 ∧ b = 0`.
  * ★ `fold_iff_collinear` — `aˣ = b` (asked as `a^r = b^q`, `q > 0`) has a
    solution exactly when `a`'s and `b`'s exponent-vectors point the same
    way (one is a fixed rational multiple of the other at every prime).

This answers the question "does `aˣ = b` have a fractional answer `x = r/q`":
it does exactly when `a^r = b^q`, which by `pow_eq_pow_iff_vp` is "do the two
exponent-vectors point the same way".  Different primes never do, so
`2^a = 3^b` needs `a = b = 0`.

All ∅-axiom.  Built on `VpSeparation` (+ `VpMul`, `Valuation`).
-/

namespace E213.Meta.Nat.FoldCriterion

open E213.Meta.Nat.VpMul (IsPrime213 vp_pow vp_self_pow)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpSeparation (vp_separation vp_eq_zero_of_not_dvd)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §1 — the equality criterion -/

/-- ★★ **Two powers are equal exactly when their prime-exponent readings
    match at every prime.**  `a^r = b^q ↔ ∀ prime p, r·vp p a = q·vp p b`
    (for `a, b > 0`).

    (→) read both sides with `vp p`; `vp_pow` rewrites `vp p (a^r)` as
    `r·vp p a`, so equal numbers give equal readings.
    (←) the readings of `a^r` and `b^q` agree at every prime (again by
    `vp_pow`), and `vp_separation` says equal readings ⇒ equal numbers. -/
theorem pow_eq_pow_iff_vp {a b : Nat} (ha : 0 < a) (hb : 0 < b) (r q : Nat) :
    a ^ r = b ^ q ↔ ∀ p, IsPrime213 p → r * vp p a = q * vp p b := by
  constructor
  · intro hab p hp
    have := congrArg (vp p) hab
    rwa [vp_pow hp ha r, vp_pow hp hb q] at this
  · intro hmatch
    have har : 0 < a ^ r := Nat.pos_pow_of_pos r ha
    have hbq : 0 < b ^ q := Nat.pos_pow_of_pos q hb
    refine vp_separation har hbq ?_
    intro p hp
    rw [vp_pow hp ha r, vp_pow hp hb q]
    exact hmatch p hp

/-! ## §2 — distinct primes never collide -/

/-- For a prime `p` and a prime `q ≠ p`, `p ∤ q`: `q`'s only divisors are
    `1` and `q`, and `p` is neither (`p ≥ 2 ≠ 1`, and `p ≠ q`). -/
theorem prime_not_dvd_prime {p q : Nat} (hp : IsPrime213 p) (hq : IsPrime213 q)
    (hpq : p ≠ q) : ¬ p ∣ q := by
  intro hdvd
  rcases hq.2 p hdvd with h1 | hpq'
  · rw [h1] at hp; exact absurd hp.two_le (by decide)
  · exact hpq hpq'

/-- ★ **Distinct primes give independent axes.**  For primes `p ≠ q`,
    `p^a = q^b → a = 0 ∧ b = 0`.

    Read at the prime `p`: `vp p p = 1` (`vp_self_pow`) and `vp p q = 0`
    (`p ∤ q`, so `vp_eq_zero_of_not_dvd`), so `pow_eq_pow_iff_vp` gives
    `a·1 = b·0 = 0`, i.e. `a = 0`.  Read at `q` symmetrically for `b`. -/
theorem prime_pow_unique {p q a b : Nat} (hp : IsPrime213 p) (hq : IsPrime213 q)
    (hpq : p ≠ q) (h : p ^ a = q ^ b) : a = 0 ∧ b = 0 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.two_le
  have hmatch := (pow_eq_pow_iff_vp hppos hqpos a b).mp h
  -- vp p p = 1
  have hvp_pp : vp p p = 1 := by
    have := vp_self_pow hp 1; rwa [Nat.pow_one] at this
  have hvp_qq : vp q q = 1 := by
    have := vp_self_pow hq 1; rwa [Nat.pow_one] at this
  -- vp p q = 0, vp q p = 0
  have hvp_pq : vp p q = 0 :=
    vp_eq_zero_of_not_dvd hp hqpos (prime_not_dvd_prime hp hq hpq)
  have hvp_qp : vp q p = 0 :=
    vp_eq_zero_of_not_dvd hq hppos (prime_not_dvd_prime hq hp (fun e => hpq e.symm))
  constructor
  · -- at p: a * 1 = b * 0
    have e := hmatch p hp
    rw [hvp_pp, hvp_pq, Nat.mul_one, Nat.mul_zero] at e
    exact e
  · -- at q: a * 0 = b * 1
    have e := hmatch q hq
    rw [hvp_qq, hvp_qp, Nat.mul_zero, Nat.mul_one] at e
    exact e.symm

/-- A concrete instance of `prime_pow_unique`: `2^a = 3^b → a = 0 ∧ b = 0`.
    `2` and `3` are primes (divisor dichotomy), and `2 ≠ 3`. -/
theorem two_three_unique {a b : Nat} (h : 2 ^ a = 3 ^ b) : a = 0 ∧ b = 0 := by
  have two_prime : IsPrime213 2 := by
    refine ⟨by decide, ?_⟩
    intro d hd
    have hle : d ≤ 2 := le_of_dvd_pos d 2 (by decide) hd
    rcases E213.Tactic.NatHelper.cases_lt_three (Nat.lt_succ_of_le hle) with h0 | h1 | h2
    · subst h0; obtain ⟨c, hc⟩ := hd; rw [Nat.zero_mul] at hc; exact Nat.noConfusion hc
    · exact Or.inl h1
    · exact Or.inr h2
  have three_prime : IsPrime213 3 := by
    refine ⟨by decide, ?_⟩
    intro d hd
    have hle : d ≤ 3 := le_of_dvd_pos d 3 (by decide) hd
    rcases E213.Tactic.NatHelper.cases_lt_four (Nat.lt_succ_of_le hle) with h0 | h1 | h2 | h3
    · subst h0; obtain ⟨c, hc⟩ := hd; rw [Nat.zero_mul] at hc; exact Nat.noConfusion hc
    · exact Or.inl h1
    · -- 2 ∣ 3 is impossible
      exfalso; subst h2; obtain ⟨c, hc⟩ := hd
      -- 3 = 2 * c : c can only be 0 or 1, neither works
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · rcases E213.Tactic.NatHelper.cases_lt_two hc2 with hc0 | hc1
        · rw [hc0, Nat.mul_zero] at hc; exact absurd hc (by decide)
        · rw [hc1, Nat.mul_one] at hc; exact absurd hc (by decide)
      · have hle : 2 * 2 ≤ 2 * c := Nat.mul_le_mul_left 2 hc2
        rw [← hc] at hle; exact absurd hle (by decide)
    · exact Or.inr h3
  exact prime_pow_unique two_prime three_prime (by decide) h

/-! ## §3 — the fold criterion, named plainly -/

/-- ★ **The fold criterion.**  Asking "does `aˣ = b` have a fractional
    answer `x = r/q`" is asking "is `a^r = b^q`" (with `q > 0`).  By
    `pow_eq_pow_iff_vp` that holds exactly when `a`'s and `b`'s
    exponent-vectors point the same way: at every prime, `r·vp p a =
    q·vp p b`.  (For different primes they never do — `two_three_unique`.) -/
theorem fold_iff_collinear {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    (∃ r q, 0 < q ∧ a ^ r = b ^ q) ↔
    (∃ r q, 0 < q ∧ ∀ p, IsPrime213 p → r * vp p a = q * vp p b) := by
  constructor
  · rintro ⟨r, q, hq, hab⟩
    exact ⟨r, q, hq, (pow_eq_pow_iff_vp ha hb r q).mp hab⟩
  · rintro ⟨r, q, hq, hmatch⟩
    exact ⟨r, q, hq, (pow_eq_pow_iff_vp ha hb r q).mpr hmatch⟩

end E213.Meta.Nat.FoldCriterion
