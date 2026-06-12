import E213.Meta.Nat.VpMul

/-!
# VpSeparation — faithfulness of the prime-exponent coordinate (∅-axiom)

`VpMul.lean` builds the exponent-lattice homomorphism (`vp_mul`, `vp_pow`,
`vp_self_pow`, prime `p`).  This file closes the keystone: that homomorphism
is **injective** — a positive natural number is *determined* by its full
prime-exponent vector (`vp_separation`).  Unique factorization, stated as
the faithfulness of the `vp`-coordinate; this is what licenses `exp(n) =
(vp 2 n, vp 3 n, …)` as a coordinate on ℕ₊ rather than a lossy readout.

  * ★ `exists_prime_factor` — every `n ≥ 2` has a prime factor (a bounded
    least-divisor search; `Meta/Nat` sits below `Lib/Math`, so this is a
    local clone of the `FourSquare` search rather than an up-import that
    would invert the layer architecture).
  * `vp_div_prime` / `vp_div_prime_other` — dividing by a prime `p` drops
    `vp p` by exactly one and leaves every other `vp q` (`q ≠ p`) fixed.
  * ★★★ `vp_separation` — `(∀ p prime, vp p m = vp p n) → m = n` (`m,n>0`),
    by strong induction on `m + n`, peeling one prime factor at a time.

All ∅-axiom; built on `VpMul` (+ `Valuation`, `Gcd213`, `NatDiv213`,
`AddMod213`, `Pow213`/`NatHelper` transitively).
-/

namespace E213.Meta.Nat.VpSeparation

open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_self_pow)
open E213.Meta.Nat.Valuation (vp le_vp_iff drefl dtrans mod_zero_of_dvd)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)
open E213.Tactic.NatHelper (add_right_cancel_pure)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)

/-! ## §1 — decidable divisibility + the least-divisor search -/

/-- Decidable divisibility (constructive), `∅`-axiom via `n % k` (`0 < k`). -/
theorem dvd_dec (k n : Nat) (hk : 0 < k) : (k ∣ n) ∨ ¬ k ∣ n := by
  rcases Nat.eq_zero_or_pos (n % k) with h0 | hp
  · exact Or.inl (dvd_of_mod_eq_zero h0)
  · exact Or.inr (fun hd => by rw [mod_zero_of_dvd hk hd] at hp; exact Nat.lt_irrefl 0 hp)

/-- Bounded search: either `n` has a nontrivial divisor `2 ≤ d < n`, or no
    `d < k` with `2 ≤ d < n` divides `n`. -/
theorem searchDiv (n : Nat) : ∀ (k : Nat),
    (∃ d, 2 ≤ d ∧ d < n ∧ d ∣ n) ∨ (∀ d, 2 ≤ d → d < n → d < k → ¬ d ∣ n) := by
  intro k
  induction k with
  | zero => exact Or.inr (fun d _ _ hlt => absurd hlt (Nat.not_lt_zero d))
  | succ k ih =>
    rcases ih with hfound | hnone
    · exact Or.inl hfound
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · refine Or.inr (fun d hd2 hdn hdk1 => ?_)
        rcases Nat.lt_or_ge d k with hdk | hdk
        · exact hnone d hd2 hdn hdk
        · have he : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdk1) hdk
          rw [he] at hd2; exact absurd (Nat.lt_of_le_of_lt hd2 hk2) (Nat.lt_irrefl 2)
      · rcases Nat.lt_or_ge k n with hkn | hkn
        · rcases dvd_dec k n (Nat.lt_of_lt_of_le (by decide) hk2) with hdvd | hndvd
          · exact Or.inl ⟨k, hk2, hkn, hdvd⟩
          · refine Or.inr (fun d hd2 hdn hdk1 => ?_)
            rcases Nat.lt_or_ge d k with hdk | hdk
            · exact hnone d hd2 hdn hdk
            · have he : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdk1) hdk
              rw [he]; exact hndvd
        · refine Or.inr (fun d hd2 hdn hdk1 => ?_)
          rcases Nat.lt_or_ge d k with hdk | hdk
          · exact hnone d hd2 hdn hdk
          · have he : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdk1) hdk
            rw [he] at hdn; exact absurd (Nat.lt_of_lt_of_le hdn hkn) (Nat.lt_irrefl k)

/-- ★ **Every `n ≥ 2` has a prime factor** (`∅`-axiom; least-divisor argument
    via `searchDiv`, fuelled recursion).  Yields the `IsPrime213` predicate. -/
theorem exists_prime_factor : ∀ (fuel n : Nat), n ≤ fuel → 2 ≤ n →
    ∃ q, IsPrime213 q ∧ q ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro n hn h2; exact absurd (Nat.le_trans h2 hn) (by decide)
  | succ f ih =>
    intro n hnf h2
    rcases searchDiv n n with ⟨d, hd2, hdn, hddvd⟩ | hnone
    · obtain ⟨q, hqpr, hqd⟩ :=
        ih d (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdn hnf)) hd2
      exact ⟨q, hqpr, dtrans hqd hddvd⟩
    · -- no nontrivial divisor below `n`, so `n` itself is prime
      refine ⟨n, ⟨h2, ?_⟩, drefl n⟩
      intro e hen
      have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) h2
      have hen_le : e ≤ n := le_of_dvd_pos e n hnpos hen
      rcases Nat.lt_or_ge e n with helt | hege
      · rcases Nat.lt_or_ge e 2 with he2 | he2
        · rcases Nat.lt_or_ge e 1 with he1 | he1
          · exfalso
            have he0 : e = 0 := Nat.le_antisymm (Nat.le_of_lt_succ he1) (Nat.zero_le e)
            rw [he0] at hen
            obtain ⟨c, hc⟩ := hen; rw [Nat.zero_mul] at hc
            rw [hc] at h2; exact absurd h2 (by decide)
          · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ he2) he1)
        · exact absurd hen (hnone e he2 helt helt)
      · exact Or.inr (Nat.le_antisymm hen_le hege)

/-! ## §2 — the `vp`/divisibility bridge lemmas -/

/-- A prime not dividing `n` has valuation `0`. -/
theorem vp_eq_zero_of_not_dvd {p n : Nat} (hp : IsPrime213 p) (hn : 0 < n)
    (h : ¬ p ∣ n) : vp p n = 0 := by
  apply Nat.le_antisymm _ (Nat.zero_le _)
  rcases Nat.lt_or_ge (vp p n) 1 with hlt | hge
  · exact Nat.le_of_lt_succ hlt
  · exfalso
    have hdvd : p ^ 1 ∣ n := (le_vp_iff p n 1 hp.two_le hn).mpr hge
    rw [Nat.pow_one] at hdvd
    exact h hdvd

/-- For prime `p` and `n > 0`, `p ∣ n ↔ 1 ≤ vp p n`. -/
theorem dvd_iff_one_le_vp {p n : Nat} (hp : IsPrime213 p) (hn : 0 < n) :
    p ∣ n ↔ 1 ≤ vp p n := by
  have hiff := le_vp_iff p n 1 hp.two_le hn
  rwa [Nat.pow_one] at hiff

/-- Self axis: for prime `p` dividing `n > 0`, `vp p (n / p) + 1 = vp p n`. -/
theorem vp_div_prime {p n : Nat} (hp : IsPrime213 p) (hn : 0 < n) (hpn : p ∣ n) :
    vp p (n / p) + 1 = vp p n := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  obtain ⟨c, hc⟩ := hpn
  have hdiv : n / p = c := by rw [hc]; exact mul_div_cancel_left_pure p c hppos
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with hc0 | hcp
    · exfalso; rw [hc0, Nat.mul_zero] at hc; rw [hc] at hn; exact Nat.lt_irrefl 0 hn
    · exact hcp
  have hvpp : vp p p = 1 := by
    have hsp := vp_self_pow hp 1; rwa [Nat.pow_one] at hsp
  have key : vp p n = vp p c + 1 := by
    rw [hc, vp_mul hp hppos hc_pos, hvpp, Nat.add_comm]
  rw [hdiv, key]

/-- Cross axis: for distinct primes `p ≠ q` with `p ∣ n > 0`,
    `vp q (n / p) = vp q n`. -/
theorem vp_div_prime_other {p q n : Nat} (hp : IsPrime213 p) (hq : IsPrime213 q)
    (hpq : q ≠ p) (hn : 0 < n) (hpn : p ∣ n) :
    vp q (n / p) = vp q n := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  obtain ⟨c, hc⟩ := hpn
  have hdiv : n / p = c := by rw [hc]; exact mul_div_cancel_left_pure p c hppos
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with hc0 | hcp
    · exfalso; rw [hc0, Nat.mul_zero] at hc; rw [hc] at hn; exact Nat.lt_irrefl 0 hn
    · exact hcp
  have hqnp : ¬ q ∣ p := by
    intro hqd
    rcases hp.2 q hqd with h1 | hpp
    · have hq2 : 2 ≤ q := hq.two_le
      rw [h1] at hq2; exact absurd hq2 (by decide)
    · exact hpq hpp
  have hvqp : vp q p = 0 := vp_eq_zero_of_not_dvd hq hppos hqnp
  rw [hdiv, hc, vp_mul hq hppos hc_pos, hvqp, Nat.zero_add]

/-! ## §3 — the separation theorem -/

/-- ★★★ **`vp`-separation / faithfulness of the prime-exponent coordinate.**
    If `vp p m = vp p n` for every prime `p`, then `m = n` (for `m, n > 0`).
    Unique factorization, stated as the injectivity of the `vp`-coordinate.

    Strong induction on `m + n`.  Base cases `m = 1` / `n = 1`: a value `≥ 2`
    has a prime factor (`exists_prime_factor`) of positive valuation, while
    `1` has every valuation `0` — contradiction unless both are `1`.  Step:
    a prime `p ∣ m` has `vp p m ≥ 1 = vp p n`, so `p ∣ n`; dividing both by
    `p` (`vp_div_prime` drops `p`'s exponent by `1`, `vp_div_prime_other`
    keeps the rest) preserves the hypothesis at a strictly smaller sum, so the
    IH gives `m/p = n/p`, whence `m = n`. -/
theorem vp_separation {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : ∀ p, IsPrime213 p → vp p m = vp p n) : m = n := by
  suffices H : ∀ s, ∀ m n : Nat, m + n ≤ s → 0 < m → 0 < n →
      (∀ p, IsPrime213 p → vp p m = vp p n) → m = n by
    exact H (m + n) m n (Nat.le_refl _) hm hn h
  intro s
  induction s with
  | zero =>
    intro m n hle hm hn _
    exact absurd (Nat.le_trans (Nat.add_le_add hm hn) hle) (by decide)
  | succ s ih =>
    intro m n hle hm hn hvp
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- m = 1
      have hm1 : m = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hm2) hm
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hn2) hn
        rw [hm1, hn1]
      · exfalso
        obtain ⟨q, hq, hqn⟩ := exists_prime_factor n n (Nat.le_refl n) hn2
        have hqvn : 1 ≤ vp q n := (dvd_iff_one_le_vp hq hn).mp hqn
        have hqvm : vp q m = 0 := by
          rw [hm1]
          refine vp_eq_zero_of_not_dvd hq (by decide) ?_
          intro hd
          have hle1 := le_of_dvd_pos q 1 (by decide) hd
          exact absurd (Nat.le_trans hq.two_le hle1) (by decide)
        rw [← hvp q hq, hqvm] at hqvn
        exact absurd hqvn (by decide)
    · -- m ≥ 2: pick a prime p ∣ m
      obtain ⟨p, hp, hpm⟩ := exists_prime_factor m m (Nat.le_refl m) hm2
      have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
      have hpvm : 1 ≤ vp p m := (dvd_iff_one_le_vp hp hm).mp hpm
      have hpvn : 1 ≤ vp p n := by rw [← hvp p hp]; exact hpvm
      have hpn : p ∣ n := (dvd_iff_one_le_vp hp hn).mpr hpvn
      obtain ⟨cm, hcm⟩ := hpm
      obtain ⟨cn, hcn⟩ := hpn
      have hmdiv : m / p = cm := by rw [hcm]; exact mul_div_cancel_left_pure p cm hppos
      have hndiv : n / p = cn := by rw [hcn]; exact mul_div_cancel_left_pure p cn hppos
      have hcm_pos : 0 < cm := by
        rcases Nat.eq_zero_or_pos cm with h0 | hposc
        · exfalso; rw [h0, Nat.mul_zero] at hcm; rw [hcm] at hm; exact Nat.lt_irrefl 0 hm
        · exact hposc
      have hcn_pos : 0 < cn := by
        rcases Nat.eq_zero_or_pos cn with h0 | hposc
        · exfalso; rw [h0, Nat.mul_zero] at hcn; rw [hcn] at hn; exact Nat.lt_irrefl 0 hn
        · exact hposc
      have hvp' : ∀ q, IsPrime213 q → vp q (m / p) = vp q (n / p) := by
        intro q hq
        by_cases hqp : q = p
        · subst hqp
          have em : vp q (m / q) + 1 = vp q m := vp_div_prime hq hm ⟨cm, hcm⟩
          have en : vp q (n / q) + 1 = vp q n := vp_div_prime hq hn ⟨cn, hcn⟩
          have hcancel : vp q (m / q) + 1 = vp q (n / q) + 1 := by
            rw [em, en]; exact hvp q hq
          exact add_right_cancel_pure hcancel
        · have em : vp q (m / p) = vp q m := vp_div_prime_other hp hq hqp hm ⟨cm, hcm⟩
          have en : vp q (n / p) = vp q n := vp_div_prime_other hp hq hqp hn ⟨cn, hcn⟩
          rw [em, en]; exact hvp q hq
      have hsum_lt : cm + cn < m + n := by
        rw [hcm, hcn]
        have h1 : cm < p * cm := by
          have hp2cm : 2 * cm ≤ p * cm := Nat.mul_le_mul_right cm hp.two_le
          have hlt2 : cm < 2 * cm := by
            rw [Nat.two_mul]; exact Nat.lt_add_of_pos_left hcm_pos
          exact Nat.lt_of_lt_of_le hlt2 hp2cm
        have h2 : cn ≤ p * cn := by
          calc cn = 1 * cn := (Nat.one_mul cn).symm
            _ ≤ p * cn := Nat.mul_le_mul_right cn (Nat.le_trans (by decide) hp.two_le)
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le h1 h2) (Nat.le_refl _)
      have hcle : cm + cn ≤ s := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hsum_lt hle)
      have hceq : cm = cn :=
        ih cm cn hcle hcm_pos hcn_pos (by rw [← hmdiv, ← hndiv]; exact hvp')
      rw [hcm, hcn, hceq]

/-- **Divisibility from valuations** (the order companion of `vp_separation`):
    for `a, b > 0`, if `vp q a ≤ vp q b` at every prime `q` then `a ∣ b`.  Same
    peel-a-prime strong induction on `a`. -/
theorem dvd_of_forall_vp_le {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ p, IsPrime213 p → vp p a ≤ vp p b) : a ∣ b := by
  suffices H : ∀ s, ∀ a b : Nat, a ≤ s → 0 < a → 0 < b →
      (∀ p, IsPrime213 p → vp p a ≤ vp p b) → a ∣ b by
    exact H a a b (Nat.le_refl _) ha hb h
  intro s
  induction s with
  | zero =>
      intro a b hle ha _ _
      exact absurd (Nat.lt_of_lt_of_le ha hle) (Nat.lt_irrefl 0)
  | succ s ih =>
      intro a b hle ha hb hvp
      rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · have ha1 : a = 1 := Nat.le_antisymm (Nat.le_of_lt_succ ha2) ha
        rw [ha1]; exact ⟨b, (Nat.one_mul b).symm⟩
      · obtain ⟨p, hp, hpa⟩ := exists_prime_factor a a (Nat.le_refl a) ha2
        have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
        have hpva : 1 ≤ vp p a := (dvd_iff_one_le_vp hp ha).mp hpa
        have hpb : p ∣ b := (dvd_iff_one_le_vp hp hb).mpr (Nat.le_trans hpva (hvp p hp))
        obtain ⟨ca, hca⟩ := hpa
        obtain ⟨cb, hcb⟩ := hpb
        have hadiv : a / p = ca := by rw [hca]; exact mul_div_cancel_left_pure p ca hppos
        have hbdiv : b / p = cb := by rw [hcb]; exact mul_div_cancel_left_pure p cb hppos
        have hca_pos : 0 < ca := by
          rcases Nat.eq_zero_or_pos ca with h0 | hpos
          · exfalso; rw [h0, Nat.mul_zero] at hca; rw [hca] at ha; exact Nat.lt_irrefl 0 ha
          · exact hpos
        have hcb_pos : 0 < cb := by
          rcases Nat.eq_zero_or_pos cb with h0 | hpos
          · exfalso; rw [h0, Nat.mul_zero] at hcb; rw [hcb] at hb; exact Nat.lt_irrefl 0 hb
          · exact hpos
        have hvp' : ∀ q, IsPrime213 q → vp q ca ≤ vp q cb := by
          intro q hq
          by_cases hqp : q = p
          · subst hqp
            have ea : vp q (a / q) + 1 = vp q a := vp_div_prime hq ha ⟨ca, hca⟩
            have eb : vp q (b / q) + 1 = vp q b := vp_div_prime hq hb ⟨cb, hcb⟩
            rw [hadiv] at ea; rw [hbdiv] at eb
            have hsucc : vp q ca + 1 ≤ vp q cb + 1 := by rw [ea, eb]; exact hvp q hq
            exact Nat.le_of_succ_le_succ hsucc
          · have ea : vp q (a / p) = vp q a := vp_div_prime_other hp hq hqp ha ⟨ca, hca⟩
            have eb : vp q (b / p) = vp q b := vp_div_prime_other hp hq hqp hb ⟨cb, hcb⟩
            rw [hadiv] at ea; rw [hbdiv] at eb
            rw [ea, eb]; exact hvp q hq
        have hca_lt : ca < a := by
          rw [hca]
          have hp2 : 2 * ca ≤ p * ca := Nat.mul_le_mul_right ca hp.two_le
          have hlt2 : ca < 2 * ca := by rw [Nat.two_mul]; exact Nat.lt_add_of_pos_left hca_pos
          exact Nat.lt_of_lt_of_le hlt2 hp2
        have hcle : ca ≤ s := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hca_lt hle)
        obtain ⟨d, hd⟩ := ih ca cb hcle hca_pos hcb_pos hvp'
        refine ⟨d, ?_⟩
        rw [hca, hcb, hd]
        exact (E213.Tactic.NatHelper.mul_assoc p ca d).symm

end E213.Meta.Nat.VpSeparation
