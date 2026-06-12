import E213.Meta.Nat.Valuation
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.PureNat

/-!
# VpMul — the exponent-lattice engine over `Valuation` (frontier T3), ∅-axiom

`Valuation.lean` builds the `q`-adic valuation `vp q n` (largest `k` with `qᵏ ∣ n`)
PURE.  This file turns the slogan **"ℚ₊ = the exponent lattice"** into mathematics:
for a prime `p`, `vp p (·)` is a *monoid homomorphism* `(ℕ₊, ×) → (ℕ, +)` —

  * ★★ `vp_mul` — `vp p (m·n) = vp p m + vp p n` (the headline: the valuation is
    additive over multiplication, the structural core of the prime-exponent lattice).
  * `vp_pow` — `vp p (aᵏ) = k · vp p a` (iterating `vp_mul`).
  * `vp_self_pow` — `vp p (pᵏ) = k` (the lattice axis at `p` reads its own exponent).

## Primality hypothesis

The `≥` direction of `vp_mul` is pure combinatorics on divisibility; the `≤`
direction needs **Euclid's lemma** (`p ∣ a·b → p ∣ a ∨ p ∣ b`).  The repo's
`Gcd213.coprime_dvd_of_dvd_mul` is a Bezout-free Euclid's lemma keyed on
coprimality, so we package primality as the *minimal-divisor* predicate

  `IsPrime213 p  :=  2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`

— honest, general (no concrete-prime instantiation), and exactly what is needed:
`p ∤ a` forces `gcd213 p a = 1` (the gcd divides `p`, hence is `1` or `p`; if `p`,
then `p ∣ a`, contradiction), so `coprime_dvd_of_dvd_mul` fires.  `euclid_lemma`
below is the derived Euclid's lemma; everything downstream uses it.

All ∅-axiom.  Built only on `Valuation`, `Gcd213`, `PureNat`.
-/

namespace E213.Meta.Nat.VpMul

open E213.Meta.Nat.Valuation
  (vp pow_vp_dvd vp_ge le_vp_iff vp_not_dvd_succ drefl dtrans pow_dvd_of_le)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_greatest coprime_dvd_of_dvd_mul)
open E213.Meta.Nat.Valuation (mod_zero_of_dvd)
open E213.Meta.Nat.PureNat (pow_add mul_assoc)

open E213.Tactic.NatHelper (gcd213)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)

/-! ## §0 — primality and Euclid's lemma -/

/-- Minimal-divisor primality, 213-native: `p ≥ 2` and every divisor of `p`
    is `1` or `p`.  The form Euclid's lemma needs given the repo's
    coprimality-keyed `coprime_dvd_of_dvd_mul`. -/
def IsPrime213 (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem IsPrime213.two_le {p : Nat} (hp : IsPrime213 p) : 2 ≤ p := hp.1

/-- For a prime `p`, `p ∤ a` makes `p` coprime to `a`: `gcd213 p a = 1`. -/
theorem coprime_of_not_dvd {p a : Nat} (hp : IsPrime213 p) (h : ¬ p ∣ a) :
    gcd213 p a = 1 := by
  have hdvd : gcd213 p a ∣ p := gcd213_dvd_left p a
  rcases hp.2 (gcd213 p a) hdvd with h1 | hp'
  · exact h1
  · exfalso
    -- gcd213 p a = p, and gcd213 p a ∣ a, so p ∣ a
    have hda : gcd213 p a ∣ a := E213.Meta.Nat.Gcd213.gcd213_dvd_right p a
    rw [hp'] at hda
    exact h hda

/-- ★ **Euclid's lemma**: `p` prime, `p ∣ a·b ⟹ p ∣ a ∨ p ∣ b`.
    Derived from `coprime_dvd_of_dvd_mul` (Bezout-free) + minimal-divisor
    primality.  Either `p ∣ a`, or `p` is coprime to `a` and so divides `b`. -/
theorem euclid_lemma {p a b : Nat} (hp : IsPrime213 p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  -- decide on `a % p = 0` (structural `decEq`, PURE — avoids the
  -- propext-carrying `Decidable (p ∣ a)` instance).
  by_cases ha : a % p = 0
  · exact Or.inl (dvd_of_mod_eq_zero ha)
  · refine Or.inr ?_
    have hnd : ¬ p ∣ a := fun hd => ha (mod_zero_of_dvd hppos hd)
    have hco : gcd213 p a = 1 := coprime_of_not_dvd hp hnd
    exact coprime_dvd_of_dvd_mul hco h

/-! ## §1 — divisibility arithmetic on prime powers -/

/-- `p^(k+1) = p^k * p`. -/
theorem pow_succ' (p k : Nat) : p ^ (k + 1) = p ^ k * p := Nat.pow_succ p k

/-- Cancel a positive common left factor inside divisibility:
    `0 < c → c * x ∣ c * y → x ∣ y`. -/
theorem dvd_cancel_mul_left {c x y : Nat} (hc : 0 < c) (h : c * x ∣ c * y) :
    x ∣ y := by
  obtain ⟨t, ht⟩ := h
  -- c * y = (c * x) * t = c * (x * t)
  have ht' : c * y = c * (x * t) := by rw [ht, mul_assoc]
  exact ⟨t, Nat.eq_of_mul_eq_mul_left hc ht'⟩

/-! ## §2 — the peeling lemma: split a prime power across a product -/

/-- ★★ **Peeling**: for prime `p` and `m, n > 0`, every power `p^k` dividing
    `m·n` splits as `p^i ∣ m`, `p^j ∣ n` with `i + j = k`.  Induction on `k`,
    each step using Euclid's lemma + left-cancellation of `p^k`. -/
theorem pow_dvd_mul_split {p : Nat} (hp : IsPrime213 p) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    ∀ k, p ^ k ∣ m * n → ∃ i j, i + j = k ∧ p ^ i ∣ m ∧ p ^ j ∣ n
  | 0,     _ => ⟨0, 0, rfl, ⟨m, (Nat.one_mul m).symm⟩, ⟨n, (Nat.one_mul n).symm⟩⟩
  | k + 1, hk => by
    have hp2 : 2 ≤ p := hp.two_le
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
    -- IH on p^k (since p^k ∣ p^(k+1))
    have hk' : p ^ k ∣ m * n := dtrans (pow_dvd_of_le p (Nat.le_succ k)) hk
    obtain ⟨i, j, hij, hi, hj⟩ := pow_dvd_mul_split hp hm hn k hk'
    obtain ⟨m', hm'⟩ : ∃ m', m = p ^ i * m' := hi  -- m = p^i * m'
    obtain ⟨n', hn'⟩ : ∃ n', n = p ^ j * n' := hj  -- n = p^j * n'
    -- m * n = p^k * (m' * n')
    have hmn : m * n = p ^ k * (m' * n') := by
      calc m * n = (p ^ i * m') * (p ^ j * n') := by rw [hm', hn']
        _ = (p ^ i * p ^ j) * (m' * n') := by
              rw [mul_assoc (p ^ i) m', mul_assoc, ← mul_assoc m' (p ^ j) n',
                  Nat.mul_comm m' (p ^ j), mul_assoc (p ^ j) m' n',
                  ← mul_assoc (p ^ i) (p ^ j) (m' * n')]
        _ = p ^ (i + j) * (m' * n') := by rw [pow_add]
        _ = p ^ k * (m' * n') := by rw [hij]
    -- p^(k+1) = p^k * p ∣ p^k * (m'*n')  ⟹  p ∣ m'*n'
    have hpk_pos : 0 < p ^ k := Nat.pos_pow_of_pos k hppos
    have hk2 : p ^ k * p ∣ m * n := by rw [← pow_succ' p k]; exact hk
    have hdvd_pk : p ^ k * p ∣ p ^ k * (m' * n') := by rw [← hmn]; exact hk2
    have hp_mn : p ∣ m' * n' := dvd_cancel_mul_left hpk_pos hdvd_pk
    rcases euclid_lemma hp hp_mn with hpm | hpn
    · -- p ∣ m', so p^(i+1) ∣ m, use (i+1, j)
      obtain ⟨m'', hm''⟩ := hpm
      refine ⟨i + 1, j, by rw [Nat.add_right_comm, hij], ?_, ⟨n', hn'⟩⟩
      exact ⟨m'', by rw [hm', hm'', pow_succ', mul_assoc]⟩
    · -- p ∣ n', so p^(j+1) ∣ n, use (i, j+1)
      obtain ⟨n'', hn''⟩ := hpn
      refine ⟨i, j + 1, by rw [← Nat.add_assoc, hij], ⟨m', hm'⟩, ?_⟩
      exact ⟨n'', by rw [hn', hn'', pow_succ', mul_assoc]⟩

/-! ## §3 — the exponent-lattice homomorphism -/

/-- `≥` direction (pure, no primality): `vp p m + vp p n ≤ vp p (m·n)`.
    From `p^(vp m) ∣ m`, `p^(vp n) ∣ n` we get `p^(vp m + vp n) ∣ m·n`. -/
theorem le_vp_mul (p m n : Nat) (hp : 2 ≤ p) (hm : 0 < m) (hn : 0 < n) :
    vp p m + vp p n ≤ vp p (m * n) := by
  have hdm : p ^ (vp p m) ∣ m := pow_vp_dvd p m
  have hdn : p ^ (vp p n) ∣ n := pow_vp_dvd p n
  obtain ⟨a, ha⟩ := hdm
  obtain ⟨b, hb⟩ := hdn
  have hdvd : p ^ (vp p m + vp p n) ∣ m * n := by
    refine ⟨a * b, ?_⟩
    calc m * n = (p ^ vp p m * a) * (p ^ vp p n * b) := by rw [← ha, ← hb]
      _ = (p ^ vp p m * p ^ vp p n) * (a * b) := by
            rw [mul_assoc (p ^ vp p m) a, mul_assoc, ← mul_assoc a (p ^ vp p n) b,
                Nat.mul_comm a (p ^ vp p n), mul_assoc (p ^ vp p n) a b,
                ← mul_assoc (p ^ vp p m) (p ^ vp p n) (a * b)]
      _ = p ^ (vp p m + vp p n) * (a * b) := by rw [pow_add]
  have hmn_pos : 0 < m * n := Nat.mul_pos hm hn
  exact (le_vp_iff p (m * n) (vp p m + vp p n) hp hmn_pos).mp hdvd

/-- ★★ **`vp` is additive over `×`** — the exponent-lattice homomorphism:
    for prime `p`, `vp p (m·n) = vp p m + vp p n`.

    `≥` is `le_vp_mul`.  `≤`: `p^(vp(mn)) ∣ m·n` peels (Euclid) into
    `p^i ∣ m`, `p^j ∣ n` with `i + j = vp(mn)`; exactness `vp_not_dvd_succ`
    bounds `i ≤ vp m`, `j ≤ vp n`, so `vp(mn) = i + j ≤ vp m + vp n`. -/
theorem vp_mul {p : Nat} (hp : IsPrime213 p) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    vp p (m * n) = vp p m + vp p n := by
  have hp2 : 2 ≤ p := hp.two_le
  apply Nat.le_antisymm
  · -- ≤ : peel p^(vp(mn))
    have hdvd : p ^ (vp p (m * n)) ∣ m * n := pow_vp_dvd p (m * n)
    obtain ⟨i, j, hij, hi, hj⟩ := pow_dvd_mul_split hp hm hn (vp p (m * n)) hdvd
    -- i ≤ vp m, j ≤ vp n directly from `le_vp_iff`
    have hi_le : i ≤ vp p m := (le_vp_iff p m i hp2 hm).mp hi
    have hj_le : j ≤ vp p n := (le_vp_iff p n j hp2 hn).mp hj
    calc vp p (m * n) = i + j := hij.symm
      _ ≤ vp p m + vp p n := Nat.add_le_add hi_le hj_le
  · exact le_vp_mul p m n hp2 hm hn

/-! ## §4 — corollaries: powers along the lattice axis -/

/-- `vp p (aᵏ) = k · vp p a` for prime `p`, `a > 0`.  Iterate `vp_mul`. -/
theorem vp_pow {p : Nat} (hp : IsPrime213 p) {a : Nat} (ha : 0 < a) :
    ∀ k, vp p (a ^ k) = k * vp p a
  | 0     => by
      show vp p (a ^ 0) = 0 * vp p a
      rw [Nat.pow_zero, Nat.zero_mul]
      -- vp p 1 = 0 : p^1 = p > 1 does not divide 1, so only k=0 works
      apply Nat.le_antisymm _ (Nat.zero_le _)
      rcases Nat.lt_or_ge (vp p 1) 1 with hlt | hge
      · exact Nat.le_of_lt_succ hlt
      · exfalso
        have hdvd : p ^ 1 ∣ (1 : Nat) := dtrans (pow_dvd_of_le p hge) (pow_vp_dvd p 1)
        rw [Nat.pow_one] at hdvd
        have hple : p ≤ 1 := le_of_dvd_pos p 1 (by decide) hdvd
        exact absurd (Nat.le_trans hp.two_le hple) (by decide)
  | k + 1 => by
      have hak : 0 < a ^ k := Nat.pos_pow_of_pos k ha
      show vp p (a ^ (k + 1)) = (k + 1) * vp p a
      rw [pow_succ', vp_mul hp hak ha, vp_pow hp ha k, Nat.succ_mul]

/-- `vp p (pᵏ) = k` for prime `p`: the lattice axis at `p` reads its own
    exponent.  Specialises `vp_pow` with `vp p p = 1`. -/
theorem vp_self_pow {p : Nat} (hp : IsPrime213 p) (k : Nat) :
    vp p (p ^ k) = k := by
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  -- vp p p = 1
  have hvp_p : vp p p = 1 := by
    apply Nat.le_antisymm
    · -- p^(vp p p) ∣ p and p^2 > p, so vp p p ≤ 1
      rcases Nat.lt_or_ge (vp p p) 2 with hlt | h2
      · exact Nat.le_of_lt_succ hlt
      exfalso
      have hdvd : p ^ 2 ∣ p := dtrans (pow_dvd_of_le p h2) (pow_vp_dvd p p)
      have hple : p ^ 2 ≤ p := le_of_dvd_pos (p ^ 2) p hppos hdvd
      -- p^2 = p * p ≥ 2 * p > p, contradiction
      have hpp : p * p ≤ p := by
        have : p ^ 2 = p * p := by rw [pow_succ', Nat.pow_one]
        rwa [this] at hple
      have h2p : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
      have hcontra : 2 * p ≤ p := Nat.le_trans h2p hpp
      have hp_lt : p < 2 * p := by
        rw [Nat.two_mul]; exact Nat.lt_add_of_pos_left hppos
      exact Nat.lt_irrefl p (Nat.lt_of_lt_of_le hp_lt hcontra)
    · -- 1 ≤ vp p p : p^1 = p ∣ p
      exact (le_vp_iff p p 1 hp2 hppos).mp (by rw [Nat.pow_one]; exact drefl p)
  rw [vp_pow hp hppos k, hvp_p, Nat.mul_one]

end E213.Meta.Nat.VpMul
