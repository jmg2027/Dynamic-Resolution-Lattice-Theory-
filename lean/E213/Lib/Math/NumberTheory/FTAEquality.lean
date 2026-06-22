import E213.Lib.Math.NumberTheory.FTAUniqueness
import E213.Lib.Math.NumberTheory.GaussTotient
import E213.Meta.Nat.PolyNatMTactic

/-!
# FTA equality — a positive number is determined by its prime valuations (∅-axiom)

The converse of `FTAUniqueness` (which reads the factorization *multiset* off `n` via `vp`):
**two positive numbers with equal `vp` at every prime are equal** (`eq_of_vp_eq`).  This is the
"number = its prime-valuation vector" half of FTA — the tool a product identity like
`N! = Π lcm(1..⌊N/i⌋)` needs (prove the valuations match, conclude the numbers match).

Route (no permutation/UFD machinery): `vp`-division is clean from `vp_mul`
(`vp_div_self`/`vp_div_other`), so `prodL L ∣ b` follows from `countOcc q L ≤ vp q b` by
induction (peel a prime, divide `b`); then equal valuations give `a ∣ b ∧ b ∣ a`, hence `a = b`.
-/

namespace E213.Lib.Math.NumberTheory.FTAEquality

open E213.Lib.Math.NumberTheory.FTAUniqueness (countOcc countOcc_cons vp_prime_single vp_prodL_eq_countOcc)
open E213.Lib.Math.NumberTheory.PrimeFactorization (prodL prodL_cons factorize factorize_prod factorize_all_prime)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul)
open E213.Meta.Nat.Valuation (vp pow_vp_dvd pow_dvd_of_le dtrans)
open E213.Lib.Math.NumberTheory.GaussTotient (mul_div_of_dvd)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §1 — `vp` under division by a prime factor -/

/-- The cofactor `b/p` is positive when `p ∣ b`, `0 < b`. -/
theorem div_pos_of_dvd {p b : Nat} (hpb : p ∣ b) (hb : 0 < b) : 0 < b / p := by
  rcases Nat.eq_zero_or_pos (b / p) with h0 | hpos
  · exfalso
    have hcof : p * (b / p) = b := mul_div_of_dvd hpb
    rw [h0, Nat.mul_zero] at hcof
    exact Nat.lt_irrefl 0 (hcof ▸ hb)
  · exact hpos

/-- ★★ **`vp` of the divided prime drops by one**: `vp p b = vp p (b/p) + 1`. -/
theorem vp_div_self {p b : Nat} (hp : IsPrime213 p) (hpb : p ∣ b) (hb : 0 < b) :
    vp p b = vp p (b / p) + 1 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hbp : 0 < b / p := div_pos_of_dvd hpb hb
  have hcof : p * (b / p) = b := mul_div_of_dvd hpb
  have hmul : vp p (p * (b / p)) = vp p p + vp p (b / p) := vp_mul hp hppos hbp
  have hpp : vp p p = 1 := by rw [vp_prime_single hp hp]; rw [if_pos rfl]
  rw [hcof] at hmul
  rw [hmul, hpp, Nat.add_comm]

/-- ★★ **`vp` of other primes is unchanged**: `vp q b = vp q (b/p)` for `q ≠ p`. -/
theorem vp_div_other {p q b : Nat} (hp : IsPrime213 p) (hq : IsPrime213 q)
    (hqp : q ≠ p) (hpb : p ∣ b) (hb : 0 < b) : vp q b = vp q (b / p) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hbp : 0 < b / p := div_pos_of_dvd hpb hb
  have hcof : p * (b / p) = b := mul_div_of_dvd hpb
  have hmul : vp q (p * (b / p)) = vp q p + vp q (b / p) := vp_mul hq hppos hbp
  have hqp0 : vp q p = 0 := by
    rw [vp_prime_single hq hp, if_neg (fun e => hqp e.symm)]
  rw [hcof] at hmul
  rw [hmul, hqp0, Nat.zero_add]

/-! ## §2 — divisibility from valuation domination -/

/-- If a prime list's occurrence counts are bounded by `b`'s valuations, the product divides
    `b`.  Induction: peel a prime `p` (`p ∣ b` since `vp p b ≥ 1`), divide `b` by `p`, the counts
    drop in step with the valuations (`vp_div_self`/`vp_div_other`). -/
theorem dvd_of_countOcc_le_vp :
    ∀ (L : List Nat), (∀ x, x ∈ L → IsPrime213 x) →
      ∀ (b : Nat), 0 < b → (∀ q, IsPrime213 q → countOcc q L ≤ vp q b) → prodL L ∣ b := by
  intro L
  induction L with
  | nil => intro _ b _ _; exact ⟨b, (Nat.one_mul b).symm⟩
  | cons p rest ih =>
      intro hall b hb hbound
      have hp : IsPrime213 p := hall p (List.Mem.head rest)
      have hrest : ∀ x, x ∈ rest → IsPrime213 x := fun x hx => hall x (List.Mem.tail p hx)
      have hcp : countOcc p (p :: rest) = 1 + countOcc p rest := by
        rw [countOcc_cons, if_pos rfl]
      have hvp1 : 1 ≤ vp p b :=
        Nat.le_trans (by rw [hcp]; exact Nat.le_add_right 1 (countOcc p rest)) (hbound p hp)
      have hpdvd : p ∣ b := by
        have h1 : p ^ 1 ∣ p ^ (vp p b) := pow_dvd_of_le p hvp1
        rw [Nat.pow_one] at h1
        exact dtrans h1 (pow_vp_dvd p b)
      have hbp : 0 < b / p := div_pos_of_dvd hpdvd hb
      have hcof : p * (b / p) = b := mul_div_of_dvd hpdvd
      have hbound' : ∀ q, IsPrime213 q → countOcc q rest ≤ vp q (b / p) := by
        intro q hq
        cases Nat.decEq q p with
        | isTrue hqp =>
            subst hqp
            have h1 : countOcc q rest + 1 ≤ vp q b := by
              have := hbound q hq
              rwa [hcp, Nat.add_comm 1 (countOcc q rest)] at this
            rw [vp_div_self hq hpdvd hb] at h1
            exact Nat.le_of_succ_le_succ h1
        | isFalse hqp =>
            have hco : countOcc q (p :: rest) = countOcc q rest := by
              rw [countOcc_cons, if_neg (fun e => hqp e.symm), Nat.zero_add]
            rw [← vp_div_other hp hq hqp hpdvd hb]
            rw [← hco]; exact hbound q hq
      have hrec : prodL rest ∣ b / p := ih hrest (b / p) hbp hbound'
      obtain ⟨k, hk⟩ := hrec
      refine ⟨k, ?_⟩
      -- b = p*(b/p) = p*(prodL rest * k) = (p * prodL rest)*k = prodL (p::rest) * k
      rw [prodL_cons, ← hcof, hk]
      ring_nat

/-! ## §3 — equality from equal valuations -/

/-- `a ∣ b` when every prime valuation of `a` is ≤ that of `b`. -/
theorem dvd_of_forall_vp_le {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ q, IsPrime213 q → vp q a ≤ vp q b) : a ∣ b := by
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · have hae : a = 1 := Nat.le_antisymm (Nat.le_of_lt_succ ha1) ha
    rw [hae]; exact ⟨b, (Nat.one_mul b).symm⟩
  · have hall : ∀ x, x ∈ factorize a → IsPrime213 x := factorize_all_prime a ha2
    have hprod : prodL (factorize a) = a := factorize_prod a ha
    have hbound : ∀ q, IsPrime213 q → countOcc q (factorize a) ≤ vp q b := by
      intro q hq
      have hco : countOcc q (factorize a) = vp q a := by
        rw [← vp_prodL_eq_countOcc hq (factorize a) hall, hprod]
      rw [hco]; exact h q hq
    have hdvd : prodL (factorize a) ∣ b := dvd_of_countOcc_le_vp (factorize a) hall b hb hbound
    rwa [hprod] at hdvd

/-- ★★★ **A positive number is determined by its prime valuations.**  If `vp q a = vp q b` for
    every prime `q`, then `a = b` (`a ∣ b` and `b ∣ a` by valuation domination, then `≤`
    antisymmetry).  The "number = its valuation vector" half of FTA — prove a product identity
    by matching prime exponents. -/
theorem eq_of_vp_eq {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ q, IsPrime213 q → vp q a = vp q b) : a = b := by
  have hab : a ∣ b := dvd_of_forall_vp_le ha hb (fun q hq => Nat.le_of_eq (h q hq))
  have hba : b ∣ a := dvd_of_forall_vp_le hb ha (fun q hq => Nat.le_of_eq (h q hq).symm)
  exact Nat.le_antisymm (le_of_dvd_pos a b hb hab) (le_of_dvd_pos b a ha hba)

end E213.Lib.Math.NumberTheory.FTAEquality
