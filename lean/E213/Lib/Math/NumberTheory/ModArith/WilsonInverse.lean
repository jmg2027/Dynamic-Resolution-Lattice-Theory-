import E213.Meta.Nat.VpMul
import E213.Meta.Nat.AddMod213
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor

/-!
# Toward Wilson's theorem: self-inverse characterization + unique inverse (∅-axiom)

The two number-theoretic ingredients of Wilson's theorem, both genuinely absent
(only Frankl–Wilson combinatorics existed):

  ★ **W1 `self_inverse`** — for prime `p` and `0 < x < p`, `x² ≡ 1 (mod p)` ⟹
    `x = 1 ∨ x + 1 = p` (the only self-inverse elements of `(ℤ/p)ˣ` are `±1`).
    Proof: `p ∣ x²−1 = (x−1)(x+1)`, Euclid's lemma splits, range bounds pin `x`.
  * **W2** — every `x ∈ [1, p−1]` has a *unique* inverse in `[1, p−1]`
    (`inverse_exists` + `inverse_unique`, from the modular inverse + coprime
    cancellation).

These are exactly the lemmas the Wilson product-pairing fold consumes; the full
`(p−1)! ≡ −1 (mod p)` additionally needs "the inverse map is a permutation of
`[1..p−1]`" (a length/NoDup bijection-to-permutation argument over the existing
`ProdLperm` toolkit), left open.  All declarations here ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.WilsonInverse

open E213.Meta.Nat.VpMul (IsPrime213 euclid_lemma)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (le_of_dvd_loc)

/-! ## W1 — self-inverse characterization -/

/-- **W1 (factored form).**  `p` prime, `x = y+1 < p`, `p ∣ (x−1)(x+1) = y·(y+2)`
    ⟹ `x = 1 ∨ x + 1 = p` (written subtraction-free as `y+1=1 ∨ y+1+1=p`). -/
theorem self_inverse_factored {p y : Nat} (hp : IsPrime213 p)
    (hlt : y + 1 < p) (h : p ∣ y * (y + 2)) :
    y + 1 = 1 ∨ y + 1 + 1 = p := by
  rcases euclid_lemma hp h with hdy | hdy2
  · left
    rcases Nat.eq_zero_or_pos y with hy0 | hypos
    · rw [hy0]
    · exfalso
      have hyltp : y < p := Nat.lt_of_succ_lt hlt
      have hpley : p ≤ y := le_of_dvd_loc hypos hdy
      exact Nat.lt_irrefl p (Nat.lt_of_le_of_lt hpley hyltp)
  · right
    have hpos2 : 0 < y + 2 := Nat.succ_pos (y + 1)
    have hle : p ≤ y + 2 := le_of_dvd_loc hpos2 hdy2
    have hle2 : y + 2 ≤ p := Nat.succ_le_of_lt hlt
    have hrw : y + 1 + 1 = y + 2 := rfl
    rw [hrw]
    exact Nat.le_antisymm hle2 hle

/-- ★ **W1 — self-inverse characterization.**  `p` prime, `0 < x < p`,
    `x·x ≡ 1 (mod p)` ⟹ `x = 1 ∨ x + 1 = p` (the `Nat` form of `x = 1 ∨ x = p−1`). -/
theorem self_inverse {p x : Nat} (hp : IsPrime213 p)
    (hx0 : 0 < x) (hxlt : x < p) (hself : (x * x) % p = 1 % p) :
    x = 1 ∨ x + 1 = p := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, (Nat.succ_pred_eq_of_pos hx0).symm⟩
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have h1mod : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt hp1
  have hxx : ((y + 1) * (y + 1)) % p = 1 % p := hself
  have hid : (y + 1) * (y + 1) = y * (y + 2) + 1 := by ring_nat
  rw [hid, h1mod] at hxx
  have hdvd : p ∣ (y * (y + 2)) := by
    have hmod0 : (y * (y + 2)) % p = 0 := by
      have key := E213.Meta.Nat.AddMod213.add_mod_gen (y * (y + 2)) 1 p
      rw [hxx, h1mod] at key
      have hrlt : (y * (y + 2)) % p < p :=
        Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide) hp.two_le)
      rcases Nat.eq_zero_or_pos ((y * (y + 2)) % p) with h0 | hpos
      · exact h0
      · exfalso
        rcases Nat.lt_or_ge ((y * (y + 2)) % p + 1) p with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at key
          have : (y * (y + 2)) % p = 0 :=
            (E213.Tactic.NatHelper.add_right_cancel_pure
              (show (y*(y+2))%p + 1 = 0 + 1 from key.symm.trans (Nat.zero_add 1).symm))
          exact Nat.lt_irrefl 0 (this ▸ hpos)
        · have heqp : (y * (y + 2)) % p + 1 = p :=
            Nat.le_antisymm (Nat.succ_le_of_lt hrlt) hge
          rw [heqp, E213.Meta.Nat.AddMod213.mod_self] at key
          exact absurd key.symm (by decide)
    exact E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hmod0
  rcases self_inverse_factored hp hxlt hdvd with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [show y + 1 + 1 = (y + 1) + 1 from rfl] at h; exact h)

/-! ## W2 — unique inverse in `[1, p−1]` -/

open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (inverse_of_coprime euclid_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.VpMul (coprime_of_not_dvd)

/-- For prime `p` and `0 < x < p`, `gcd213 x p = 1`. -/
theorem coprime_of_lt {p x : Nat} (hp : IsPrime213 p) (hx0 : 0 < x) (hxlt : x < p) :
    gcd213 x p = 1 := by
  have hnd : ¬ p ∣ x := fun hd => Nat.lt_irrefl p (Nat.lt_of_le_of_lt (le_of_dvd_loc hx0 hd) hxlt)
  rw [E213.Meta.Nat.Gcd213.gcd213_comm]
  exact coprime_of_not_dvd hp hnd

/-- **W2 existence** — a reduced inverse in `[1, p−1]`: for prime `p`, `0 < x < p`,
    there is `b` with `0 < b < p` and `(x·b) % p = 1`. -/
theorem inverse_exists {p x : Nat} (hp : IsPrime213 p) (hx0 : 0 < x) (hxlt : x < p) :
    ∃ b, 0 < b ∧ b < p ∧ (x * b) % p = 1 := by
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hco : gcd213 x p = 1 := coprime_of_lt hp hx0 hxlt
  have hraw : (x * (modBezout x p).2) % p = 1 % p := inverse_of_coprime x p hppos hco
  have h1mod : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt hp1
  rw [h1mod] at hraw
  refine ⟨(modBezout x p).2 % p, ?_, Nat.mod_lt _ hppos, ?_⟩
  · rcases Nat.eq_zero_or_pos ((modBezout x p).2 % p) with h0 | hpos
    · exfalso
      have hred : (x * (modBezout x p).2) % p = (x * ((modBezout x p).2 % p)) % p := by
        rw [mul_mod_pure x (modBezout x p).2 p, mul_mod_pure x ((modBezout x p).2 % p) p,
            E213.Meta.Nat.AddMod213.mod_mod]
      rw [hred, h0, Nat.mul_zero, Nat.mod_eq_of_lt hppos] at hraw
      exact absurd hraw (by decide)
    · exact hpos
  · rw [mul_mod_pure x ((modBezout x p).2 % p) p, E213.Meta.Nat.AddMod213.mod_mod,
        ← mul_mod_pure x (modBezout x p).2 p]
    exact hraw

/-- **W2 uniqueness** — the inverse in `[1, p−1]` is unique: any `a, b < p` with
    `(x·a)%p = 1` and `(x·b)%p = 1` are equal (coprime cancellation). -/
theorem inverse_unique {p x a b : Nat} (hp : IsPrime213 p)
    (hx0 : 0 < x) (hxlt : x < p) (ha : a < p) (hb : b < p)
    (hia : (x * a) % p = 1) (hib : (x * b) % p = 1) :
    a = b := by
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hco : gcd213 x p = 1 := coprime_of_lt hp hx0 hxlt
  have core : ∀ u v : Nat, v ≤ u → u < p → (x * u) % p = 1 → (x * v) % p = 1 → u = v := by
    intro u v hvu hup hiu hiv
    have hmodeq : (x * v) % p = (x * u) % p := hiv.trans hiu.symm
    have hle : x * v ≤ x * u := Nat.mul_le_mul_left x hvu
    have hz : (x * u - x * v) % p = 0 :=
      E213.Meta.Nat.AddMod213.mod_diff_eq_zero_of_le hppos hle hmodeq
    have hpdvd0 : p ∣ (x * u - x * v) := E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hz
    have hms : x * u - x * v = x * (u - v) := (E213.Tactic.NatHelper.mul_sub x u v).symm
    have hpdvd : p ∣ (x * (u - v)) := by rw [hms] at hpdvd0; exact hpdvd0
    have hpd : p ∣ (u - v) := euclid_of_coprime x (u - v) p hp1 hco hpdvd
    have huv_lt : u - v < p := Nat.lt_of_le_of_lt (Nat.sub_le u v) hup
    have huv0 : u - v = 0 := by
      rcases Nat.eq_zero_or_pos (u - v) with h0 | hpos
      · exact h0
      · exact absurd (le_of_dvd_loc hpos hpd) (Nat.not_le_of_lt huv_lt)
    exact (Nat.le_antisymm hvu (Nat.le_of_sub_eq_zero huv0)).symm
  rcases Nat.le_total b a with hba | hab
  · exact core a b hba ha hia hib
  · exact (core b a hab hb hib hia).symm

end E213.Lib.Math.NumberTheory.ModArith.WilsonInverse
