import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFreshman
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Meta.Int213.PolyIntMTactic

/-!
# Fermat's little theorem in `ℤ` — `q ∣ (a^q − a)` for a prime `q`, all `a : Int` (∅-axiom)

★★★★ `int_fermat` : `(↑q) ∣ (a^q − a)` for every integer `a` and prime `q`.

Built **without** `Int.induction_on` (no Mathlib) and **without** `Int` modular arithmetic — both via the
binary freshman's dream `add_pow_modEq_prime` routed through `ofInt : ℤ → ℤ[ω]`:

- `int_freshman` : `(↑q) ∣ ((A+B)^q − (A^q + B^q))` (the ℤ shadow of the ℤ[ω] freshman, reflected back by
  `ofIntDvd_reflect : ofInt a ∣ ofInt b → a ∣ b`).
- `pos_fermat` : `q ∣ ((↑n)^q − ↑n)` for `n : ℕ` by induction on `n` (step: freshman at `B = 1`).
- the negative branch needs **no parity case**: `(−A)^q ≡ −A^q (mod q)` comes from the freshman at
  `A + (−A) = 0` (`neg_pow_modEq`), so `int_fermat` closes on the two `Int` constructors
  (`ofNat` / `negSucc`).

The `ℤ[ω]` lift `ofInt_fermat` (`(ofInt a)^q ≡ ofInt a (mod q)`) is the Fermat half of the Frobenius
`conj z ≡ z^q (mod q)` on `ℤ[ω]/(q) ≅ 𝔽_{q²}` — the central brick of the cubic-reciprocity finish.
∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFreshman (add_pow_modEq_prime ofInt_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (ofInt_pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (ofInt_add ofInt_neg)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Meta.Int213

/-- `0^q = 0` for a prime `q` (`q ≥ 1`). -/
private theorem zero_pow_pos {q : Nat} (hq : 1 < q) : (0 : Int) ^ q = 0 := by
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.not_eq_zero_of_lt hq)
  rw [Int.pow_succ, Int.mul_zero]

/-- `1^q = 1` in `ℤ`. -/
private theorem int_one_pow : ∀ q : Nat, (1 : Int) ^ q = 1
  | 0 => rfl
  | q + 1 => by rw [Int.pow_succ, int_one_pow q, Int.one_mul]

/-! PURE `ℤ`-divisibility helpers (the Lean-core `Int.dvd_*` leak `propext`; these route the witness
arithmetic through the PURE `ring_intZ`). -/

private theorem dvd_add_p {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := by
  obtain ⟨k1, rfl⟩ := h1; obtain ⟨k2, rfl⟩ := h2; exact ⟨k1 + k2, by ring_intZ⟩

private theorem dvd_sub_p {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b - c) := by
  obtain ⟨k1, rfl⟩ := h1; obtain ⟨k2, rfl⟩ := h2; exact ⟨k1 - k2, by ring_intZ⟩

private theorem dvd_of_dvd_neg_p {a b : Int} (h : a ∣ -b) : a ∣ b := by
  obtain ⟨k, hk⟩ := h; exact ⟨-k, by rw [← Int.neg_neg b, hk]; ring_intZ⟩

/-- ★★★ **`ofInt` reflects divisibility** — `ofInt a ∣ ofInt b ⟹ a ∣ b`.  From `ofInt a · z =
    ⟨a·z.re, a·z.im⟩` (the `im = 0` factor), the real part gives `b = a·z.re`.  The inverse of
    `ofInt_dvd`.  ∅-axiom. -/
theorem ofIntDvd_reflect {a b : Int} (h : ofInt a ∣ ofInt b) : a ∣ b := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z.re, ?_⟩
  have h2 : (ofInt a * z).re = a * z.re := by
    show a * z.re - 0 * z.im = a * z.re
    rw [zero_mul, Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  have hb : (ofInt b).re = b := rfl
  rw [← hb, hz, h2]

/-- ★★★★ **The freshman's dream in `ℤ`** — `(↑q) ∣ ((A+B)^q − (A^q + B^q))` for a prime `q`.  The ℤ
    shadow of `add_pow_modEq_prime` (in `ℤ[ω]`), pulled back along `ofInt` by `ofIntDvd_reflect`.
    ∅-axiom. -/
theorem int_freshman {q : Nat} (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q) (A B : Int) :
    (↑q : Int) ∣ ((A + B) ^ q - (A ^ q + B ^ q)) := by
  apply ofIntDvd_reflect
  have hf := add_pow_modEq_prime (ofInt A) (ofInt B) q hq hqr
  rw [ofInt_add A B, ofInt_pow (A + B) q, ofInt_pow A q, ofInt_pow B q,
      ofInt_add (A ^ q) (B ^ q)] at hf
  show ofInt ((q : Nat) : Int) ∣ ofInt ((A + B) ^ q + -(A ^ q + B ^ q))
  rw [← ofInt_add ((A + B) ^ q) (-(A ^ q + B ^ q)), ofInt_neg (A ^ q + B ^ q)]
  exact hf

/-- ★★★ **Fermat on `ℕ`-cast** — `(↑q) ∣ ((↑n)^q − ↑n)` for `n : ℕ`.  Induction on `n`: the step uses
    `int_freshman` at `B = 1` (`(↑n+1)^q ≡ (↑n)^q + 1`).  ∅-axiom. -/
theorem pos_fermat {q : Nat} (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q) :
    ∀ n : Nat, (↑q : Int) ∣ ((↑n : Int) ^ q - ↑n)
  | 0 => by
      show (↑q : Int) ∣ ((0 : Int) ^ q - 0)
      rw [zero_pow_pos hq]; exact Int.dvd_zero _
  | n + 1 => by
      have ih := pos_fermat hq hqr n
      have hfr := int_freshman hq hqr (↑n) 1
      have hcomb := dvd_add_p hfr ih
      have heq : ((↑(n + 1) : Int)) ^ q - ↑(n + 1)
          = ((↑n + 1) ^ q - ((↑n) ^ q + (1 : Int) ^ q)) + ((↑n) ^ q - ↑n) := by
        rw [int_one_pow q, Int.ofNat_succ]; ring_intZ
      rw [heq]; exact hcomb

/-- ★★★ **The negation power congruence** — `(↑q) ∣ (A^q + (−A)^q)` for a prime `q`.  From `int_freshman`
    at `B = −A` (`A + (−A) = 0`, `0^q = 0`): `0 ≡ A^q + (−A)^q`, so the sum is `q`-divisible — no parity
    case.  ∅-axiom. -/
theorem neg_pow_modEq {q : Nat} (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q) (A : Int) :
    (↑q : Int) ∣ (A ^ q + (-A) ^ q) := by
  have hf := int_freshman hq hqr A (-A)
  have he : (A + -A) ^ q - (A ^ q + (-A) ^ q) = -(A ^ q + (-A) ^ q) := by
    rw [add_neg_cancel A, zero_pow_pos hq, Int.sub_eq_add_neg, zero_add]
  rw [he] at hf
  exact dvd_of_dvd_neg_p hf

/-- ★★★★ **Fermat's little theorem in `ℤ`** — `(↑q) ∣ (a^q − a)` for a prime `q` and every `a : Int`.
    `ofNat` branch is `pos_fermat`; `negSucc` branch (`a = −A`, `A = ↑(n+1)`) combines `pos_fermat` with
    `neg_pow_modEq` (`(−A)^q ≡ −A^q`) — no parity case.  ∅-axiom. -/
theorem int_fermat {q : Nat} (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q) :
    ∀ a : Int, (↑q : Int) ∣ (a ^ q - a)
  | Int.ofNat n => pos_fermat hq hqr n
  | Int.negSucc n => by
      have hpos := pos_fermat hq hqr (n + 1)
      have hneg := neg_pow_modEq hq hqr (↑(n + 1))
      have hcomb := dvd_sub_p hneg hpos
      have heq : (Int.negSucc n) ^ q - Int.negSucc n
          = (((↑(n + 1) : Int)) ^ q + (-(↑(n + 1) : Int)) ^ q) - ((↑(n + 1) : Int) ^ q - ↑(n + 1)) := by
        rw [Int.negSucc_eq, Int.ofNat_succ]; ring_intZ
      rw [heq]; exact hcomb

/-- ★★★★★ **Fermat's little theorem in `ℤ[ω]` on rational integers** — `(ofInt a)^q ≡ ofInt a (mod q)`
    for a prime `q`.  `ofInt_pow` turns the `ℤ[ω]` power into `ofInt (a^q)`; `int_fermat` supplies
    `q ∣ (a^q − a)`, lifted by `ofInt_dvd`.  The Fermat half of the Frobenius `conj z ≡ z^q (mod q)` on
    `ℤ[ω]/(q)`.  ∅-axiom. -/
theorem ofInt_fermat {q : Nat} (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q) (a : Int) :
    ModEq (ofInt ((q : Nat) : Int))
      (pow (ofInt a) q)
      (ofInt a) := by
  have hkey : pow (ofInt a) q + -(ofInt a) = ofInt (a ^ q + -a) := by
    rw [ofInt_pow a q, ← ofInt_neg a, ← ofInt_add (a ^ q) (-a)]
  show ofInt ((q : Nat) : Int) ∣ (pow (ofInt a) q + -(ofInt a))
  rw [hkey]
  exact ofInt_dvd (int_fermat hq hqr a)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat
