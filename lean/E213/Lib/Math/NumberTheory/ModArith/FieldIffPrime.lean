import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.WilsonConverse
import E213.Lib.Math.NumberTheory.PerfectNumbers
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Gcd213

/-!
# `ℤ/n` is a field ⟺ `n` is prime — on representatives, no quotient ring

A vein-A ∅-axiom case: classically this is a statement about the **quotient ring** `ℤ/n`
(built via `Quot.sound`, the field structure obtained by lifting inverses through the quotient).
With no quotient available, the statement is about residues `{0,…,n−1}` under `%`-arithmetic:

* "`a` is invertible" = `hasInverse n a := ∃ b, (a * b) % n = 1 % n` — an explicit modular inverse.
* "`ℤ/n` is a field" = `isFieldZn n := 1 < n ∧ ∀ a, a % n ≠ 0 → hasInverse n a`.

**The forcing**: the field/non-field dichotomy *is the gcd computation* — invertibility is decided
by Bezout (`inverse_of_coprime`: `gcd a n = 1 ⟹ a` has a modular inverse), and the failure for a
composite `n` is exhibited by an **explicit zero divisor** read off the factorization `n = a·b`
(`(a·b) % n = n % n = 0`).  The quotient ring was packaging; the content is the Bezout/zero-divisor
split on representatives.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.FieldIffPrime

open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 prime_coprime_of_not_dvd)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (inverse_of_coprime le_of_dvd_loc)
open E213.Lib.Math.NumberTheory.ModArith.WilsonConverse (exists_nontrivial_factor factor_bounds)
open E213.Meta.Nat.AddMod213 (mod_self dvd_of_mod_eq_zero div_add_mod)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Meta.Nat.VpSeparation (searchDiv)
open E213.Tactic.NatHelper (gcd213)

/-! ## §1 — definitions (representative-level, no quotient) -/

/-- `a` has a modular inverse mod `n`: some residue `b` with `a·b ≡ 1 (mod n)`. -/
def hasInverse (n a : Nat) : Prop := ∃ b, (a * b) % n = 1 % n

/-- "`ℤ/n` is a field": `n > 1` and every nonzero residue is invertible. -/
def isFieldZn (n : Nat) : Prop := 1 < n ∧ ∀ a, a % n ≠ 0 → hasInverse n a

/-! ## §2 — prime ⟹ field (Bezout inverse) -/

/-- A nonzero residue mod a prime is not divisible by the prime: `a % p ≠ 0 ⟹ ¬ p ∣ a`. -/
theorem not_dvd_of_mod_ne_zero {p a : Nat} (h : a % p ≠ 0) : ¬ p ∣ a := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  exact h (by rw [hc]; exact E213.Tactic.NatHelper.mul_mod_right p c)

/-- ★★★ **prime ⟹ field.**  For a prime `n`, every nonzero residue `a` (`a % n ≠ 0`, so the prime
    `n` does not divide `a`, hence `gcd a n = 1`) has the explicit Bezout inverse from
    `inverse_of_coprime`.  Invertibility is *decided by the gcd computation*. -/
theorem prime_imp_field {n : Nat} (hp : Prime213 n) : isFieldZn n := by
  refine ⟨Nat.lt_of_lt_of_le (by decide) hp.1, ?_⟩
  intro a hmod
  have hndvd : ¬ n ∣ a := not_dvd_of_mod_ne_zero hmod
  have hco : gcd213 a n = 1 := (gcd213_comm a n).trans (prime_coprime_of_not_dvd hp hndvd)
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hp.1
  exact ⟨_, inverse_of_coprime a n hnpos hco⟩

/-! ## §3 — composite ⟹ NOT a field (explicit zero divisor) -/

/-- ★★★ **composite ⟹ explicit zero divisor.**  A composite `n` (`1 < n`, not prime) factors as
    `n = a·b` with `1 < a < n` and `1 < b < n` (`exists_nontrivial_factor` + `factor_bounds`).
    Then `a, b` are *nonzero* residues (`a < n ⟹ a % n = a ≠ 0`) whose product is `0`:
    `(a·b) % n = n % n = 0`.  This is the obstruction read straight off the factorization — no
    quotient ring involved. -/
theorem composite_imp_zero_divisor {n : Nat} (hn : 1 < n) (hcomp : ¬ Prime213 n) :
    ∃ a b, a % n ≠ 0 ∧ b % n ≠ 0 ∧ (a * b) % n = 0 := by
  have hn2 : 2 ≤ n := hn
  obtain ⟨a, hd, ha1, han⟩ := exists_nontrivial_factor hn2 hcomp
  obtain ⟨h1a, halt⟩ := factor_bounds hn2 hd ha1 han
  obtain ⟨b, hab⟩ := hd          -- n = a * b
  -- b is the cofactor: 1 < b < n
  have hdb : b ∣ n := ⟨a, by rw [hab, Nat.mul_comm]⟩
  have hb1 : b ≠ 1 := by
    intro he; rw [he, Nat.mul_one] at hab; exact absurd hab.symm han
  have hbn : b ≠ n := by
    intro he
    -- b = n with n = a*b and 1 < a forces n < n
    rw [he] at hab
    have : n * 1 = n * a := by rw [Nat.mul_one, Nat.mul_comm n a]; exact hab
    have hapos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn2
    have h1eqa : (1 : Nat) = a := Nat.eq_of_mul_eq_mul_left hapos this
    exact absurd h1eqa.symm (Nat.ne_of_gt h1a)
  obtain ⟨h1b, hblt⟩ := factor_bounds hn2 hdb hb1 hbn
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rw [Nat.mod_eq_of_lt halt]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h1a)
  · rw [Nat.mod_eq_of_lt hblt]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h1b)
  · -- (a*b) % n = n % n = 0
    rw [← hab]; exact mod_self n

/-- A residue invertible mod `n` cannot be a zero divisor: if `a·c ≡ 1` and `a·b ≡ 0` (mod `n`)
    then `b ≡ 0`.  (`b ≡ b·1 ≡ b·(a·c) ≡ (a·b)·c ≡ 0·c ≡ 0`.) -/
theorem zero_divisor_not_invertible {n a b : Nat}
    (hzd : (a * b) % n = 0) (hinv : hasInverse n a) : b % n = 0 := by
  obtain ⟨c, hc⟩ := hinv          -- (a*c) % n = 1 % n
  -- b % n = (b * (a*c)) % n  since (a*c) % n = 1 % n
  have step1 : (b * (a * c)) % n = (b * 1) % n := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure b (a * c) n,
        E213.Meta.Nat.MulMod213.mul_mod_pure b 1 n, hc]
  -- b * (a*c) = (a*b) * c
  have hreassoc : b * (a * c) = (a * b) * c := by
    rw [E213.Tactic.NatHelper.mul_left_comm b a c, E213.Tactic.NatHelper.mul_assoc a b c]
  -- ((a*b)*c) % n = 0  since (a*b) % n = 0
  have step2 : ((a * b) * c) % n = 0 := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure (a * b) c n, hzd, Nat.zero_mul]
    exact E213.Meta.Nat.AddMod213.zero_mod n
  -- combine: (b*1) % n = 0
  have hb1 : (b * 1) % n = 0 := by rw [← step1, hreassoc, step2]
  rwa [Nat.mul_one] at hb1

/-- ★★★ **composite ⟹ NOT a field.**  The explicit zero divisor cannot be invertible, so some
    nonzero residue lacks an inverse — `isFieldZn n` fails. -/
theorem composite_imp_not_field {n : Nat} (hn : 1 < n) (hcomp : ¬ Prime213 n) :
    ¬ isFieldZn n := by
  intro hfield
  obtain ⟨a, b, ha, hb, hzd⟩ := composite_imp_zero_divisor hn hcomp
  have hinv : hasInverse n a := hfield.2 a ha
  exact hb (zero_divisor_not_invertible hzd hinv)

/-! ## §4 — constructive prime/composite dichotomy + the iff -/

/-- **Constructive prime-or-composite** for `n ≥ 2`: bounded divisor search (`searchDiv`) either
    finds a nontrivial divisor (composite) or certifies primality (every divisor is `1` or `n`).
    `Classical`-free — no `by_contra`/excluded middle. -/
theorem prime_or_composite {n : Nat} (hn : 2 ≤ n) : Prime213 n ∨ ¬ Prime213 n := by
  rcases searchDiv n n with ⟨d, hd2, hdn, hddvd⟩ | hnone
  · -- nontrivial divisor d (2 ≤ d < n) ⟹ not prime
    right
    intro hp
    rcases hp.2 d hddvd with h1 | hpe
    · rw [h1] at hd2; exact absurd hd2 (by decide)
    · rw [hpe] at hdn; exact absurd hdn (Nat.lt_irrefl n)
  · -- no nontrivial divisor below n ⟹ prime
    left
    refine ⟨hn, ?_⟩
    intro e hen
    have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
    have hen_le : e ≤ n := le_of_dvd_loc hnpos hen
    rcases Nat.lt_or_ge e n with helt | hege
    · rcases Nat.lt_or_ge e 2 with he2 | he2
      · -- e < 2: e = 0 (impossible, 0∤n>0) or e = 1
        rcases Nat.lt_or_ge e 1 with he1 | he1
        · exfalso
          have he0 : e = 0 := Nat.le_antisymm (Nat.le_of_lt_succ he1) (Nat.zero_le e)
          rw [he0] at hen
          obtain ⟨c, hc⟩ := hen; rw [Nat.zero_mul] at hc
          rw [hc] at hnpos; exact absurd hnpos (Nat.lt_irrefl 0)
        · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ he2) he1)
      · exact absurd hen (hnone e he2 helt helt)
    · exact Or.inr (Nat.le_antisymm hen_le hege)

/-- ★★ **`ℤ/n` is a field ⟺ `n` is prime** (representative-level, for `n > 1`).  Forward via the
    constructive dichotomy `prime_or_composite`: if `n` were composite, `composite_imp_not_field`
    would contradict the field hypothesis; backward by `prime_imp_field`.  The whole content is the
    Bezout-vs-zero-divisor split — no quotient ring. -/
theorem field_iff_prime {n : Nat} (hn : 1 < n) : isFieldZn n ↔ Prime213 n := by
  constructor
  · intro hfield
    rcases prime_or_composite hn with hp | hcomp
    · exact hp
    · exact absurd hfield (composite_imp_not_field hn hcomp)
  · intro hp; exact prime_imp_field hp

/-! ## §5 — concrete smokes -/

open E213.Lib.Math.NumberTheory.PerfectNumbers (prime_of_bounded)

/-- `Prime213 5` via the `√q`-bounded primality check. -/
theorem prime5 : Prime213 5 := prime_of_bounded (by decide) (B := 3) (by decide) (by decide)

/-- `n = 5` is a field: each nonzero residue `1,2,3,4` has an inverse mod `5`
    (`1·1, 2·3, 3·2, 4·4 ≡ 1`) — instance of `prime_imp_field`. -/
theorem field_5 : isFieldZn 5 := prime_imp_field prime5

/-- Explicit inverses mod `5` (closed `decide` smokes): `2·3 ≡ 1`, `4·4 ≡ 1 (mod 5)`. -/
theorem inverses_mod_5 :
    (2 * 3) % 5 = 1 % 5 ∧ (3 * 2) % 5 = 1 % 5 ∧ (4 * 4) % 5 = 1 % 5 ∧ (1 * 1) % 5 = 1 % 5 := by
  decide

/-- `n = 6` is NOT a field: `2·3 ≡ 0 (mod 6)` is an explicit zero divisor with `2,3` nonzero. -/
theorem zero_divisor_6 : (2 % 6 ≠ 0) ∧ (3 % 6 ≠ 0) ∧ (2 * 3) % 6 = 0 := by decide

/-- `6` is not prime: it has the divisor `2 = 2·3`, distinct from `1` and `6`. -/
theorem not_prime_6 : ¬ Prime213 6 := by
  intro hp
  rcases hp.2 2 ⟨3, by decide⟩ with h | h <;> exact absurd h (by decide)

theorem not_field_6 : ¬ isFieldZn 6 :=
  composite_imp_not_field (by decide) not_prime_6

/-- `n = 7` is a field (prime). -/
theorem field_7 : isFieldZn 7 :=
  prime_imp_field (prime_of_bounded (by decide) (B := 3) (by decide) (by decide))

end E213.Lib.Math.NumberTheory.ModArith.FieldIffPrime
