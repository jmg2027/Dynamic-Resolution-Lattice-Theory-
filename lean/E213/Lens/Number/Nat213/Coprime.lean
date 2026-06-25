import E213.Lens.Number.Nat213.Gcd

/-!
# Lens.Number.Nat213.Coprime — coprimality over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, leg-2 — the coprimality discipline, built on `Gcd`.  Over `Nat213` two
numbers are **coprime** when their greatest common divisor is `one` (the bottom of the
divisibility order): `Coprime a b := IsGcd a b one`.

The headline is **Euclid's coprime-division law** `coprime_dvd_mul`: if `gcd(a,b)=1` and `a ∣ b·c`
then `a ∣ c` — proved by the same scaling trick as `EuclidUnique.euclid`, now packaged generically
from `Gcd.isGcd_mul_left`: scaling the coprimality `gcd(b,a)=1` by `c` gives `gcd(c·b, c·a)=c`, and
`a` is a common divisor of `c·b` (`= b·c`, the hypothesis) and `c·a` (trivially), so `a ∣ c`.
∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.Coprime

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (mul one mul_one mul_comm)
open E213.Lens.Number.Nat213.Divisibility (Dvd one_dvd dvd_trans dvd_mul_left)
open E213.Lens.Number.Nat213.Gcd
  (IsGcd isGcd_comm isGcd_one_left isGcd_one_right isGcd_self isGcd_unique
   isGcd_mul_left isGcd_greatest)

/-- **Coprime over the Raw-generated ℕ₊**: `gcd(a,b) = one` — the only common divisor is the
    bottom of the divisibility order. -/
def Coprime (a b : Nat213) : Prop := IsGcd a b one

/-- Coprimality is symmetric. -/
theorem coprime_comm {a b : Nat213} (h : Coprime a b) : Coprime b a := isGcd_comm h

/-- `one` is coprime to everything (it is the divisibility bottom). -/
theorem coprime_one_left (a : Nat213) : Coprime one a := isGcd_one_left a

/-- Everything is coprime to `one`. -/
theorem coprime_one_right (a : Nat213) : Coprime a one := isGcd_one_right a

/-- **`Coprime a a ⟹ a = one`** — only the unit is coprime to itself (`gcd(a,a) = a`, and
    coprimality forces it to be `one`). -/
theorem coprime_self_imp {a : Nat213} (h : Coprime a a) : a = one :=
  (isGcd_unique (isGcd_self a) h)

/-- **Coprimality descends to divisors of the left argument** — if `d ∣ a` and `gcd(a,b)=1`
    then `gcd(d,b)=1`.  A common divisor of `d`, `b` divides `a` (through `d`) and `b`, hence the
    gcd `one`. -/
theorem coprime_of_dvd_left {a b d : Nat213} (hda : Dvd d a) (h : Coprime a b) : Coprime d b :=
  ⟨one_dvd d, one_dvd b, fun _e hed heb => isGcd_greatest h (dvd_trans hed hda) heb⟩

/-- Coprimality descends to divisors of the right argument (via `coprime_comm`). -/
theorem coprime_of_dvd_right {a b d : Nat213} (hdb : Dvd d b) (h : Coprime a b) : Coprime a d :=
  coprime_comm (coprime_of_dvd_left hdb (coprime_comm h))

/-- ★★★ **Euclid's coprime-division law over the Raw-generated ℕ₊**: `gcd(a,b)=1` and `a ∣ b·c`
    ⟹ `a ∣ c`.  Scale the coprimality `gcd(b,a)=1` by `c` (`isGcd_mul_left`): `gcd(c·b, c·a) = c`.
    `a` divides `c·b = b·c` (hypothesis) and `c·a` (trivially), so `a` divides the gcd `c`. The
    generic packaging of the `EuclidUnique.euclid` scaling trick. ∅-axiom. -/
theorem coprime_dvd_mul {a b c : Nat213} (hcop : Coprime a b) (hdvd : Dvd a (mul b c)) :
    Dvd a c := by
  have hscaled : IsGcd (mul c b) (mul c a) c := by
    have h := isGcd_mul_left (isGcd_comm hcop) c
    rwa [mul_one] at h
  have hcb : Dvd a (mul c b) := by rw [mul_comm c b]; exact hdvd
  have hca : Dvd a (mul c a) := dvd_mul_left c a
  exact isGcd_greatest hscaled hcb hca

/-- The coprime-division law with the product written `c·b` (via `mul_comm`). -/
theorem coprime_dvd_mul' {a b c : Nat213} (hcop : Coprime a b) (hdvd : Dvd a (mul c b)) :
    Dvd a c := by
  apply coprime_dvd_mul hcop
  rwa [mul_comm b c]

end E213.Lens.Number.Nat213.Coprime
