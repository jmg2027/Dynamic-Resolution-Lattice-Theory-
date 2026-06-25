import E213.Lens.Number.Nat213.ModArithReadout
import E213.Meta.Nat.AddMod213

/-!
# Lens.Number.Nat213.BinomialReadout — the freshman's dream & vanishing binomials over `Nat213` (∅-axiom)

The **descent leg**, leg-2 — the **binomial-coefficient** core of prime modular arithmetic
transported onto the carrier: the *freshman's dream* `(a+1)^p ≡ a^p + 1 (mod p)` and the vanishing of
the middle binomial coefficients `p ∣ C(p, k)` (`0 < k < p`).  These are the engine behind Fermat's
little theorem (`ModArithReadout.flt_primary`): the dream collapses the binomial expansion because
every interior `C(p,k)` carries a factor of `p`.

The binomial coefficient is a count read OUT into ℕ (`choose p.toNat k`).  The dream is `%`-form, so
it transports through the existing weld `modeq_of_toNat_mod`; the vanishing is a divisibility of the
readout (`dvd_of_mod_eq_zero` of the native `% p = 0`).

* `freshman_dream` — `(a+1)^p ≡ a^p + 1 (mod p)` on the carrier (`succ a` and `add … one`);
* `middle_binomial_dvd` — `p ∣ C(p, k+1)` for `k < p − 1`.

Primality is the finite-quantifier `h_prime_gcd` form `UniversalFLT` uses.  Native source:
`Lib/.../ModArith/UniversalFLT`.  Transported, not re-derived.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.BinomialReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (powNat succ add one toNat toNat_add)
open E213.Lens.Number.Nat213.ToNatReadout (toNat_powNat)
open E213.Lens.Number.Nat213.Congruence (ModEq)
open E213.Lens.Number.Nat213.ModArithReadout (modeq_of_toNat_mod)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_freshman_dream universal_middle_binomial_vanish)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)

/-- ★★★ **The freshman's dream over `Nat213`** — for a prime modulus `p` (`h_prime_gcd`), raising to
    the `p`-th power is additive on `a + 1`: `(a+1)^p ≡ a^p + 1 (mod p)`.  The collapse that drives
    Fermat: the interior binomial terms vanish.  Native `universal_freshman_dream` lifted out through
    `modeq_of_toNat_mod` (`succ a` reads as `a.toNat + 1`, `one` as `1`).  ∅-axiom. -/
theorem freshman_dream {a p : Nat213} (hp : 1 < p.toNat)
    (hpg : ∀ m, 0 < m → m < p.toNat → (modBezout m p.toNat).1 = 1) :
    ModEq p (powNat (succ a) p.toNat) (add (powNat a p.toNat) one) := by
  apply modeq_of_toNat_mod
  rw [toNat_powNat, toNat_add, toNat_powNat]
  exact universal_freshman_dream a.toNat p.toNat hp hpg

/-- ★★ **Vanishing middle binomials** — for a prime modulus `p`, every interior binomial coefficient
    is divisible by `p`: `p ∣ C(p, k+1)` for `k < p − 1`.  The combinatorial fact behind the
    freshman's dream (`p` divides `p! / (j!(p−j)!)` for `0 < j < p`).  Native
    `universal_middle_binomial_vanish` (`% p = 0`) read as divisibility of the count.  ∅-axiom. -/
theorem middle_binomial_dvd {p : Nat213} (hp : 1 < p.toNat)
    (hpg : ∀ m, 0 < m → m < p.toNat → (modBezout m p.toNat).1 = 1)
    (k : Nat) (hk : k < p.toNat - 1) : p.toNat ∣ choose p.toNat (k + 1) :=
  dvd_of_mod_eq_zero (universal_middle_binomial_vanish p.toNat hp hpg k hk)

end E213.Lens.Number.Nat213.BinomialReadout
