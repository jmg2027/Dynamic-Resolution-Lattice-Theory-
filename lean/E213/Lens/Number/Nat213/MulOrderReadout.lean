import E213.Lens.Number.Nat213.ModArithReadout
import E213.Lib.Math.NumberTheory.ModArith.MulOrder

/-!
# Lens.Number.Nat213.MulOrderReadout — the multiplicative-order corpus over `Nat213` (∅-axiom)

The **descent leg**, leg-2 — the structure theory of the unit group `(ℤ/pℤ)*` transported onto the
Raw-generated carrier.  After Fermat / Euler / Wilson (`ModArithReadout`), the next coherent corpus
is the **multiplicative order**: the least positive exponent `mulOrd a p` with `a^k ≡ 1 (mod p)`.

The order is a **count read OUT into ℕ** — the valuation pattern (`Valuation.vp`): a multiplicity
that can in principle be any natural, so it lives in ℕ, not on the zero-free carrier.  `mulOrd a p :=
ordModP a.toNat p.toNat` is exactly that readout.  The corpus then transports through the readout
**iff** `ModArithReadout.modeq_toNat_mod_iff` (both directions — the order's *defining* congruence
`a^ord ≡ 1` lifts out, and the *divides-any-fixing-exponent* law `aᵏ ≡ 1 ⟹ ord ∣ k` consumes a
congruence lifted in):

* `pow_mulOrd_one` — `a^(mulOrd a p) ≡ 1 (mod p)` (the order fixes `a`);
* `mulOrd_pos` — `1 ≤ mulOrd a p`;
* `mulOrd_min` — minimality: no `1 ≤ j < mulOrd a p` has `a^j ≡ 1`;
* `mulOrd_dvd` — `a^k ≡ 1 (mod p) ⟹ mulOrd a p ∣ k` (the order divides every fixing exponent);
* `mulOrd_dvd_pred` — `mulOrd a p ∣ (p − 1)` (Lagrange: order divides the group order, via Fermat).

Native source: `Lib/.../ModArith/MulOrder` (`ordModP`, `pow_ord`, `ord_min`, `ord_dvd`,
`ord_dvd_p_sub_one`).  Transported, not re-derived.  Primality is the divisor-dichotomy hypothesis
`hpr` (the form `MulOrder` uses); the unit condition is `a.toNat < p.toNat` (positivity `0 <
a.toNat` is free — `Nat213` has no zero).  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.MulOrderReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (one powNat toNat toNat_ge_one)
open E213.Lens.Number.Nat213.ToNatReadout (toNat_powNat)
open E213.Lens.Number.Nat213.Congruence (ModEq)
open E213.Lens.Number.Nat213.ModArithReadout (modeq_of_toNat_mod modeq_imp_toNat_mod)
open E213.Lib.Math.NumberTheory.ModArith.MulOrder
  (ordModP pow_ord ord_pos ord_min ord_dvd ord_dvd_p_sub_one)

/-- **The multiplicative order of `a` mod `p`** over `Nat213`, a count read OUT into ℕ (no zero on
    the carrier, so the order — which a valuation-style multiplicity — lives in ℕ): the least
    positive `k` with `a^k ≡ 1 (mod p)`, as the native `ordModP` of the depth readouts. -/
abbrev mulOrd (a p : Nat213) : Nat := ordModP a.toNat p.toNat

/-- **The order is positive** — `1 ≤ mulOrd a p` (for a prime `p` and unit `a < p`). -/
theorem mulOrd_pos {a p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (halt : a.toNat < p.toNat) :
    1 ≤ mulOrd a p :=
  ord_pos a.toNat p.toNat hp hpr (toNat_ge_one a) halt

/-- ★★★ **The order fixes `a`** — `a^(mulOrd a p) ≡ 1 (mod p)`: the defining congruence of the
    multiplicative order, on the carrier.  Native `pow_ord` lifted out through `modeq_of_toNat_mod`
    (`a.toNat^ord % p.toNat = 1 = 1 % p.toNat`, the last step by `1 < p.toNat`).  ∅-axiom. -/
theorem pow_mulOrd_one {a p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (halt : a.toNat < p.toNat) :
    ModEq p (powNat a (mulOrd a p)) one := by
  apply modeq_of_toNat_mod
  rw [toNat_powNat, pow_ord a.toNat p.toNat hp hpr (toNat_ge_one a) halt]
  exact (Nat.mod_eq_of_lt hp).symm

/-- ★★ **Minimality of the order** — no exponent `1 ≤ j < mulOrd a p` fixes `a`: `¬ a^j ≡ 1 (mod p)`.
    Native `ord_min` consumed through the forward readout (`modeq_imp_toNat_mod`).  ∅-axiom. -/
theorem mulOrd_min {a p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (halt : a.toNat < p.toNat) :
    ∀ j : Nat, 1 ≤ j → j < mulOrd a p → ¬ ModEq p (powNat a j) one := by
  intro j hj1 hjlt hcon
  apply ord_min a.toNat p.toNat hp hpr (toNat_ge_one a) halt j hj1 hjlt
  have h := modeq_imp_toNat_mod hcon
  rw [toNat_powNat] at h
  rw [h]; exact Nat.mod_eq_of_lt hp

/-- ★★★ **The order divides every fixing exponent** — `a^k ≡ 1 (mod p) ⟹ mulOrd a p ∣ k`.  Native
    `ord_dvd` consumed through the forward readout: the `Nat213` congruence pushes down to
    `a.toNat^k % p.toNat = 1`, which the native law turns into divisibility.  ∅-axiom. -/
theorem mulOrd_dvd {a p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (halt : a.toNat < p.toNat)
    (k : Nat) (hk : ModEq p (powNat a k) one) : mulOrd a p ∣ k := by
  apply ord_dvd a.toNat p.toNat hp hpr (toNat_ge_one a) halt k
  have h := modeq_imp_toNat_mod hk
  rw [toNat_powNat] at h
  rw [h]; exact Nat.mod_eq_of_lt hp

/-- ★★ **Lagrange: the order divides `p − 1`** — `mulOrd a p ∣ (p.toNat − 1)`, the group order.
    Native `ord_dvd_p_sub_one` (= `ord_dvd` applied to Fermat's exponent) at the readouts.  ∅-axiom. -/
theorem mulOrd_dvd_pred {a p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (halt : a.toNat < p.toNat) :
    mulOrd a p ∣ (p.toNat - 1) :=
  ord_dvd_p_sub_one a.toNat p.toNat hp hpr (toNat_ge_one a) halt

end E213.Lens.Number.Nat213.MulOrderReadout
