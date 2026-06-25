import E213.Lens.Number.Nat213.Congruence
import E213.Meta.Nat.NatDiv213
import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT

/-!
# Lens.Number.Nat213.ModArithReadout — transporting the native modular corpus onto `Nat213` (∅-axiom)

The **descent leg**, leg-2 — *transport, not re-derivation*.  The carrier-readout `toNat`
(`ToNatReadout.toNat_faithful`) is a faithful homomorphism `Nat213 → ℕ`, so the rich *native-`Nat`*
modular-arithmetic corpus (`Lib/.../ModArith` — Fermat, Euler, Wilson, …) need not be **re-derived**
over the Raw-generated carrier: it can be **transported** along the readout.  Build the carrier weld
once (`Congruence.modeq_toNat_iff`), then *inherit* the corpus.

The one-time friction is that the native results speak the `%`-form `A % m = B % m`, while
`modeq_toNat_iff` speaks the subtraction-free additive form `∃ k l, A + m·k = B + m·l` (the form
forced by `Nat213` having **no zero**, no subtraction).  `mod_eq_imp_additive` is the bridge between
the two — a single native ℕ lemma — and `modeq_of_toNat_mod` packages the whole transport: any native
`%`-congruence of the readouts lifts to a `Nat213` `ModEq`.  Then **Fermat's little theorem** (both
the primary `a^p ≡ a` and the unit-group `a^(p-1) ≡ 1` forms) is a one-line corollary on the
generated carrier — the native proof inherited, not rebuilt.

This is the cross-domain insight of `frontiers/carrier_readout_crossdomain.md` made into Lean: the
welds are a *transport functor* `Nat213 → Nat`.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.ModArithReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (pow powNat one toNat toNat_ge_one pow_eq_powNat_toNat)
open E213.Lens.Number.Nat213.ToNatReadout (toNat_powNat)
open E213.Lens.Number.Nat213.Congruence (ModEq modeq_toNat_iff)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_primary universal_flt_main)

/-- ★★ **The native `%`→additive bridge** — `A % m = B % m ⟹ ∃ k l, A + m·k = B + m·l`.  Converts the
    native ℕ `%`-form congruence into the subtraction-free additive form that `modeq_toNat_iff`
    speaks (the form `Nat213`'s no-zero shape forces).  Witnesses `k = B/m`, `l = A/m`, closed by
    `div_add_mod_pure` (`m·(n/m) + n%m = n`) + the shared residue `A%m = B%m`.  ∅-axiom — uses the
    PURE `div_add_mod_pure`, **not** Lean-core `Nat.div_add_mod` (which is `[propext]`). -/
theorem mod_eq_imp_additive {m A B : Nat} (h : A % m = B % m) :
    ∃ k l : Nat, A + m * k = B + m * l := by
  refine ⟨B / m, A / m, ?_⟩
  have hA : m * (A / m) + A % m = A := div_add_mod_pure A m
  have hB : m * (B / m) + B % m = B := div_add_mod_pure B m
  calc A + m * (B / m)
      = (m * (A / m) + A % m) + m * (B / m) := by rw [hA]
    _ = (m * (B / m) + B % m) + m * (A / m) := by
          rw [h, Nat.add_assoc, Nat.add_comm (B % m) (m * (B / m)),
              Nat.add_comm (m * (A / m)) (m * (B / m) + B % m)]
    _ = B + m * (A / m) := by rw [hB]

/-- ★★★ **The transport functor on congruences** — a native `%`-congruence of the depth readouts
    lifts to a `Nat213` congruence: `a.toNat % m.toNat = b.toNat % m.toNat → ModEq m a b`.  This is
    the reusable weld: any native modular-arithmetic theorem stated as `A % m = B % m` of readouts
    transports to `Nat213` through it (`modeq_toNat_iff` ∘ `mod_eq_imp_additive`).  ∅-axiom. -/
theorem modeq_of_toNat_mod {m a b : Nat213}
    (h : a.toNat % m.toNat = b.toNat % m.toNat) : ModEq m a b :=
  modeq_toNat_iff.mpr (mod_eq_imp_additive h)

/-- The `Nat213`-exponent power reads out as the native power of the readouts:
    `(a^m).toNat = a.toNat ^ m.toNat`.  Via the `pow ↔ powNat` bridge (`pow_eq_powNat_toNat`) +
    `toNat_powNat`. -/
theorem toNat_pow (a m : Nat213) : (pow a m).toNat = a.toNat ^ m.toNat := by
  rw [pow_eq_powNat_toNat, toNat_powNat]

/-- ★★★ **Fermat's little theorem (primary form) over `Nat213`, transported** — for a prime modulus
    `p` (primality encoded as `h_prime_gcd`: every `0 < m < p.toNat` is coprime to `p.toNat`, the
    finite-quantifier form `UniversalFLT` uses), `a^p ≡ a (mod p)` on the Raw-generated carrier.
    **Not re-derived** — the native `universal_flt_primary` inherited through `modeq_of_toNat_mod` +
    `toNat_pow`.  Fully `Nat213`-native statement (exponent and modulus both the carrier `p`).
    ∅-axiom. -/
theorem flt_primary {a p : Nat213} (hp : 1 < p.toNat)
    (h_prime_gcd : ∀ m, 0 < m → m < p.toNat → (modBezout m p.toNat).1 = 1) :
    ModEq p (pow a p) a := by
  apply modeq_of_toNat_mod
  rw [toNat_pow]
  exact universal_flt_primary a.toNat p.toNat hp h_prime_gcd

/-- ★★★ **Fermat's little theorem (unit-group form) over `Nat213`, transported** — for a prime
    modulus `p` and `a` below it (`a.toNat < p.toNat`; the positivity `0 < a.toNat` is free —
    `Nat213` has no zero, `toNat_ge_one`), `a^(p-1) ≡ 1 (mod p)`.  The exponent reads *in* from ℕ
    as `p.toNat - 1` (`powNat`, the Nat-exponent power — a count-Lens readout, the legitimate
    direction), since `p - 1` is not a `Nat213` act.  Native `universal_flt_main` inherited.
    ∅-axiom. -/
theorem flt_main {a p : Nat213} (hp : 1 < p.toNat) (ha_lt : a.toNat < p.toNat)
    (h_prime_gcd : ∀ m, 0 < m → m < p.toNat → (modBezout m p.toNat).1 = 1) :
    ModEq p (powNat a (p.toNat - 1)) one := by
  apply modeq_of_toNat_mod
  rw [toNat_powNat]
  exact universal_flt_main a.toNat p.toNat hp (toNat_ge_one a) ha_lt h_prime_gcd

end E213.Lens.Number.Nat213.ModArithReadout
