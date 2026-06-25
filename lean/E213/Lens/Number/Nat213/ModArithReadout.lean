import E213.Lens.Number.Nat213.Congruence
import E213.Lens.Number.Nat213.Gcd
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.Gcd213
import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT
import E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem
import E213.Lib.Math.NumberTheory.ModArith.EulerCriterion
import E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction

/-!
# Lens.Number.Nat213.ModArithReadout — transporting the native modular corpus onto `Nat213` (∅-axiom)

The **descent leg**, leg-2 — *transport, not re-derivation*.  The carrier-readout `toNat`
(`ToNatReadout.toNat_faithful`) is a faithful homomorphism `Nat213 → ℕ`, so the rich *native-`Nat`*
modular-arithmetic corpus (`Lib/.../ModArith` — Fermat, Euler, Wilson, …) need not be **re-derived**
over the Raw-generated carrier: it can be **transported** along the readout.  Build the carrier weld
once (`Congruence.modeq_toNat_iff`), then *inherit* the corpus.

The friction is one of *reading form*: native results are stated as `%`-congruence (`A % m = B % m`),
divisibility (`m ∣ A − B`), or gcd (`gcd m n = 1`), while `Nat213` has **no zero, no subtraction**, so
`Congruence.modeq_toNat_iff` speaks the additive form `∃ k l, A + m·k = B + m·l`.  A small fixed set
of welds bridges each reading once:

* `mod_eq_imp_additive` / `modeq_of_toNat_mod` — `%`-congruence of readouts → `ModEq`;
* `modeq_of_dvd_sub` / `modeq_self_of_dvd` — divisibility of a difference / of the value → `ModEq`;
* `gcd213_eq_one_of_coprime` — `Nat213` coprimality → native `gcd213 = 1`.

With those, the corpus is **inherited**, each headline a one-liner over the generated carrier:
**Fermat** (`flt_primary` `a^p ≡ a`, `flt_main` `a^(p-1) ≡ 1`), **Wilson** (`wilson` `(p-1)! ≡ p-1`,
via the carrier `Peano.factorial`), **Euler's criterion** (`euler_criterion` `a^m ≡ ±1`, `euler_qr`
the QR branch), and the **Chinese Remainder Theorem reconstruction** (`crt_reconstruction` —
simultaneous-congruence *existence*, complementing `Congruence.crt_iff`).

This is the cross-domain insight of `frontiers/carrier_readout_crossdomain.md` made into Lean: the
welds are a *transport functor* `Nat213 → Nat`.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.ModArithReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (pow powNat one succ add mul toNat toNat_add toNat_mul toNat_ge_one pow_eq_powNat_toNat
   factorial factorial_succ)
open E213.Lens.Number.Nat213.ToNatReadout (toNat_surj toNat_powNat)
open E213.Lens.Number.Nat213.Congruence (ModEq modeq_toNat modeq_toNat_iff)
open E213.Lens.Number.Nat213.Coprime (Coprime)
open E213.Lens.Number.Nat213.Gcd (isGcd_toNat)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right mul_eq_one_left)
open E213.Tactic.NatHelper (gcd213 sub_add_cancel add_mul_mod_self_pure)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_primary universal_flt_main)
open E213.Lib.Math.NumberTheory.ModArith.EulerCriterion (euler_dichotomy euler_qr_pow_one)
open E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction (crtSolve crt_solve_residues)
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Meta.Nat.VpMul (IsPrime213)

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

/-- ★★ **The transport functor, forward direction** — a `Nat213` congruence pushes down to a native
    `%`-congruence of the readouts: `ModEq m a b → a.toNat % m.toNat = b.toNat % m.toNat`.  From the
    additive certificate (`modeq_toNat`): adding a multiple of `m.toNat` preserves the residue
    (`add_mul_mod_self_pure`), so `a.toNat % m = (a.toNat+m·k) % m = (b.toNat+m·l) % m = b.toNat % m`.
    The `mp` companion to `modeq_of_toNat_mod` — needed to transport native results that *consume* a
    `%`-congruence (e.g. `ord ∣ k` from `aᵏ ≡ 1`).  ∅-axiom. -/
theorem modeq_imp_toNat_mod {m a b : Nat213} (h : ModEq m a b) :
    a.toNat % m.toNat = b.toNat % m.toNat := by
  obtain ⟨k, l, hkl⟩ := modeq_toNat h
  calc a.toNat % m.toNat
      = (a.toNat + k * m.toNat) % m.toNat := (add_mul_mod_self_pure a.toNat m.toNat k).symm
    _ = (a.toNat + m.toNat * k) % m.toNat := by rw [Nat.mul_comm]
    _ = (b.toNat + m.toNat * l) % m.toNat := by rw [hkl]
    _ = (b.toNat + l * m.toNat) % m.toNat := by rw [Nat.mul_comm]
    _ = b.toNat % m.toNat := add_mul_mod_self_pure b.toNat m.toNat l

/-- ★★★ **The transport functor is a readout iff** — `ModEq m a b ⟺ a.toNat % m.toNat = b.toNat %
    m.toNat`.  The `Nat213` congruence and the native `%`-congruence of the depth readouts are the
    *same relation* read at the two resolutions.  The capstone weld: native modular results transport
    in **both** directions through it.  ∅-axiom. -/
theorem modeq_toNat_mod_iff {m a b : Nat213} :
    ModEq m a b ↔ a.toNat % m.toNat = b.toNat % m.toNat :=
  ⟨modeq_imp_toNat_mod, modeq_of_toNat_mod⟩

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

/-- The `Nat213` factorial reads out as the native factorial of the readout:
    `(n!).toNat = (n.toNat)!`.  Induction on `n`; the step is the readout of `mul` plus the native
    `fact`'s own recursion (`(n.toNat + 1)! = (n.toNat + 1) · (n.toNat)!`). -/
theorem toNat_factorial : ∀ n : Nat213, (factorial n).toNat = fact n.toNat
  | one    => rfl
  | succ n => by rw [factorial_succ, toNat_mul, toNat_factorial n]; rfl

/-- ★★★ **Wilson's theorem over `Nat213`, transported** — for a prime modulus `succ p₀` (= `p₀+1`;
    primality encoded as `IsPrime213 (succ p₀).toNat`), `p₀! ≡ p₀ (mod p₀+1)`, i.e. the classical
    `(p-1)! ≡ -1 (mod p)` in the no-negatives form `(p-1)! ≡ p-1`.  **Not re-derived** — the native
    `WilsonTheorem.wilson` inherited through `modeq_of_toNat_mod` + `toNat_factorial`.  The native
    `% p` form gives `(p-1)`, matched to `p₀.toNat % (succ p₀).toNat = p₀.toNat` by
    `Nat.mod_eq_of_lt` (`p₀.toNat < p₀.toNat + 1`).  ∅-axiom. -/
theorem wilson {p₀ : Nat213} (hp : IsPrime213 (succ p₀).toNat) :
    ModEq (succ p₀) (factorial p₀) p₀ := by
  apply modeq_of_toNat_mod
  rw [toNat_factorial]
  have hw : fact p₀.toNat % (succ p₀).toNat = p₀.toNat :=
    E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem.wilson hp
  rw [hw]
  exact (Nat.mod_eq_of_lt (Nat.lt_succ_self p₀.toNat)).symm

/-! ## Divisibility-form transport — Euler's criterion

The native results above are `%`-form; the next two — Euler's criterion and CRT — are stated
**divisibility-first** (`p ∣ (aᵐ − 1)`) and **gcd-first** (`gcd m n = 1`).  Two more carrier welds
handle those readings: `modeq_of_dvd_sub` (a native difference divisible by `m` lifts to `ModEq`)
and `modeq_self_of_dvd` (`m ∣ a` lifts to `a ≡ m ≡ 0`), plus the coprimality bridge
`gcd213_eq_one_of_coprime`.  Same principle: the carrier reading is built once, the corpus inherited. -/

/-- ★★ **Difference-divisibility → congruence** — `b.toNat ≤ a.toNat` and `m.toNat ∣ (a.toNat −
    b.toNat)` give `ModEq m a b`.  The divisibility reading of congruence (`m ∣ a−b`) lifted to the
    carrier: `a.toNat = b.toNat + m.toNat·k` directly, so `⟨0, k⟩` is the additive certificate.
    Subtraction lives only in native ℕ (`Nat213` has none); `sub_add_cancel` closes it.  ∅-axiom. -/
theorem modeq_of_dvd_sub {m a b : Nat213}
    (hle : b.toNat ≤ a.toNat) (hd : m.toNat ∣ (a.toNat - b.toNat)) : ModEq m a b := by
  obtain ⟨k, hk⟩ := hd
  apply modeq_toNat_iff.mpr
  refine ⟨0, k, ?_⟩
  rw [Nat.mul_zero, Nat.add_zero, ← hk, Nat.add_comm]
  exact (sub_add_cancel hle).symm

/-- ★★ **Modulus-divides → congruent to the modulus** — `m.toNat ∣ a.toNat ⟹ ModEq m a m`, i.e.
    `a ≡ 0 (mod m)` in the no-zero form `a ≡ m`.  The handle for the `aᵐ + 1 ≡ 0` branch of Euler's
    `±1` dichotomy.  The readout `a.toNat = m.toNat·k` has `k ≥ 1` (`a.toNat ≥ 1`, no zero), so
    `⟨0, k−1⟩` certifies `a = m + m·(k−1)`.  ∅-axiom. -/
theorem modeq_self_of_dvd {m a : Nat213} (hd : m.toNat ∣ a.toNat) : ModEq m a m := by
  obtain ⟨k, hk⟩ := hd
  have hk1 : 1 ≤ k := by
    cases k with
    | zero => rw [Nat.mul_zero] at hk; exact absurd (hk ▸ toNat_ge_one a) (by decide)
    | succ j => exact Nat.succ_le_succ (Nat.zero_le j)
  apply modeq_toNat_iff.mpr
  refine ⟨0, k - 1, ?_⟩
  rw [Nat.mul_zero, Nat.add_zero, hk,
      Nat.add_comm m.toNat (m.toNat * (k - 1)), ← Nat.mul_succ, Nat.succ_eq_add_one,
      sub_add_cancel hk1]

/-- ★★★ **Euler's criterion over `Nat213`, transported** — for a prime modulus `p` (divisor
    dichotomy `hpr`) and an exponent `m` with `2m = p.toNat − 1`, the half-power `aᵐ` is `≡ ±1`:
    `aᵐ ≡ 1 (mod p)` **or** `aᵐ + 1 ≡ 0 (mod p)` (the `−1` residue, in the no-negatives form
    `aᵐ + 1 ≡ p`).  Native `euler_dichotomy` (`p ∣ aᵐ−1 ∨ p ∣ aᵐ+1`) inherited through the two
    divisibility welds.  ∅-axiom. -/
theorem euler_criterion {p a : Nat213} (m : Nat)
    (hp : 1 < p.toNat) (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat)
    (hpm : 2 * m = p.toNat - 1) (halt : a.toNat < p.toNat) :
    ModEq p (powNat a m) one ∨ ModEq p (add (powNat a m) one) p := by
  rcases euler_dichotomy p.toNat m a.toNat hp hpr hpm (toNat_ge_one a) halt with h | h
  · left
    refine modeq_of_dvd_sub ?_ ?_
    · exact toNat_ge_one (powNat a m)
    · rw [toNat_powNat]; exact h
  · right
    apply modeq_self_of_dvd
    rw [toNat_add, toNat_powNat]; exact h

/-- ★★★ **Euler's criterion, quadratic-residue direction over `Nat213`** — if `a` is a quadratic
    residue mod `p` (`x² ≡ a` for a unit `x < p`), then `aᵐ ≡ 1 (mod p)` (the `+1` branch).  Native
    `euler_qr_pow_one` inherited through `modeq_of_dvd_sub`.  ∅-axiom. -/
theorem euler_qr {p a : Nat213} (m : Nat)
    (hp : 1 < p.toNat) (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat)
    (hpm : 2 * m = p.toNat - 1) (x : Nat213) (hxlt : x.toNat < p.toNat)
    (hx2 : x.toNat ^ 2 % p.toNat = a.toNat) :
    ModEq p (powNat a m) one := by
  have h := euler_qr_pow_one p.toNat m a.toNat hp hpr hpm x.toNat (toNat_ge_one x) hxlt hx2
  refine modeq_of_dvd_sub ?_ ?_
  · exact toNat_ge_one (powNat a m)
  · rw [toNat_powNat]; exact h

/-! ## Gcd-form transport — the Chinese Remainder Theorem (reconstruction) -/

/-- ★★ **Coprimality → native gcd = 1** — `Coprime m n` over `Nat213` reads out as `gcd213
    m.toNat n.toNat = 1`.  `Coprime = IsGcd · · one`, whose readout (`isGcd_toNat`) gives the
    universal property; instantiated at the native `gcd213` (which divides both readouts) it forces
    `gcd213 ∣ 1`, hence `= 1` (`mul_eq_one_left`).  ∅-axiom. -/
theorem gcd213_eq_one_of_coprime {m n : Nat213} (h : Coprime m n) :
    gcd213 m.toNat n.toNat = 1 := by
  obtain ⟨_, _, hgreat⟩ := isGcd_toNat h
  obtain ⟨k, hk⟩ :=
    hgreat _ (gcd213_dvd_left m.toNat n.toNat) (gcd213_dvd_right m.toNat n.toNat)
  exact mul_eq_one_left _ k hk.symm

/-- ★★★ **Chinese Remainder Theorem (reconstruction) over `Nat213`, transported** — for coprime
    moduli `m`, `n` and any targets `a`, `b`, there is a carrier `s` simultaneously congruent:
    `s ≡ a (mod m)` and `s ≡ b (mod n)`.  This is the CRT *existence* (the surjectivity of
    `x ↦ (x mod m, x mod n)`), complementing `Congruence.crt_iff` (the combine/split for one pair).
    Native `CRTReconstruction.crt_solve_residues` builds the explicit Bezout solution; its readout is
    lifted to a carrier by `toNat_surj` (shifted by `m·n ≥ 1` to clear the no-zero gap, which
    `add_mul_mod_self_pure` absorbs), and `modeq_of_toNat_mod` closes both congruences.  ∅-axiom. -/
theorem crt_reconstruction {m n a b : Nat213} (h : Coprime m n) :
    ∃ s : Nat213, ModEq m s a ∧ ModEq n s b := by
  have hg : gcd213 m.toNat n.toNat = 1 := gcd213_eq_one_of_coprime h
  obtain ⟨hsm, hsn⟩ :=
    crt_solve_residues hg (toNat_ge_one m) (toNat_ge_one n) a.toNat b.toNat
  have hpos : 1 ≤ crtSolve m.toNat n.toNat a.toNat b.toNat + m.toNat * n.toNat :=
    Nat.le_trans (Nat.mul_le_mul (toNat_ge_one m) (toNat_ge_one n)) (Nat.le_add_left _ _)
  obtain ⟨s, hs⟩ := toNat_surj _ hpos
  refine ⟨s, ?_, ?_⟩
  · apply modeq_of_toNat_mod
    rw [hs, Nat.mul_comm m.toNat n.toNat, add_mul_mod_self_pure _ m.toNat n.toNat]
    exact hsm
  · apply modeq_of_toNat_mod
    rw [hs, add_mul_mod_self_pure _ n.toNat m.toNat]
    exact hsn

end E213.Lens.Number.Nat213.ModArithReadout
