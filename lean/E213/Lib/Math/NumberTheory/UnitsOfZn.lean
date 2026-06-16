import E213.Meta.Nat.Gcd213
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.EulerTotient

/-!
# The multiplicative group `(ℤ/n)^×` on representatives (∅-axiom)

**The forcing.**  Classically `(ℤ/n)^×` is the group of *units of the quotient
ring* `ℤ/n` — its very definition presupposes the ring `ℤ/n` and its unit set.
On representatives over `Nat` there is no quotient ring: the multiplicative group
is the **explicit set of coprime residues** `{a < n : gcd(a,n)=1}`, closed under
`·` mod `n` (a `gcd` fact — `gcd(ab,n)=1` from `gcd(a,n)=gcd(b,n)=1`, and `gcd`
is mod-invariant), with inverses produced by **Bezout** (`inverse_of_coprime`),
of size **φ(n)** (the corpus `totient`).  The quotient ring was packaging:
closure is a gcd fact, inverses are Bezout, order is φ(n).

Reuse only (no redefinition): `gcd213`, `totient`/`coprimeInd`/`sumTo`,
`coprime_mul_of_coprime`, `inverse_of_coprime`, `gcd213_rec`/`gcd213_comm`.
-/

namespace E213.Lib.Math.NumberTheory.UnitsOfZn

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213 (gcd213_rec gcd213_comm)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_mul_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (inverse_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Lib.Math.NumberTheory.EulerTotient (totient coprimeInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-- A **unit** of `ℤ/n` on representatives: a residue coprime to `n`.
    `isUnit n a := gcd213 a n = 1`. -/
def isUnit (n a : Nat) : Prop := gcd213 a n = 1

/-! ## `gcd` is mod-invariant in the first slot: `gcd((a)%n, n) = gcd(a, n)` -/

/-- **`gcd` is preserved by reducing the first argument mod `n`** (`0 < n`):
    `gcd213 (a % n) n = gcd213 a n`.  Two Euclidean steps:
    `gcd(a,n) = gcd(n, a) = gcd(a % n, n)`. -/
theorem gcd_mod_left (n a : Nat) (hn : 0 < n) :
    gcd213 (a % n) n = gcd213 a n := by
  rw [gcd213_comm a n, gcd213_rec n a hn]

/-! ## ★★ Identity -/

/-- ★★ **`1` is a unit** (the identity of the group): `gcd213 1 n = 1`. -/
theorem unit_one (n : Nat) : isUnit n 1 :=
  E213.Meta.Nat.Gcd213.gcd213_one_left n

/-! ## ★★★ Closure under `·` mod `n` -/

/-- ★★★ **Units are closed under multiplication mod `n`.**  If `gcd(a,n)=1` and
    `gcd(b,n)=1`, then `gcd((a*b) % n, n) = 1`: the product is coprime to `n`
    (`coprime_mul_of_coprime`, after `gcd213_comm`), and reducing mod `n`
    preserves the gcd (`gcd_mod_left`). -/
theorem unit_mul_closed (n a b : Nat) (hn : 0 < n)
    (ha : isUnit n a) (hb : isUnit n b) : isUnit n ((a * b) % n) := by
  show gcd213 ((a * b) % n) n = 1
  rw [gcd_mod_left n (a * b) hn]
  -- gcd(a*b, n) = 1  ⟺  gcd(n, a*b) = 1  from gcd(n,a)=gcd(n,b)=1
  rw [gcd213_comm (a * b) n]
  have ha' : gcd213 a n = 1 := ha
  have hb' : gcd213 b n = 1 := hb
  exact coprime_mul_of_coprime
    ((gcd213_comm n a).trans ha') ((gcd213_comm n b).trans hb')

/-! ## ★★★ Inverses (Bezout) -/

/-- A residue `c` with `(a*c) % n = 1` is itself a unit: any common divisor `g`
    of `c` and `n` divides `a*c` and `n`, hence the remainder `(a*c) % n = 1`,
    so `g = 1`.  This is the "inverse is a unit" core. -/
theorem inv_is_unit (n a c : Nat) (hn0 : 0 < n) (hac : (a * c) % n = 1) :
    isUnit n c := by
  show gcd213 c n = 1
  have hgc : gcd213 c n ∣ c := E213.Meta.Nat.Gcd213.gcd213_dvd_left c n
  have hgn : gcd213 c n ∣ n := E213.Meta.Nat.Gcd213.gcd213_dvd_right c n
  -- g ∣ c ⟹ g ∣ c*a = a*c
  have hgac : gcd213 c n ∣ (a * c) := by
    have h1 : gcd213 c n ∣ (c * a) :=
      E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor.dvd_mul_right_loc
        (gcd213 c n) c a hgc
    rwa [Nat.mul_comm c a] at h1
  -- g ∣ n and g ∣ a*c  ⟹  g ∣ (a*c) % n = 1
  have hgmod : gcd213 c n ∣ ((a * c) % n) :=
    E213.Meta.Nat.Gcd213.dvd_mod_via_fuel (a * c) n (a * c) (gcd213 c n)
      hn0 (Nat.le_refl _) hgn hgac
  have hg1 : gcd213 c n ∣ 1 := hac ▸ hgmod
  obtain ⟨k, hk⟩ := hg1
  exact E213.Meta.Nat.Gcd213.mul_eq_one_left (gcd213 c n) k hk.symm

/-- ★★★ **Every unit has a unit inverse** (`1 < n`).  The Bezout inverse
    `b := (modBezout a n).2 % n` satisfies `(a*b) % n = 1 % n` and is itself a
    unit.  Inverse existence: `inverse_of_coprime` gives `(a*c) % n = 1 % n` for
    `c := (modBezout a n).2`; reducing `c` mod `n` leaves the product
    unchanged.  The inverse is a unit because `(a*b) ≡ 1` forces `gcd(b,n)=1`
    (any common divisor of `b` and `n` divides `a*b` and `n`, hence
    `(a*b) % n`, which is `1`). -/
theorem unit_has_inverse (n a : Nat) (hn : 1 < n) (ha : isUnit n a) :
    ∃ b, isUnit n b ∧ (a * b) % n = 1 % n := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  -- Bezout gives c with (a*c) % n = 1 % n;  the witness is b := c % n.
  have hinv : (a * (modBezout a n).2) % n = 1 % n := inverse_of_coprime a n hn0 ha
  -- product with the reduced inverse:  (a * (c % n)) % n = 1 % n
  have hbprod : (a * ((modBezout a n).2 % n)) % n = 1 % n := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure a ((modBezout a n).2 % n) n,
        E213.Meta.Nat.AddMod213.mod_mod (modBezout a n).2 n,
        ← E213.Meta.Nat.MulMod213.mul_mod_pure a (modBezout a n).2 n]
    exact hinv
  have hb1 : (a * ((modBezout a n).2 % n)) % n = 1 := by
    rw [hbprod, Nat.mod_eq_of_lt hn]
  exact ⟨(modBezout a n).2 % n, inv_is_unit n a ((modBezout a n).2 % n) hn0 hb1, hbprod⟩

/-! ## ★★ Order = φ(n): the unit count is the totient -/

/-- The count of units below `n`: `Σ_{a=0}^{n-1} [gcd213 (a+1) n = 1]`.
    This counts the residues `a+1 ∈ {1,…,n}` coprime to `n`. -/
def unitCount (n : Nat) : Nat := sumTo n (fun a => (gcd213 (a + 1) n == 1).toNat)

/-- ★★ **The unit group has order φ(n).**  The count of coprime residues below
    `n` is exactly the corpus `totient` — `rfl`, since `totient n =
    sumTo n (fun a => (gcd213 (a+1) n == 1).toNat)` (`coprimeInd`). -/
theorem unit_count_eq_totient (n : Nat) : unitCount n = totient n := rfl

/-! ## ★ Smokes (`decide`, closed) -/

/-- Units mod 8 are `{1,3,5,7}` (non-units `{2,4,6}`) — and `φ(8) = 4`.
    Stated with `gcd213 _ 8 = 1` (= `isUnit 8 _` by definition, decidable). -/
theorem units_mod_8_smoke :
    gcd213 1 8 = 1 ∧ gcd213 3 8 = 1 ∧ gcd213 5 8 = 1 ∧ gcd213 7 8 = 1 ∧
    ¬ gcd213 2 8 = 1 ∧ ¬ gcd213 4 8 = 1 ∧ ¬ gcd213 6 8 = 1 ∧ totient 8 = 4 := by
  decide

/-- `isUnit 8 a` reading of the smoke (definitional). -/
theorem units_mod_8_isUnit : isUnit 8 1 ∧ isUnit 8 3 ∧ isUnit 8 5 ∧ isUnit 8 7 :=
  ⟨units_mod_8_smoke.1, units_mod_8_smoke.2.1,
   units_mod_8_smoke.2.2.1, units_mod_8_smoke.2.2.2.1⟩

/-- Closure: `3·5 = 15 ≡ 7 (mod 8)`, and `7` is a unit. -/
theorem closure_mod_8_smoke : (3 * 5) % 8 = 7 ∧ gcd213 ((3 * 5) % 8) 8 = 1 := by
  decide

/-- Inverses mod 8: every unit is its own inverse (`3·3 ≡ 1`, `5·5 ≡ 1`, `7·7 ≡ 1`). -/
theorem inverses_mod_8_smoke :
    (1 * 1) % 8 = 1 ∧ (3 * 3) % 8 = 1 ∧ (5 * 5) % 8 = 1 ∧ (7 * 7) % 8 = 1 := by
  decide

end E213.Lib.Math.NumberTheory.UnitsOfZn
