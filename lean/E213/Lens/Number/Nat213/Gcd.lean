import E213.Lens.Number.Nat213.EuclidUnique
import E213.Lens.Number.Nat213.ToNatReadout

/-!
# Lens.Number.Nat213.Gcd — the gcd discipline over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, leg-2.  `EuclidUnique.gcd_exists_mul` proved the existence of a
subtractive greatest-common-divisor with the *scaled* spec (`GcdMulSpec` — the multiplicative law
`gcd(c·a,c·b)=c·gcd(a,b)` baked into the quantifier over the scaling `c`), in one well-founded
induction with no zero and no subtraction operator.  This file extracts the clean discipline:

`IsGcd a b d` is the **greatest lower bound of `a`, `b` in the divisibility partial order**
(`Divisibility.dvd_antisymm`): a common divisor that every common divisor divides.  Over `Nat213`
the gcd **exists** (`isGcd_exists`, from the subtractive algorithm) and is **unique**
(`isGcd_unique`, from `dvd_antisymm`) — so divisibility is a meet-semilattice on the
distinguishing's own counting object — with the multiplicative law `gcd(c·a,c·b)=c·gcd(a,b)`
(`isGcd_mul_left`) following directly from the scaled existence + uniqueness.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.Gcd

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (mul one mul_one one_mul mul_comm toNat_ge_one)
open E213.Lens.Number.Nat213.Divisibility (Dvd dvd_refl dvd_antisymm one_dvd)
open E213.Lens.Number.Nat213.EuclidUnique (GcdMulSpec gcd_exists_mul)
open E213.Lens.Number.Nat213.ToNatReadout (dvd_toNat_iff toNat_surj)

/-- **Greatest common divisor over the Raw-generated ℕ₊**: `d` is a common divisor of `a`, `b`
    that every common divisor divides — the **greatest lower bound** in the `Dvd` partial order.
    The `c = 1` instance of `EuclidUnique.GcdMulSpec`. -/
def IsGcd (a b d : Nat213) : Prop :=
  Dvd d a ∧ Dvd d b ∧ (∀ e, Dvd e a → Dvd e b → Dvd e d)

/-- The scaled spec at scaling `one` is plain `IsGcd`. -/
theorem isGcd_of_gcdMulSpec {a b d : Nat213} (h : GcdMulSpec a b d) : IsGcd a b d := by
  obtain ⟨h1, h2, h3⟩ := h one
  rw [one_mul, one_mul] at h1 h2
  refine ⟨h1, h2, fun e he1 he2 => ?_⟩
  have h3' := h3 e (by rwa [one_mul]) (by rwa [one_mul])
  rwa [one_mul] at h3'

/-- ★★★ **gcd exists** — from the subtractive algorithm (`gcd_exists_mul`), no zero, no
    subtraction operator.  Divisibility over `Nat213` has all binary meets. -/
theorem isGcd_exists (a b : Nat213) : ∃ d, IsGcd a b d := by
  obtain ⟨d, hd⟩ := gcd_exists_mul a b
  exact ⟨d, isGcd_of_gcdMulSpec hd⟩

/-- ★★★ **gcd is unique** — two greatest common divisors divide each other, so are equal by
    `dvd_antisymm`.  The meet is well-defined; "the" gcd is justified. -/
theorem isGcd_unique {a b d₁ d₂ : Nat213} (h1 : IsGcd a b d₁) (h2 : IsGcd a b d₂) : d₁ = d₂ :=
  dvd_antisymm (h2.2.2 d₁ h1.1 h1.2.1) (h1.2.2 d₂ h2.1 h2.2.1)

/-- gcd is symmetric: `gcd(a,b) = gcd(b,a)`. -/
theorem isGcd_comm {a b d : Nat213} (h : IsGcd a b d) : IsGcd b a d :=
  ⟨h.2.1, h.1, fun e he1 he2 => h.2.2 e he2 he1⟩

/-- A gcd divides its left argument. -/
theorem isGcd_dvd_left {a b d : Nat213} (h : IsGcd a b d) : Dvd d a := h.1

/-- A gcd divides its right argument. -/
theorem isGcd_dvd_right {a b d : Nat213} (h : IsGcd a b d) : Dvd d b := h.2.1

/-- A gcd is divisible by every common divisor (it is greatest). -/
theorem isGcd_greatest {a b d e : Nat213} (h : IsGcd a b d)
    (h1 : Dvd e a) (h2 : Dvd e b) : Dvd e d := h.2.2 e h1 h2

/-- `gcd(a,a) = a` — the meet of an element with itself. -/
theorem isGcd_self (a : Nat213) : IsGcd a a a :=
  ⟨dvd_refl a, dvd_refl a, fun _ he1 _ => he1⟩

/-- `gcd(1,a) = 1` — `one` is the bottom of the divisibility order. -/
theorem isGcd_one_left (a : Nat213) : IsGcd one a one :=
  ⟨dvd_refl one, one_dvd a, fun _ he1 _ => he1⟩

/-- `gcd(a,1) = 1`. -/
theorem isGcd_one_right (a : Nat213) : IsGcd a one one :=
  isGcd_comm (isGcd_one_left a)

/-- **`a ∣ b ⟹ gcd(a,b) = a`** — a divisor *is* the meet with its multiple.  (`a ∣ a` and
    `a ∣ b` make `a` a common divisor; any common divisor of `a`, `b` divides `a`.) -/
theorem isGcd_of_dvd {a b : Nat213} (h : Dvd a b) : IsGcd a b a :=
  ⟨dvd_refl a, h, fun _ he1 _ => he1⟩

/-- ★★★ **The multiplicative law `gcd(c·a, c·b) = c·gcd(a,b)`** — Euclid's Bézout substitute.
    From the *scaled* existence (`gcd_exists_mul`) at scaling `c` and uniqueness: the unique gcd
    `d` of `a`, `b` satisfies the full scaled spec, whose `c`-instance is `IsGcd (c·a) (c·b) (c·d)`. -/
theorem isGcd_mul_left {a b d : Nat213} (h : IsGcd a b d) (c : Nat213) :
    IsGcd (mul c a) (mul c b) (mul c d) := by
  obtain ⟨d', hd'⟩ := gcd_exists_mul a b
  have hdd' : d = d' := isGcd_unique h (isGcd_of_gcdMulSpec hd')
  subst hdd'
  obtain ⟨h1, h2, h3⟩ := hd' c
  exact ⟨h1, h2, h3⟩

/-- `gcd(a·c, b·c) = gcd(a,b)·c` (right-scaled form, via `mul_comm`). -/
theorem isGcd_mul_right {a b d : Nat213} (h : IsGcd a b d) (c : Nat213) :
    IsGcd (mul a c) (mul b c) (mul d c) := by
  have := isGcd_mul_left h c
  rwa [mul_comm c a, mul_comm c b, mul_comm c d] at this

/-- ★★★ **The gcd discipline over the Raw-generated ℕ₊**: divisibility is a meet-semilattice —
    every pair has a greatest common divisor, unique, with the multiplicative law.  The gcd
    discipline generated all the way down on the distinguishing's own counting object. -/
theorem gcd_meet_semilattice :
    (∀ a b : Nat213, ∃ d, IsGcd a b d)
    ∧ (∀ a b d₁ d₂ : Nat213, IsGcd a b d₁ → IsGcd a b d₂ → d₁ = d₂)
    ∧ (∀ a b d c : Nat213, IsGcd a b d → IsGcd (mul c a) (mul c b) (mul c d)) :=
  ⟨isGcd_exists, fun _ _ _ _ => isGcd_unique, fun _ _ _ c h => isGcd_mul_left h c⟩

/-- ★★★ **The generated gcd reads out as a native greatest-common-divisor** — `IsGcd a b d`
    implies `d.toNat` divides both `a.toNat`, `b.toNat` and is divisible by every native common
    divisor.  The gcd analogue of `Valuation.vp_eq_vpSub`, at spec level: the `Nat213` meet-
    semilattice structure is the readout of the native gcd structure.  ⟹ via `dvd_toNat_iff`; the
    greatest clause lifts a native common divisor `e` back through `toNat`'s surjectivity onto ℕ₊
    (`toNat_surj`; `e ≥ 1` since `e ∣ a.toNat` and `a.toNat ≥ 1`), runs it through `IsGcd`'s own
    greatest clause, and reads the result back out.  ∅-axiom. -/
theorem isGcd_toNat {a b d : Nat213} (h : IsGcd a b d) :
    d.toNat ∣ a.toNat ∧ d.toNat ∣ b.toNat ∧
      ∀ e : Nat, e ∣ a.toNat → e ∣ b.toNat → e ∣ d.toNat := by
  refine ⟨dvd_toNat_iff.mp h.1, dvd_toNat_iff.mp h.2.1, fun e hea heb => ?_⟩
  have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hea (toNat_ge_one a)
  obtain ⟨c, hc⟩ := toNat_surj e he1
  have hca : Dvd c a := dvd_toNat_iff.mpr (by rw [hc]; exact hea)
  have hcb : Dvd c b := dvd_toNat_iff.mpr (by rw [hc]; exact heb)
  have hcd : c.toNat ∣ d.toNat := dvd_toNat_iff.mp (h.2.2 c hca hcb)
  rw [hc] at hcd; exact hcd

end E213.Lens.Number.Nat213.Gcd
