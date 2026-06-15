import E213.Meta.Nat.Gcd213
import E213.Lib.Math.NumberTheory.Lcm213

/-!
# The divisibility lattice `(ℕ, gcd, lcm)` (∅-axiom)

Meet = `gcd213`, join = `lcm213`.  The order-theoretic **lattice axioms** for the
naturals under divisibility, proven via divisibility-antisymmetry
(`dvd_antisymm_213`, the PURE twin — `Nat.dvd_antisymm` leaks `propext`):

  * **Absorption** `gcd(a, lcm(a,b)) = a` (`gcd_lcm_absorb`) and
    `lcm(a, gcd(a,b)) = a` (`lcm_gcd_absorb`).
  * **Idempotence** `gcd(a,a) = a` (`gcd213_self`) and `lcm(a,a) = a` (`lcm_self`).

All proven *unconditionally* (no `0 < a`): the `a = 0` branch is handled directly
(`lcm213 0 x = 0`), the positivity-requiring lcm lemmas apply only in the
`a = succ a'` branch.  Commutativity is `gcd213_comm` / the lcm symmetry already
in the corpus; the **distributive** law `gcd(a, lcm(b,c)) = lcm(gcd(a,b),gcd(a,c))`
(upgrading to a *distributive* lattice) is left open — it needs the
prime-valuation `min/max` distributivity, a larger detour.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.GcdLcmLattice

open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm
   gcd213_self dvd_antisymm_213 gcd213_zero_left)
open E213.Lib.Math.NumberTheory.Lcm213
  (lcm213 dvd_lcm_left dvd_lcm_right lcm_dvd lcm_pos gcd_pos)
open E213.Tactic.NatHelper (gcd213)

/-- `a ∣ a`. -/
theorem dvd_refl' (a : Nat) : a ∣ a := ⟨1, (Nat.mul_one a).symm⟩

/-- `lcm213 0 x = 0`. -/
theorem lcm_zero_left (x : Nat) : lcm213 0 x = 0 := by
  show 0 * x / gcd213 0 x = 0
  rw [Nat.zero_mul, Nat.zero_div]

/-- **Absorption 1**: `gcd(a, lcm(a,b)) = a`. -/
theorem gcd_lcm_absorb (a b : Nat) : gcd213 a (lcm213 a b) = a := by
  cases a with
  | zero =>
    show gcd213 0 (lcm213 0 b) = 0
    rw [lcm_zero_left b, gcd213_zero_left]
  | succ a' =>
    apply dvd_antisymm_213
    · exact gcd213_dvd_left (a'+1) (lcm213 (a'+1) b)
    · exact gcd213_greatest (a'+1) (lcm213 (a'+1) b) (a'+1)
        (dvd_refl' (a'+1))
        (dvd_lcm_left (a'+1) b (Nat.succ_pos a'))

/-- **Absorption 2**: `lcm(a, gcd(a,b)) = a`. -/
theorem lcm_gcd_absorb (a b : Nat) : lcm213 a (gcd213 a b) = a := by
  cases a with
  | zero =>
    show lcm213 0 (gcd213 0 b) = 0
    exact lcm_zero_left (gcd213 0 b)
  | succ a' =>
    have hapos : 0 < a' + 1 := Nat.succ_pos a'
    have hgpos : 0 < gcd213 (a'+1) b := gcd_pos (a'+1) b hapos
    apply dvd_antisymm_213
    · exact lcm_dvd (a'+1) (gcd213 (a'+1) b) (a'+1) hapos hgpos
        (dvd_refl' (a'+1))
        (gcd213_dvd_left (a'+1) b)
    · exact dvd_lcm_left (a'+1) (gcd213 (a'+1) b) hapos

/-- **lcm idempotence**: `lcm(a,a) = a`.  (gcd idempotence is `gcd213_self`.) -/
theorem lcm_self (a : Nat) : lcm213 a a = a := by
  cases a with
  | zero =>
    show lcm213 0 0 = 0
    exact lcm_zero_left 0
  | succ a' =>
    have hapos : 0 < a' + 1 := Nat.succ_pos a'
    apply dvd_antisymm_213
    · exact lcm_dvd (a'+1) (a'+1) (a'+1) hapos hapos
        (dvd_refl' (a'+1)) (dvd_refl' (a'+1))
    · exact dvd_lcm_left (a'+1) (a'+1) hapos

/-- gcd idempotence (re-export of `gcd213_self` for the lattice-law set). -/
theorem gcd_self_law (a : Nat) : gcd213 a a = a := gcd213_self a

end E213.Lib.Math.NumberTheory.GcdLcmLattice
