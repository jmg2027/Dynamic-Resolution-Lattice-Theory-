import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Nat.PolyNatMTactic

/-!
# EisensteinCubeRoot — the cube-root reduction (Phase 3 of the split-converse marathon)

Phase 3 needs `p ≡ 1 mod 3 ⟹ ∃ x, p ∣ x²+x+1`.  The classical argument: with FLT, every
nonzero `a` has `(aᵐ)³ = a^(p−1) ≡ 1` (`m = (p−1)/3`), so `aᵐ` is a cube root of unity; if some
`aᵐ ≢ 1` it is *primitive*, and writing `z = aᵐ − 1` (`p ∤ z`), `p ∣ (z+1)³ − 1 =
z·(z²+3z+3)`, whence `p ∣ z²+3z+3 = (z+1)²+(z+1)+1` (Euclid's lemma) — so `x = z+1` works.

This file closes the **reduction** (the Euclid step), isolating the one remaining gate — the
*existence* of a primitive cube root, equivalently `∃ a, aᵐ ≢ 1`, which reduces to Lagrange's
root bound (a degree-`m` polynomial over `ℤ/p` has `≤ m < p−1` roots) — a polynomial-root
library mod `p` not yet in the repo.

  * ★★★ `cube_root_of_order3` — `p ∣ z·(z²+3z+3)`, `p ∤ z` (`p` prime) ⟹ `∃ x, p ∣ x²+x+1`
    (namely `x = z+1`), via `prime_coprime` + `euclid_of_coprime`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.EisensteinCubeRoot

open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (euclid_of_coprime prime_coprime)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213)

/-- ★★★ **The cube-root reduction.**  For a prime `p`, if `p ∣ z·(z²+3z+3)` (`= (z+1)³−1`) and
    `p ∤ z`, then `x = z+1` satisfies `p ∣ x²+x+1`.  The primitive cube root `z+1 = aᵐ` (with
    `z = aᵐ−1`, `p ∤ z` ⟺ `aᵐ ≢ 1`) yields the representation root; Euclid's lemma extracts the
    cyclotomic factor `z²+3z+3 = (z+1)²+(z+1)+1` from `z·(z²+3z+3)`. -/
theorem cube_root_of_order3 (p z : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hdvd : p ∣ z * (z * z + 3 * z + 3)) (hz : ¬ p ∣ z) :
    ∃ x : Nat, p ∣ (x * x + x + 1) := by
  have hco : gcd213 z p = 1 := by rw [gcd213_comm]; exact prime_coprime p z hpr hz
  have hT : p ∣ (z * z + 3 * z + 3) := euclid_of_coprime z (z * z + 3 * z + 3) p hp hco hdvd
  refine ⟨z + 1, ?_⟩
  have heq : (z + 1) * (z + 1) + (z + 1) + 1 = z * z + 3 * z + 3 := by ring_nat
  rw [heq]; exact hT

end E213.Lib.Math.NumberTheory.ModArith.EisensteinCubeRoot
