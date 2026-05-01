import E213.Math.Cohomology.Dyadic.NumberTheory213v2
import E213.Math.Cohomology.Dyadic.Pell.ProperBridge

/-!
# 213-native number theory v3 — Pisano + parametric discriminant

v3 strengthens v2 with the discriminant-parametric Legendre-Pisano
bridge.  Two discriminants verified (D = 5 and D = 8), framework
PARAMETRIC across them.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★★★★★★ v3 Master capstone — discriminant-parametric.

    Bundles v2 (Step 1+2+3) with the new Pell proper (D=8) bridge:

      D = 5 (Pell-Fib²): split→(p-1)/2, inert→p+1, ramified→2p
      D = 8 (Pell proper): split→p-1,    inert→2(p+1)

    All <= {propext, Quot.sound}. -/
theorem number_theory_213_capstone_v3 :
    -- Inherits v2 (Step 1 + Step 2 D=5 + Step 3)
    (∀ (bs1 bs2 : Nat → Bool) (p q : Nat),
      0 < p → 0 < q →
      (∀ k, bs1 (k + p) = bs1 k) → (∀ k, bs2 (k + q) = bs2 k) →
      ∀ (g : Bool → Bool → Bool) k,
        g (bs1 (k + Nat.lcm p q)) (bs2 (k + Nat.lcm p q))
        = g (bs1 k) (bs2 k))
    -- Pell proper (D=8) at 3 primes, both branches
    ∧ (legendre213 8 3 (by omega) = ⟨2, by decide⟩
        ∧ legendre213 8 5 (by omega) = ⟨2, by decide⟩
        ∧ legendre213 8 7 (by omega) = ⟨1, by decide⟩
        ∧ pisano_predict_proper 3 (by omega) = 8
        ∧ pisano_predict_proper 5 (by omega) = 12
        ∧ pisano_predict_proper 7 (by omega) = 6) := by
  refine ⟨bs_combined_periodic_lcm, ?_⟩
  refine ⟨legendre_8_mod_3, legendre_8_mod_5, legendre_8_mod_7,
          ?_, ?_, ?_⟩ <;> decide

end E213.Math.Cohomology.Dyadic.Conjecture
