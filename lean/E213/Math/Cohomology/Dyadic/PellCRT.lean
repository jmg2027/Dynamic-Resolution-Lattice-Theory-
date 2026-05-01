import E213.Math.Cohomology.Dyadic.LCMClosure
import E213.Math.Cohomology.Dyadic.PellFamily

/-!
# Pell family CRT-style period multiplicativity

Concrete CRT-style period combination instances:

  - lcm(3, 4) = 12  (mod 2 ↔ mod 3 combined)
  - lcm(4, 10) = 20 (mod 3 ↔ mod 5 combined)
  - lcm(4, 8) = 8   (mod 3 ↔ mod 7 combined; 8 = 4·2)
  - lcm(10, 8) = 40 (mod 5 ↔ mod 7 combined)

In each case, any stream defined as a function of a Pell-mod-m
bit and a Pell-mod-n bit (gcd(m,n) = 1) is periodic with the
LCM of component periods.  This is the structural content of
Pisano CRT specialised to our Fibonacci-squared matrix family.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★ Pell mod 3 ⊕ mod 5 combined stream: period | lcm(4,10) = 20. -/
theorem pell_mod3_xor_mod5_period_20 :
    ∀ k, xor (pellFSMmod3.bits (k + Nat.lcm 4 10))
            (pellFSMmod5.bits (k + Nat.lcm 4 10))
        = xor (pellFSMmod3.bits k) (pellFSMmod5.bits k) :=
  bs_combined_periodic_lcm pellFSMmod3.bits pellFSMmod5.bits 4 10
    (by omega) (by omega)
    pellFSMmod3_bits_period_4 pellFSMmod5_bits_period_10 xor

/-- ★★★★★ Pell mod 3 ⊕ mod 7 combined stream: period | lcm(4,8) = 8. -/
theorem pell_mod3_xor_mod7_period_8 :
    ∀ k, xor (pellFSMmod3.bits (k + Nat.lcm 4 8))
            (pellFSMmod7.bits (k + Nat.lcm 4 8))
        = xor (pellFSMmod3.bits k) (pellFSMmod7.bits k) :=
  bs_combined_periodic_lcm pellFSMmod3.bits pellFSMmod7.bits 4 8
    (by omega) (by omega)
    pellFSMmod3_bits_period_4 pellFSMmod7_bits_period_8 xor

/-- ★★★★★ Pell mod 5 ⊕ mod 7 combined stream: period | lcm(10,8) = 40. -/
theorem pell_mod5_xor_mod7_period_40 :
    ∀ k, xor (pellFSMmod5.bits (k + Nat.lcm 10 8))
            (pellFSMmod7.bits (k + Nat.lcm 10 8))
        = xor (pellFSMmod5.bits k) (pellFSMmod7.bits k) :=
  bs_combined_periodic_lcm pellFSMmod5.bits pellFSMmod7.bits 10 8
    (by omega) (by omega)
    pellFSMmod5_bits_period_10 pellFSMmod7_bits_period_8 xor

/-- Concrete LCM values for verification. -/
theorem pell_lcm_table :
    Nat.lcm 4 10 = 20 ∧ Nat.lcm 4 8 = 8 ∧ Nat.lcm 10 8 = 40 := by decide

/-- ★★★★★★ Pell CRT capstone: pairwise LCM closures for moduli 3, 5, 7. -/
theorem pell_crt_capstone :
    -- mod 3 × mod 5: period | 20
    (∀ k, xor (pellFSMmod3.bits (k + 20)) (pellFSMmod5.bits (k + 20))
        = xor (pellFSMmod3.bits k) (pellFSMmod5.bits k))
    -- mod 3 × mod 7: period | 8
    ∧ (∀ k, xor (pellFSMmod3.bits (k + 8)) (pellFSMmod7.bits (k + 8))
        = xor (pellFSMmod3.bits k) (pellFSMmod7.bits k))
    -- mod 5 × mod 7: period | 40
    ∧ (∀ k, xor (pellFSMmod5.bits (k + 40)) (pellFSMmod7.bits (k + 40))
        = xor (pellFSMmod5.bits k) (pellFSMmod7.bits k)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k; have := pell_mod3_xor_mod5_period_20 k
    rwa [pell_lcm_table.1] at this
  · intro k; have := pell_mod3_xor_mod7_period_8 k
    rwa [pell_lcm_table.2.1] at this
  · intro k; have := pell_mod5_xor_mod7_period_40 k
    rwa [pell_lcm_table.2.2] at this

end E213.Math.Cohomology.Dyadic.Conjecture
