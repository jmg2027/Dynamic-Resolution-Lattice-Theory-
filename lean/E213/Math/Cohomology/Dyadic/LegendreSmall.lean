import E213.Math.Cohomology.Dyadic.Legendre213

/-!
# Concrete Legendre values for the Pell discriminant D = 5

Pell matrix M = [[2,1],[1,1]] has characteristic polynomial
λ² - 3λ + 1, discriminant Δ = 9 - 4 = 5.

The Legendre symbol (5/p) governs whether M's eigenvalues split
in 𝔽_p (split: π_F(p) | p - 1) or remain inert (inert: π_F(p) | 2(p+1)),
which controls the Pell period.

Manual trajectory verification (Euler's criterion D^((p-1)/2) mod p):

  p=3: walk 1 → 2.  Step 1.  Terminal 2 = -1 mod 3.  NQR (inert).
  p=5: walk 1 → 0 → 0.  Step 2.  Terminal 0.  Ramified.
  p=7: walk 1 → 5 → 4 → 6.  Step 3.  Terminal 6 = -1 mod 7.  NQR.
  p=11: walk 1 → 5 → 3 → 4 → 9 → 1.  Step 5.  Terminal 1.  QR (split).
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★ Pell discriminant 5 is NQR mod 3 (inert). -/
theorem legendre_5_mod_3 : legendre213 5 3 (by omega) = ⟨2, by decide⟩ := by
  decide

/-- ★★★★★ Pell discriminant 5 is ramified mod 5 (Δ = 0). -/
theorem legendre_5_mod_5 : legendre213 5 5 (by omega) = ⟨0, by decide⟩ := by
  decide

/-- ★★★★★ Pell discriminant 5 is NQR mod 7 (inert). -/
theorem legendre_5_mod_7 : legendre213 5 7 (by omega) = ⟨2, by decide⟩ := by
  decide

/-- ★★★★★ Pell discriminant 5 is QR mod 11 (split). -/
theorem legendre_5_mod_11 : legendre213 5 11 (by omega) = ⟨1, by decide⟩ := by
  decide

/-- ★★★★★★ The Legendre lens reveals the Pell discriminant pattern:
    primes 3, 7 are inert (NQR), prime 11 is split (QR), prime 5
    is ramified.  All four cases decided by trajectory walking. -/
theorem pell_discriminant_legendre_table :
    legendre213 5 3 (by omega) = ⟨2, by decide⟩
    ∧ legendre213 5 5 (by omega) = ⟨0, by decide⟩
    ∧ legendre213 5 7 (by omega) = ⟨2, by decide⟩
    ∧ legendre213 5 11 (by omega) = ⟨1, by decide⟩ :=
  ⟨legendre_5_mod_3, legendre_5_mod_5, legendre_5_mod_7, legendre_5_mod_11⟩

end E213.Math.Cohomology.Dyadic.Conjecture
