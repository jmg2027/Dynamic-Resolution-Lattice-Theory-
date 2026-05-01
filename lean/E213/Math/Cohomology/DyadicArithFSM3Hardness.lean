import E213.Math.Cohomology.DyadicArithFSM3Bound
import E213.Math.Cohomology.DyadicTier2Hardness

/-!
# ArithFSM3 hardness — aperiodic bit streams are not ArithFSM3-generable

Cubic-class analogue of `aperiodic_bits_imp_not_ArithFSM2`.
Mechanism: ArithFSM3(n) bit-stream ⊂ BitFSM(n³); if bs were
ArithFSM3-generable then it would be BitFSM-generable, contradicting
`aperiodic_bits_imp_no_BitFSM`.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★ Aperiodic ⇒ no ArithFSM3 generates it (any modulus). -/
theorem aperiodic_bits_imp_not_ArithFSM3 (bs : Nat → Bool)
    (h_aperiodic : ∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) :
    ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM3 n),
      ¬ (∀ k, m.bits k = bs k) := by
  intro n hn m h_match
  apply aperiodic_bits_imp_not_BitFSM bs h_aperiodic (n * n * n)
    (m.toBitFSM hn)
  intro k
  rw [toBitFSM3_bits_eq hn m k]
  exact h_match k

/-- ★★★★★★ ArithFSM3-generable ⇒ eventually periodic. -/
theorem ArithFSM3_generable_imp_eventually_periodic (bs : Nat → Bool) :
    (∃ (n : Nat) (hn : 0 < n) (m : ArithFSM3 n), ∀ k, m.bits k = bs k)
    → ∃ N P, 0 < P ∧ ∀ k, k ≥ N → bs (k + P) = bs k := by
  rintro ⟨n, hn, m, hmatch⟩
  apply BitFSM_generable_imp_eventually_periodic bs
  refine ⟨n * n * n, m.toBitFSM hn, ?_⟩
  intro k
  rw [toBitFSM3_bits_eq hn m k]
  exact hmatch k

end E213.Math.Cohomology.DyadicConjecture
