import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.Tier2Hardness

/-!
# ArithFSM2 hardness: aperiodic bit streams are NOT ArithFSM-generable

Strict refinement of Tier 2 hardness:
  aperiodic bs ⇒ ¬ ∃ n hn m, ArithFSM2(n).bits = bs

Mechanism: ArithFSM2(n) bit-stream-equiv-to BitFSM(n²); if bs were
ArithFSM2-generable then it would be BitFSM-generable, contradicting
`aperiodic_bits_imp_no_BitFSM`.

This formally places Pell/algebraic streams strictly below
transcendental streams in the Tier hierarchy *via the ArithFSM lens*.
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Hardness

open E213.Math.Cohomology.Dyadic.ArithFSM.V2 (ArithFSM2)


/-- ★★★★★ Aperiodic ⇒ no ArithFSM2 generates it (any modulus). -/
theorem aperiodic_bits_imp_not_ArithFSM2 (bs : Nat → Bool)
    (h_aperiodic : ∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) :
    ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n),
      ¬ (∀ k, m.bits k = bs k) := by
  intro n hn m h_match
  apply aperiodic_bits_imp_not_BitFSM bs h_aperiodic (n * n) (m.toBitFSM hn)
  intro k
  rw [toBitFSM_bits_eq hn m k]
  exact h_match k

/-- ★★★★★★ ArithFSM2-generable ⇒ eventually periodic. -/
theorem ArithFSM2_generable_imp_eventually_periodic (bs : Nat → Bool) :
    (∃ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n), ∀ k, m.bits k = bs k)
    → ∃ N P, 0 < P ∧ ∀ k, k ≥ N → bs (k + P) = bs k := by
  rintro ⟨n, hn, m, hmatch⟩
  apply BitFSM_generable_imp_eventually_periodic bs
  refine ⟨n * n, m.toBitFSM hn, ?_⟩
  intro k
  rw [toBitFSM_bits_eq hn m k]
  exact hmatch k

end E213.Math.Cohomology.Dyadic.ArithFSM.Hardness
