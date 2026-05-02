import E213.Math.Cohomology.Dyadic.SignatureInj
import E213.Math.Cohomology.Dyadic.BitFSM.Examples
import E213.Math.Cohomology.Dyadic.Tier2Hardness

/-!
# Dyadic / K_{3,2}^{(2)} signature capstone

Single ★★★★★★ bundle collecting all results from G1
Conjecture 2 work.

Theorem chain (all ≤ {propext, Quot.sound}):

  Tier 0 (rationals) characterised:
    bs purely periodic ⇔ ∃ BitFSM(p) generating bs
                       ⇔ signature ev-periodic
  Lossless invariant:
    sig injective; bit streams match ⇔ signatures match
  Tier 1 ∪ Tier 2 vs Tier 0:
    aperiodic bits ⇒ aperiodic signature
  Quantitative:
    BitFSM(n) ⇒ signature period ≤ 5n
-/

namespace E213.Math.Cohomology.Dyadic.Archive.Capstone

open E213.Math.Cohomology.Dyadic.Classifier (signature_periodic_implies_bits_periodic)
open E213.Math.Cohomology.Dyadic.ForwardEventual (signature_eventually_periodic_of_eventually_periodic_bits)
open E213.Math.Cohomology.Dyadic.Signature (signature)
open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)


/-- ★★★★★★★ Dyadic / K_{3,2}^{(2)} signature capstone. -/
theorem dyadic_signature_capstone :
    -- (1) Lossless: signatures match ⇔ bit streams match
    (∀ bs₁ bs₂ : Nat → Bool,
      (∀ k, signature bs₁ k = signature bs₂ k) ↔ (∀ k, bs₁ k = bs₂ k))
    -- (2) Backward: signature ev-periodic ⇒ bit stream ev-periodic
    ∧ (∀ (bs : Nat → Bool) (p N : Nat) (hp : 0 < p),
        (∀ n, n ≥ N → signature bs (n + p) = signature bs n)
          → ∀ n, n ≥ N → bs (n + p) = bs n)
    -- (3) Forward: bs ev-periodic ⇒ signature ev-periodic
    ∧ (∀ (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p),
        (∀ n, n ≥ N₀ → bs (n + p) = bs n)
          → ∃ N P, 0 < P
              ∧ ∀ n, n ≥ N → signature bs (n + P) = signature bs n)
    -- (4) Tier 0 ⇔ BitFSM
    ∧ (∀ (bs : Nat → Bool) (p : Nat) (hp : 0 < p),
        (∀ n, bs (n + p) = bs n) → ∃ (m : BitFSM p), ∀ k, m.bits k = bs k)
    -- (5) BitFSM(n) ⇒ pre-period + period ≤ 5n
    ∧ (∀ (n : Nat) (m : BitFSM n) (hn : 0 < n),
        ∃ N P, 0 < P ∧ N + P ≤ 5 * n
          ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k
              ∧ m.run (k + P) = m.run k)
    -- (6) Tier 2 hardness: aperiodic ⇒ no BitFSM (any size)
    ∧ (∀ (bs : Nat → Bool),
        (∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k)
          → ¬ ∃ (n : Nat) (m : BitFSM n), ∀ k, m.bits k = bs k)
    -- (7-9) Concrete Tier 0 BitFSM witnesses
    ∧ (∃ m : BitFSM 2, m.bits 0 = false ∧ m.bits 1 = true)
    ∧ (∃ m : BitFSM 4, m.bits 2 = true ∧ m.bits 3 = true)
    ∧ (∃ m : BitFSM 3, m.bits 0 = false ∧ m.bits 2 = true) :=
  ⟨signature_eq_iff_bits_eq,
   signature_periodic_implies_bits_periodic,
   signature_eventually_periodic_of_eventually_periodic_bits,
   tier0_equiv_bitfsm,
   fun _ m hn => fsm_signature_period_bound m hn,
   aperiodic_bits_imp_no_BitFSM,
   ⟨fsm_one_third, by decide, by decide⟩,
   ⟨fsm_one_fifth, by decide, by decide⟩,
   ⟨fsm_one_seventh, by decide, by decide⟩⟩

end E213.Math.Cohomology.Dyadic.Archive.Capstone
