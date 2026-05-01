import E213.Math.Cohomology.Dyadic.BitFSMConverse

/-!
# Signature is lossless: matching signatures ⇒ matching bit streams

Strong injectivity result: if two bit streams have identical
K_{3,2}^{(2)} signature trajectories at every step, the bit
streams themselves are identical.

Implication: signature *losslessly* encodes the bit stream.
All bit-stream complexity is preserved by the signature.
The Fin 5-valued trajectory is informationally equivalent to
the underlying Bool stream.

Proof: nextVertex is bit-injective (Lemma `nextVertex_bit_inj`).
If sig (k+1) = sig (k+1) for both streams, and sig k matches,
then the bits at step k must agree.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★ Signature is injective on Bool streams: matching
    signature trajectories at every step ⇒ matching bit streams. -/
theorem signature_injective (bs₁ bs₂ : Nat → Bool)
    (h : ∀ k, signature bs₁ k = signature bs₂ k) :
    ∀ k, bs₁ k = bs₂ k := by
  intro k
  apply nextVertex_bit_inj (signature bs₁ k)
  show nextVertex (signature bs₁ k) (bs₁ k)
       = nextVertex (signature bs₁ k) (bs₂ k)
  have hstep1 : nextVertex (signature bs₁ k) (bs₁ k)
                  = signature bs₁ (k + 1) := rfl
  have hstep2 : nextVertex (signature bs₂ k) (bs₂ k)
                  = signature bs₂ (k + 1) := rfl
  rw [hstep1, h (k + 1), ← hstep2, h k]

/-- ★★★★★★ Bidirectional characterisation: bit streams match iff
    signatures match.  Signature is a lossless invariant. -/
theorem signature_eq_iff_bits_eq (bs₁ bs₂ : Nat → Bool) :
    (∀ k, signature bs₁ k = signature bs₂ k) ↔ (∀ k, bs₁ k = bs₂ k) := by
  refine ⟨signature_injective bs₁ bs₂, ?_⟩
  intro h k
  induction k with
  | zero => rfl
  | succ k' ih =>
    show nextVertex (signature bs₁ k') (bs₁ k')
        = nextVertex (signature bs₂ k') (bs₂ k')
    rw [ih, h k']

/-- ★★★ Eventual lossless: signatures eventually match from N
    ⇒ bit streams eventually match from N (forward direction). -/
theorem signature_injective_eventual (bs₁ bs₂ : Nat → Bool) (N : Nat)
    (h : ∀ k, k ≥ N → signature bs₁ k = signature bs₂ k) :
    ∀ k, k ≥ N → bs₁ k = bs₂ k := by
  intro k hk
  apply nextVertex_bit_inj (signature bs₁ k)
  show nextVertex (signature bs₁ k) (bs₁ k)
       = nextVertex (signature bs₁ k) (bs₂ k)
  have hstep1 : nextVertex (signature bs₁ k) (bs₁ k)
                  = signature bs₁ (k + 1) := rfl
  have hstep2 : nextVertex (signature bs₂ k) (bs₂ k)
                  = signature bs₂ (k + 1) := rfl
  rw [hstep1, h (k + 1) (by omega), ← hstep2, h k hk]

end E213.Math.Cohomology.Dyadic.Conjecture
