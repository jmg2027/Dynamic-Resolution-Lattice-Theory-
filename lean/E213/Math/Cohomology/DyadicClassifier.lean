import E213.Math.Cohomology.DyadicSignature

/-!
# Dyadic classifier — signature periodic ⇒ bit stream periodic

Key structural theorem (G1 Conjecture 2 sharpened):

  signature periodic from step N with period p
  ⇒ bit stream periodic from step N with period p

Proof: nextVertex is *bit-injective* at every vertex —
the two outgoing transitions land on different next-vertices.
So if signatures match before and after period p, the bits must
have matched.

Contrapositive: aperiodic bit stream (i.e., irrational binary
expansion) ⇒ aperiodic signature.  This is the formal core of
"signature classifies rationality".
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- nextVertex distinguishes the bit at every vertex. -/
theorem nextVertex_bit_inj (v : Fin 5) (b₁ b₂ : Bool) :
    nextVertex v b₁ = nextVertex v b₂ → b₁ = b₂ := by
  obtain ⟨n, hn⟩ := v
  match n, hn with
  | 0, _ => intro h; cases b₁ <;> cases b₂ <;> simp_all [nextVertex]
  | 1, _ => intro h; cases b₁ <;> cases b₂ <;> simp_all [nextVertex]
  | 2, _ => intro h; cases b₁ <;> cases b₂ <;> simp_all [nextVertex]
  | 3, _ => intro h; cases b₁ <;> cases b₂ <;> simp_all [nextVertex]
  | 4, _ => intro h; cases b₁ <;> cases b₂ <;> simp_all [nextVertex]

/-- ★★★ Key theorem: signature periodicity ⇒ bit periodicity. -/
theorem signature_periodic_implies_bits_periodic
    (bs : Nat → Bool) (p N : Nat) (hp : 0 < p)
    (h_sig : ∀ n, n ≥ N → signature bs (n + p) = signature bs n) :
    ∀ n, n ≥ N → bs (n + p) = bs n := by
  intro n hn
  have hn1 : n + 1 ≥ N := Nat.le_succ_of_le hn
  have h1 : signature bs (n + 1) = nextVertex (signature bs n) (bs n) := rfl
  have h2 : signature bs (n + p + 1)
              = nextVertex (signature bs (n + p)) (bs (n + p)) := rfl
  have hsig_n : signature bs (n + p) = signature bs n := h_sig n hn
  have hsig_n1 : signature bs (n + 1 + p) = signature bs (n + 1) :=
    h_sig (n + 1) hn1
  have heq_idx : n + 1 + p = n + p + 1 := Nat.succ_add n p
  have hkey : nextVertex (signature bs n) (bs n)
                = nextVertex (signature bs n) (bs (n + p)) := by
    rw [← h1, ← hsig_n1, heq_idx, h2, hsig_n]
  exact (nextVertex_bit_inj _ _ _ hkey).symm

/-- ★★★★★ Contrapositive — aperiodic bits ⇒ aperiodic signature. -/
theorem aperiodic_bits_imp_aperiodic_signature
    (bs : Nat → Bool)
    (h_aperiodic : ∀ p N : Nat, 0 < p →
                    ∃ n, n ≥ N ∧ bs (n + p) ≠ bs n) :
    ∀ p N : Nat, 0 < p →
      ¬ (∀ n, n ≥ N → signature bs (n + p) = signature bs n) := by
  intro p N hp h_sig_per
  obtain ⟨n, hn, hne⟩ := h_aperiodic p N hp
  exact hne (signature_periodic_implies_bits_periodic bs p N hp
              h_sig_per n hn)

end E213.Math.Cohomology.DyadicConjecture
