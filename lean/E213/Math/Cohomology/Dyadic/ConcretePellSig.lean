import E213.Math.Cohomology.Dyadic.ArithFSMSignature

/-!
# Concrete signature periods for the Pell ArithFSM family

The eventual-period theorem only existential.  Concrete computation
shows the actual periods are tight:

  - pellFSMmod2: bit period 3 ⇒ signature pre-period 1, period 6
  - pellFSMmod3: bit period 4 ⇒ signature period 4 (pure)
  - pellFSMmod5: bit period 10 ⇒ signature period 10 (pure)

This file gives a *universal closure* lemma: bits periodic with
period P AND sig P = sig 0 ⇒ sig is purely periodic with period P.

Then applies it to the Pell mod-3 and Pell mod-5 instances.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- Universal closure: if bits are purely periodic with period P
    and the signature returns to ⟨0⟩ at step P, then the signature
    is purely periodic with the same period. -/
theorem signature_period_of_bits_period_and_anchor
    (bs : Nat → Bool) (P : Nat)
    (hbs : ∀ k, bs (k + P) = bs k)
    (hsig : signature bs P = signature bs 0) :
    ∀ k, signature bs (k + P) = signature bs k := by
  intro k
  induction k with
  | zero => show signature bs (0 + P) = signature bs 0
            rw [Nat.zero_add]; exact hsig
  | succ k' ih =>
    have hreorder : k' + 1 + P = (k' + P) + 1 := Nat.succ_add k' P
    rw [hreorder]
    show nextVertex (signature bs (k' + P)) (bs (k' + P))
        = nextVertex (signature bs k') (bs k')
    rw [ih, hbs]

/-- ★★★★ Pell mod-3 signature has period 4 (TIGHT, matches bit period). -/
theorem pellFSMmod3_signature_period_4 :
    ∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod3.bits 4
    pellFSMmod3_bits_period_4 (by decide)

/-- ★★★★★ Pell mod-5 signature has period 10 (TIGHT, matches bit period). -/
theorem pellFSMmod5_signature_period_10 :
    ∀ k, signature pellFSMmod5.bits (k + 10) = signature pellFSMmod5.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod5.bits 10
    pellFSMmod5_bits_period_10 (by decide)

/-- Universal closure with pre-period: bits periodic from N₀ with
    period P, plus signature anchor at (N₀, N₀+P) ⇒ signature
    eventually periodic from N₀ with period P. -/
theorem signature_period_of_bits_period_and_anchor_from
    (bs : Nat → Bool) (P N₀ : Nat)
    (hbs : ∀ k, bs (k + P) = bs k)
    (hsig : signature bs (N₀ + P) = signature bs N₀) :
    ∀ k, k ≥ N₀ → signature bs (k + P) = signature bs k := by
  have key : ∀ d, signature bs (N₀ + d + P) = signature bs (N₀ + d) := by
    intro d
    induction d with
    | zero => show signature bs (N₀ + 0 + P) = signature bs (N₀ + 0)
              rw [Nat.add_zero]; exact hsig
    | succ d' ih =>
      have hreorder : N₀ + (d' + 1) + P = (N₀ + d' + P) + 1 :=
        Nat.succ_add (N₀ + d') P
      have hsucc : N₀ + (d' + 1) = (N₀ + d') + 1 := rfl
      rw [hreorder, hsucc]
      show nextVertex (signature bs (N₀ + d' + P)) (bs (N₀ + d' + P))
          = nextVertex (signature bs (N₀ + d')) (bs (N₀ + d'))
      rw [ih, hbs]
  intro k hk
  have hk_eq : k = N₀ + (k - N₀) := (Nat.add_sub_cancel' hk).symm
  rw [hk_eq]; exact key (k - N₀)

/-- ★★★★ Pell mod-2 signature has period 6 from step 1 (TIGHT;
    pre-period 1, then 2×3-fold cycle). -/
theorem pellFSMmod2_signature_period_6_from_1 :
    ∀ k, k ≥ 1 →
      signature pellFSMmod2.bits (k + 6) = signature pellFSMmod2.bits k := by
  apply signature_period_of_bits_period_and_anchor_from
    pellFSMmod2.bits 6 1
  · intro k
    have hp3 := pellFSMmod2_bits_period_3 (k + 3)
    have hp3' := pellFSMmod2_bits_period_3 k
    have heq : k + 6 = (k + 3) + 3 := (Nat.add_assoc k 3 3).symm
    rw [heq, hp3, hp3']
  · decide

end E213.Math.Cohomology.Dyadic.Conjecture
