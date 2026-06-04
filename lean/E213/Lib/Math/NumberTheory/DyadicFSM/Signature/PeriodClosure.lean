import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature
import E213.Meta.Tactic.NatHelper

/-!
# Signature period closure (universal — no Pell dependency)

Two universal closure lemmas for signatures of bit-streams:

  - `signature_period_of_bits_period_and_anchor` — pure-period
    closure: bits periodic with period P + signature anchored at P
    ⇒ signature also periodic with period P.

  - `signature_period_of_bits_period_and_anchor_from` — eventual-
    period closure with pre-period N₀.

Both depend only on `nextVertex` / `signature` from
`DyadicFSM.Signature.Signature`.  Split from
`ConcretePellSig.lean` to break the ArithFSM ↔ ConcretePellSig
build cycle (ConcretePellSig used to provide these utilities AND
consume `ArithFSM.Mod*` which itself needed the utilities).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig

open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (nextVertex signature)

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
  have hk_eq : k = N₀ + (k - N₀) := (E213.Tactic.NatHelper.add_sub_of_le hk).symm
  rw [hk_eq]; exact key (k - N₀)

end E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
