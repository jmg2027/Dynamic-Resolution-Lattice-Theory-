/-!
# Bool XOR fold infrastructure

Generic XOR-fold over `Nat → Bool` and the AC pair-swap identity.
Used to prove F₂-linearity of "ψ-style" sum functionals across
cohomology files without needing `funext` (and thus without
`Quot.sound`).

  · `xor_pair_swap` — AC: `(a⊕b)⊕(c⊕d) = (a⊕c)⊕(b⊕d)`
  · `psiNatPos n v` — left-assoc XOR `v 0 ⊕ v 1 ⊕ … ⊕ v n`
  · `psiNatPos_linear` — distribution over pointwise XOR
  · `psiNatPos_congr_all` — pointwise-agreement congruence
    (avoids `funext`)

The `psiNatPos` shape is base-`v 0` (not `false`) so that lifts of
`Fin (n+1) → Bool` cochains match definitionally via explicit
pattern-match lifts (`vToNat`-style).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Infrastructure.BoolXORFold

/-- Bool-XOR AC pair swap: `(a⊕b) ⊕ (c⊕d) = (a⊕c) ⊕ (b⊕d)`. -/
theorem xor_pair_swap (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Recursive XOR over a `Nat → Bool` taking values at indices `0..n`.
    Base case `v 0` (not `false`) keeps definitional match with the
    `Fin (n+1)`-cochain lifts. -/
def psiNatPos : (n : Nat) → (Nat → Bool) → Bool
  | 0, v => v 0
  | k+1, v => xor (psiNatPos k v) (v (k+1))

/-- `psiNatPos` distributes over pointwise XOR of two `Nat → Bool`
    functions.  Inductive proof via `xor_pair_swap` at the succ step. -/
theorem psiNatPos_linear (n : Nat) (v w : Nat → Bool) :
    psiNatPos n (fun i => xor (v i) (w i))
      = xor (psiNatPos n v) (psiNatPos n w) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show xor (psiNatPos k _) (xor (v (k+1)) (w (k+1)))
        = xor (xor (psiNatPos k v) (v (k+1)))
              (xor (psiNatPos k w) (w (k+1)))
    rw [ih]
    exact xor_pair_swap _ _ _ _

/-- `psiNatPos` respects pointwise-everywhere agreement.  Replaces
    function-level equality (which needs `funext` ⇒ `Quot.sound`). -/
theorem psiNatPos_congr_all (n : Nat) (v w : Nat → Bool)
    (h : ∀ i, v i = w i) : psiNatPos n v = psiNatPos n w := by
  induction n with
  | zero => exact h 0
  | succ k ih =>
    show xor (psiNatPos k v) (v (k+1)) = xor (psiNatPos k w) (w (k+1))
    rw [ih, h (k+1)]

end E213.Lib.Math.Cohomology.Infrastructure.BoolXORFold
