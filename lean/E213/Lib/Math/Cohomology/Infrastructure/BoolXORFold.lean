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

/-! ## `Fin 9 → Bool` lift bridge

Pattern-match lift from `Fin 9 → Bool` to `Nat → Bool`.  Used to
feed `Fin 9`-cochains into the `psiNatPos 8` fold without invoking
`dite` (which would route through `propext`).  Out-of-range Nat
indices default to `false`.

This is the canonical `vToNat`-style bridge: both
`V33Indeterminacy` (NS = NT = 3, c = 1) and `V33c3Indeterminacy`
(c = 3) opened identical inline copies via local `def vToNat`
before extraction; they now `open`-renaming `fin9LiftToNat` back
to `vToNat` to preserve call sites. -/

/-- Lift `Fin 9 → Bool` to `Nat → Bool` by direct pattern match.
    Out-of-range Nat indices return `false`. -/
def fin9LiftToNat (v : Fin 9 → Bool) : Nat → Bool
  | 0 => v ⟨0, by decide⟩
  | 1 => v ⟨1, by decide⟩
  | 2 => v ⟨2, by decide⟩
  | 3 => v ⟨3, by decide⟩
  | 4 => v ⟨4, by decide⟩
  | 5 => v ⟨5, by decide⟩
  | 6 => v ⟨6, by decide⟩
  | 7 => v ⟨7, by decide⟩
  | 8 => v ⟨8, by decide⟩
  | _ => false

/-- `fin9LiftToNat` distributes over pointwise XOR at every Nat index.
    Proved by exhaustive case match (9 in-range + 1 out-of-range). -/
theorem fin9LiftToNat_xor (v w : Fin 9 → Bool) (i : Nat) :
    fin9LiftToNat (fun f => xor (v f) (w f)) i
      = xor (fin9LiftToNat v i) (fin9LiftToNat w i) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | _+9 => rfl

end E213.Lib.Math.Cohomology.Infrastructure.BoolXORFold
