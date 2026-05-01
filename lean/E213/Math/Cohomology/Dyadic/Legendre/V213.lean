import E213.Math.Cohomology.Dyadic.ArithFSM.V1

/-!
# Legendre symbol as ArithFSM₁ trajectory (213-native)

Definition via Euler's criterion: D^((p-1)/2) mod p.

The trajectory `1, D, D², D³, ..., D^((p-1)/2) mod p` is exactly an
ArithFSM₁(p) run.  At step (p-1)/2:
  - 0 if D ≡ 0 mod p
  - 1 if D is a quadratic residue mod p
  - p-1 if D is a non-residue (≡ -1 mod p)

The "Legendre lens" is therefore a 1-state arithmetic FSM whose
terminal state encodes the QR classification.

This is the bottom of the ArithFSM hierarchy:
  ArithFSM₁ ⊂ ArithFSM₂ (Pell) ⊂ ArithFSM₃ (Tribonacci) ⊂ ...
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- Legendre FSM: walk x ↦ D·x mod p, starting from 1. -/
def legendreFSM (D p : Nat) (hp : 0 < p) : ArithFSM1 p where
  init := ⟨1 % p, Nat.mod_lt _ hp⟩
  step x := ⟨(D * x.val) % p, Nat.mod_lt _ hp⟩
  out x := decide (x.val = 1)

/-- 213-native Legendre symbol: walk the FSM (p-1)/2 steps and read
    the trajectory's terminal state.  Returned as Fin 3:
      0 = ramified (D ≡ 0 mod p)
      1 = QR (split, terminal = 1)
      2 = NQR (inert, terminal = p-1) -/
def legendre213 (D p : Nat) (hp : 1 < p) : Fin 3 :=
  let v := ((legendreFSM D p (Nat.zero_lt_of_lt hp)).run ((p - 1) / 2)).val
  if v = 0 then ⟨0, by decide⟩
  else if v = 1 then ⟨1, by decide⟩
  else ⟨2, by decide⟩

end E213.Math.Cohomology.Dyadic.Conjecture
