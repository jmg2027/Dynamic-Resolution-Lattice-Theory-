import E213.Research.Real213.CutDistance

/-!
# Research.Real213CutSequence: Real213-valued sequences + Cauchy + limit

A sequence of cuts (or signed cuts) — Cauchy in cut-level form.

## Definition

CutSeq := Nat → RealCut.
CauchySeqCut: explicit modulus N(m, k) bounding eventual agreement.
limitOf cs h := the eventual cut value (well-defined by Cauchy).

## Significance

213-native form of Real-valued sequence convergence.  Bishop-style
Cauchy structure, axiom-free.
-/

namespace E213.Research.Real213.CutSequence

open E213.Firmware E213.Hypervisor

/-- Sequence of cuts. -/
abbrev CutSeq := Nat → (Nat → Nat → Bool)

/-- **CauchySeqCut**: Cauchy sequence with explicit modulus. -/
structure CauchySeqCut where
  cs : CutSeq
  N : Nat → Nat → Nat
  cauchy : ∀ m k, ∀ i j, i ≥ N m k → j ≥ N m k → cs i m k = cs j m k

/-- Limit cut — eventual value. -/
def CauchySeqCut.limit (cs : CauchySeqCut) : Nat → Nat → Bool :=
  fun m k => cs.cs (cs.N m k) m k

/-- Constant sequence is Cauchy. -/
def constCauchySeqCut (c : Nat → Nat → Bool) : CauchySeqCut where
  cs := fun _ => c
  N := fun _ _ => 0
  cauchy := fun _ _ _ _ _ _ => rfl

/-- Limit of constant sequence = itself. -/
theorem constCauchySeqCut_limit (c : Nat → Nat → Bool) :
    (constCauchySeqCut c).limit = c := rfl

end E213.Research.Real213.CutSequence
